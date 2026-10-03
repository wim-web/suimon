//go:build !js

package main

import (
	"context"
	"encoding/hex"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
)

type unreadBody struct{ t *testing.T }

func (b unreadBody) Read([]byte) (int, error) {
	b.t.Error("rejected request body was read")
	return 0, io.EOF
}
func (unreadBody) Close() error { return nil }

func TestLocalHandlerRejectsUntrustedRequests(t *testing.T) {
	s := newServer(context.Background(), nil)
	// A nil execution makes any accidental call to the cancel handler fail immediately.
	s.runs["r1"] = &run{}
	h, err := s.localHandler(nil, &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 8080})
	if err != nil {
		t.Fatal(err)
	}
	res := httptest.NewRecorder()
	h.ServeHTTP(res, httptest.NewRequest("GET", "http://127.0.0.1:8080/api/csrf", nil))
	token := decode[map[string]string](t, res.Body.Bytes())["token"]
	for _, test := range []struct {
		name   string
		change func(*http.Request)
		status int
	}{
		{"foreign host", func(r *http.Request) { r.Host = "attacker.test:8080" }, 403},
		{"localhost suffix", func(r *http.Request) { r.Host = "localhost.attacker.test:8080" }, 403},
		{"wrong port", func(r *http.Request) { r.Host = "127.0.0.1:8081" }, 403},
		{"no port", func(r *http.Request) { r.Host = "127.0.0.1" }, 403},
		{"public IP", func(r *http.Request) { r.Host = "192.0.2.1:8080" }, 403},
		{"foreign origin", func(r *http.Request) { r.Header.Set("Origin", "https://attacker.test") }, 403},
		{"other local origin", func(r *http.Request) { r.Header.Set("Origin", "http://127.0.0.1:8081") }, 403},
		{"other local hostname", func(r *http.Request) { r.Header.Set("Origin", "http://localhost:8080") }, 403},
		{"null origin", func(r *http.Request) { r.Header.Set("Origin", "null") }, 403},
		{"empty origin", func(r *http.Request) { r.Header.Set("Origin", "") }, 403},
		{"origin with path", func(r *http.Request) { r.Header.Set("Origin", "http://127.0.0.1:8080/") }, 403},
		{"duplicate origin", func(r *http.Request) { r.Header.Add("Origin", "https://attacker.test") }, 403},
		{"cross-site", func(r *http.Request) { r.Header.Set("Sec-Fetch-Site", "cross-site") }, 403},
		{"same-site", func(r *http.Request) { r.Header.Set("Sec-Fetch-Site", "same-site") }, 403},
		{"none on write", func(r *http.Request) { r.Header.Set("Sec-Fetch-Site", "none") }, 403},
		{"unknown fetch site", func(r *http.Request) { r.Header.Set("Sec-Fetch-Site", "unknown") }, 403},
		{"duplicate fetch site", func(r *http.Request) { r.Header.Add("Sec-Fetch-Site", "cross-site") }, 403},
		{"missing content type", func(r *http.Request) { r.Header.Del("Content-Type") }, 415},
		{"text/plain", func(r *http.Request) { r.Header.Set("Content-Type", "text/plain") }, 415},
		{"form", func(r *http.Request) { r.Header.Set("Content-Type", "application/x-www-form-urlencoded") }, 415},
		{"multipart", func(r *http.Request) { r.Header.Set("Content-Type", "multipart/form-data; boundary=x") }, 415},
		{"invalid media type", func(r *http.Request) { r.Header.Set("Content-Type", "application/json; charset") }, 415},
		{"duplicate content type", func(r *http.Request) { r.Header.Add("Content-Type", "text/plain") }, 415},
		{"missing token", func(r *http.Request) { r.Header.Del(csrfHeader) }, 403},
		{"wrong token", func(r *http.Request) { r.Header.Set(csrfHeader, strings.Repeat("0", len(token))) }, 403},
		{"duplicate token", func(r *http.Request) { r.Header.Add(csrfHeader, token) }, 403},
		{"forwarded headers", func(r *http.Request) {
			r.Host = "attacker.test:8080"
			r.Header.Set("X-Forwarded-Host", "127.0.0.1:8080")
			r.Header.Set("X-Forwarded-Proto", "http")
		}, 403},
	} {
		t.Run(test.name, func(t *testing.T) {
			for _, path := range []string{"/api/runs", "/api/runs/r1/cancel"} {
				req := httptest.NewRequest("POST", "http://127.0.0.1:8080"+path, unreadBody{t})
				req.Header.Set("Origin", "http://127.0.0.1:8080")
				req.Header.Set("Sec-Fetch-Site", "same-origin")
				req.Header.Set("Content-Type", "application/json")
				req.Header.Set(csrfHeader, token)
				test.change(req)
				res := httptest.NewRecorder()
				h.ServeHTTP(res, req)
				if res.Code != test.status {
					t.Errorf("%s: %d %s, want %d", path, res.Code, res.Body.String(), test.status)
				}
			}
		})
	}
}

func TestLocalHandlerToken(t *testing.T) {
	srv := newTestServer(t)
	res, err := http.Get(srv.URL + "/api/csrf")
	if err != nil {
		t.Fatal(err)
	}
	defer res.Body.Close()
	data, err := io.ReadAll(res.Body)
	if err != nil {
		t.Fatal(err)
	}
	token := decode[map[string]string](t, data)["token"]
	if decoded, err := hex.DecodeString(token); err != nil || len(decoded) != 32 {
		t.Fatalf("expected a 256-bit token: %q", token)
	}
	if res.StatusCode != 200 || res.Header.Get("Cache-Control") != "no-store" ||
		res.Header.Get("Content-Type") != "application/json" || res.Header.Get("X-Content-Type-Options") != "nosniff" ||
		res.Header.Get("Access-Control-Allow-Origin") != "" {
		t.Fatalf("unexpected token response: %d %v", res.StatusCode, res.Header)
	}
	_, again := call(t, "GET", srv.URL+"/api/csrf", "")
	if decode[map[string]string](t, again)["token"] != token {
		t.Fatal("token changed within a server instance")
	}
	other := newTestServer(t)
	_, data = call(t, "GET", other.URL+"/api/csrf", "")
	if decode[map[string]string](t, data)["token"] == token {
		t.Fatal("separate server instances share a token")
	}

	// Clients without browser metadata still need the capability, even with valid JSON.
	for _, test := range []struct {
		target, token string
		status        int
	}{
		{srv.URL, "", 403},
		{other.URL, token, 403},
		{srv.URL, token, 201},
	} {
		req, err := http.NewRequest("POST", test.target+"/api/runs", strings.NewReader(`{"scenario":"branch","unitMs":10}`))
		if err != nil {
			t.Fatal(err)
		}
		req.Header.Set("Content-Type", "application/json; charset=utf-8")
		req.Header.Set(csrfHeader, test.token)
		res, err := http.DefaultClient.Do(req)
		if err != nil {
			t.Fatal(err)
		}
		res.Body.Close()
		if res.StatusCode != test.status {
			t.Errorf("POST %s with token %q: %d, want %d", test.target, test.token, res.StatusCode, test.status)
		}
	}
}

func TestLocalHandlerProtectsReadsAndPreflight(t *testing.T) {
	h, err := newServer(context.Background(), nil).localHandler(nil, &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 8080})
	if err != nil {
		t.Fatal(err)
	}
	for _, path := range []string{"/api/csrf", "/api/scenarios", "/api/runs/r1/events", "/"} {
		for _, test := range []struct{ header, value string }{
			{"Host", "attacker.test:8080"},
			{"Origin", "https://attacker.test"},
			{"Sec-Fetch-Site", "cross-site"},
			{"Sec-Fetch-Site", "same-site"},
		} {
			req := httptest.NewRequest("GET", "http://127.0.0.1:8080"+path, nil)
			if test.header == "Host" {
				req.Host = test.value
			} else {
				req.Header.Set(test.header, test.value)
			}
			res := httptest.NewRecorder()
			h.ServeHTTP(res, req)
			if res.Code != http.StatusForbidden || strings.Contains(res.Body.String(), `"token"`) {
				t.Errorf("%s %s=%s: %d %s", path, test.header, test.value, res.Code, res.Body.String())
			}
		}
	}
	req := httptest.NewRequest("OPTIONS", "http://127.0.0.1:8080/api/runs", nil)
	req.Header.Set("Origin", "https://attacker.test")
	req.Header.Set("Access-Control-Request-Method", "POST")
	req.Header.Set("Access-Control-Request-Headers", "Content-Type, X-CSRF-Token")
	res := httptest.NewRecorder()
	h.ServeHTTP(res, req)
	if res.Code != http.StatusForbidden || res.Header().Get("Access-Control-Allow-Origin") != "" {
		t.Fatalf("preflight: %d %v", res.Code, res.Header())
	}
}

func TestLocalHandlerLoopbackHosts(t *testing.T) {
	for _, ip := range []string{"127.0.0.1", "::1"} {
		h, err := newServer(context.Background(), nil).localHandler(nil, &net.TCPAddr{IP: net.ParseIP(ip), Port: 8080})
		if err != nil {
			t.Fatal(err)
		}
		for _, host := range []string{net.JoinHostPort(ip, "8080"), "localhost:8080"} {
			for _, site := range []string{"same-origin", "none"} {
				req := httptest.NewRequest("GET", "http://"+host+"/api/csrf", nil)
				req.Header.Set("Origin", "http://"+host)
				req.Header.Set("Sec-Fetch-Site", site)
				res := httptest.NewRecorder()
				h.ServeHTTP(res, req)
				if res.Code != http.StatusOK {
					t.Errorf("%s %s: %d %s", host, site, res.Code, res.Body.String())
				}
			}
		}
	}
}

func TestListenLoopback(t *testing.T) {
	for _, address := range []string{":0", "0.0.0.0:0", "[::]:0", "192.0.2.1:0", "[2001:db8::1]:0"} {
		listener, err := listenLoopback(address)
		if err == nil {
			listener.Close()
			t.Errorf("accepted non-loopback listener %s", address)
		} else if !strings.Contains(err.Error(), "loopback") {
			t.Errorf("%s: rejected after validation: %v", address, err)
		}
	}
	for _, address := range []string{"127.0.0.1:0", "localhost:0"} {
		listener, err := listenLoopback(address)
		if err != nil {
			t.Fatal(err)
		}
		if addr := listener.Addr().(*net.TCPAddr); !addr.IP.IsLoopback() || addr.Port == 0 {
			t.Errorf("unexpected bound address: %s", addr)
		}
		listener.Close()
	}
}
