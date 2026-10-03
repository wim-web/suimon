//go:build !js

package main

import (
	"crypto/rand"
	"crypto/subtle"
	"encoding/hex"
	"fmt"
	"io/fs"
	"mime"
	"net"
	"net/http"
	"strconv"
)

const csrfHeader = "X-CSRF-Token"

func listenLoopback(address string) (*net.TCPListener, error) {
	addr, err := net.ResolveTCPAddr("tcp", address)
	if err != nil {
		return nil, err
	}
	if !addr.IP.IsLoopback() {
		return nil, fmt.Errorf("-listen must resolve to a loopback address")
	}
	// Bind the checked IP, without resolving the hostname again.
	return net.ListenTCP("tcp", addr)
}

// localHandler protects the native HTTP boundary. The WASM worker calls handler directly,
// within its own page, without a network listener or browser HTTP requests.
func (s *server) localHandler(assets fs.FS, address net.Addr) (http.Handler, error) {
	addr, ok := address.(*net.TCPAddr)
	if !ok || !addr.IP.IsLoopback() {
		return nil, fmt.Errorf("the playground requires a loopback listener")
	}
	var secret [32]byte
	if _, err := rand.Read(secret[:]); err != nil {
		return nil, fmt.Errorf("generate CSRF token: %w", err)
	}
	token := hex.EncodeToString(secret[:])
	localhost := net.JoinHostPort("localhost", strconv.Itoa(addr.Port))
	mux := http.NewServeMux()
	mux.HandleFunc("GET /api/csrf", func(w http.ResponseWriter, r *http.Request) {
		writeJSON(w, http.StatusOK, map[string]string{"token": token})
	})
	mux.Handle("/", s.handler(assets))
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("X-Content-Type-Options", "nosniff")
		if r.Host != addr.String() && r.Host != localhost {
			http.Error(w, "unexpected Host", http.StatusForbidden)
			return
		}
		if origins := r.Header.Values("Origin"); len(origins) != 0 && (len(origins) != 1 || origins[0] != "http://"+r.Host) {
			http.Error(w, "unexpected Origin", http.StatusForbidden)
			return
		}
		safe := r.Method == http.MethodGet || r.Method == http.MethodHead || r.Method == http.MethodOptions
		if sites := r.Header.Values("Sec-Fetch-Site"); len(sites) != 0 &&
			(len(sites) != 1 || (sites[0] != "same-origin" && !(safe && sites[0] == "none"))) {
			http.Error(w, "expected a same-origin request", http.StatusForbidden)
			return
		}
		if !safe {
			contentTypes := r.Header.Values("Content-Type")
			mediaType, _, err := mime.ParseMediaType(r.Header.Get("Content-Type"))
			if len(contentTypes) != 1 || err != nil || mediaType != "application/json" {
				http.Error(w, "expected application/json", http.StatusUnsupportedMediaType)
				return
			}
			tokens := r.Header.Values(csrfHeader)
			if len(tokens) != 1 || subtle.ConstantTimeCompare([]byte(tokens[0]), []byte(token)) != 1 {
				http.Error(w, "invalid CSRF token", http.StatusForbidden)
				return
			}
		}
		mux.ServeHTTP(w, r)
	}), nil
}
