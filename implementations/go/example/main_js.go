//go:build js && wasm

package main

import (
	"bytes"
	"context"
	"net/http"
	"strings"
	"syscall/js"
)

// The worker calls the same handlers as the local server, without opening a socket.
// Progress uses polling; the SSE handler requires a streaming ResponseWriter.
func main() {
	scenarios, err := loadScenarios()
	if err != nil {
		panic(err)
	}
	handler := newServer(context.Background(), scenarios).handler(nil)
	request := js.FuncOf(func(_ js.Value, args []js.Value) any {
		method, path, body := args[0].String(), args[1].String(), args[2].String()
		executor := js.FuncOf(func(_ js.Value, callbacks []js.Value) any {
			resolve, reject := callbacks[0], callbacks[1]
			// Return to JavaScript before running Go code that may wait for a timer.
			go func() {
				req, err := http.NewRequest(method, path, strings.NewReader(body))
				if err != nil {
					reject.Invoke(js.Global().Get("Error").New(err.Error()))
					return
				}
				response := &wasmResponse{header: make(http.Header), status: http.StatusOK}
				handler.ServeHTTP(response, req)
				resolve.Invoke(map[string]any{"status": response.status, "body": response.String()})
			}()
			return nil
		})
		promise := js.Global().Get("Promise").New(executor)
		executor.Release()
		return promise
	})
	defer request.Release()
	js.Global().Set("suimonRequest", request)
	js.Global().Call("suimonReady")
	select {}
}

type wasmResponse struct {
	bytes.Buffer
	header http.Header
	status int
}

func (w *wasmResponse) Header() http.Header    { return w.header }
func (w *wasmResponse) WriteHeader(status int) { w.status = status }
