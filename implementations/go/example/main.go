// Command example is a playground for the suimon Go runtime: a few definitions (definitions/*.json)
// run with Go functions whose I/O is simulated with sleeps. Without -ui it runs one scenario and
// prints the spans of user code and the report; with -ui it serves the browser UI and its API.
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"net"
	"net/http"
	"os"
	"os/signal"
	"strings"
	"time"
)

const defaultUnit = 250 * time.Millisecond

func main() {
	ui := flag.Bool("ui", false, "serve the browser UI and the JSON API")
	listen := flag.String("listen", "127.0.0.1:8080", "listen address for -ui")
	uiDir := flag.String("ui-dir", "example/ui/dist", "the built UI (relative to the working directory)")
	name := flag.String("scenario", "stream", "the scenario to run without -ui")
	unit := flag.Duration("unit", defaultUnit, "one unit of simulated I/O (10ms to 400ms; the timeout scenario allows 1s per call)")
	flag.Parse()
	if *unit < 10*time.Millisecond || *unit > 400*time.Millisecond {
		log.Fatal("-unit must be between 10ms and 400ms")
	}
	scenarios, err := loadScenarios()
	if err != nil {
		log.Fatal(err)
	}
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt)
	defer stop()
	if *ui {
		if err := serve(ctx, scenarios, *listen, *uiDir, *unit); err != nil {
			log.Fatal(err)
		}
		return
	}
	if err := runOnce(ctx, scenarios, *name, *unit); err != nil {
		log.Fatal(err)
	}
}

func serve(ctx context.Context, scenarios []*scenario, address, dir string, unit time.Duration) error {
	assets, err := uiAssets(dir)
	if err != nil {
		return err
	}
	listener, err := net.Listen("tcp", address)
	if err != nil {
		return err
	}
	fmt.Printf("suimon playground: http://%s\n", listener.Addr())
	srv := &http.Server{Handler: newServer(ctx, scenarios, unit).handler(assets), ReadHeaderTimeout: 5 * time.Second}
	go func() {
		<-ctx.Done()
		_ = srv.Close()
	}()
	if err := srv.Serve(listener); err != http.ErrServerClosed {
		return err
	}
	return nil
}

func runOnce(ctx context.Context, scenarios []*scenario, name string, unit time.Duration) error {
	var ids []string
	for _, sc := range scenarios {
		ids = append(ids, sc.ID)
		if sc.ID != name {
			continue
		}
		r, err := startRun(ctx, "cli", sc, sc.Input, unit)
		if err != nil {
			return err
		}
		r.wait()
		report, runErr, _ := r.result()
		if report == nil {
			return fmt.Errorf("the run did not finish: %s", runErr)
		}
		for _, s := range r.env.snapshot() {
			end := "running"
			if s.EndMs != nil {
				end = fmt.Sprintf("%7.1fms", *s.EndMs)
			}
			fmt.Printf("%7.1fms - %s  %-14s %-12s %s\n", s.StartMs, end, s.Function, s.Detail, s.Outcome)
		}
		out, err := json.MarshalIndent(report, "", "  ")
		if err != nil {
			return err
		}
		fmt.Println(string(out))
		return nil
	}
	return fmt.Errorf("unknown scenario %q; one of %s", name, strings.Join(ids, ", "))
}
