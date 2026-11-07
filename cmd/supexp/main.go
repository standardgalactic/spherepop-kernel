// Command supexp runs the experiment that compares the scoped design, in
// which the reducer's configuration decides what a step may do, with a
// supervised baseline, in which a flat worker proposes and a separate
// supervisor decides.
//
//	supexp diff    differential run over the corpus, and its positive control
//	supexp count   trusted code reachable from each design's acceptance function
//	supexp mutate  record-tampering matrix
//	supexp time    cost per accepted step
//	supexp all     all four
package main

import (
	"fmt"
	"os"
)

func main() {
	cmd := "all"
	if len(os.Args) > 1 {
		cmd = os.Args[1]
	}
	var err error
	switch cmd {
	case "diff":
		if err = runDiff(); err == nil {
			err = runDiffControl(1, 1000, 5, 60)
		}
	case "count":
		err = runCount()
	case "mutate":
		err = runMutate()
	case "time":
		err = runTime()
	case "all":
		for i, f := range []func() error{runDiff, func() error { return runDiffControl(1, 1000, 5, 60) }, runCount, runMutate, runTime} {
			if i == 2 || i == 3 || i == 4 {
				fmt.Println()
			}
			if err = f(); err != nil {
				break
			}
		}
	default:
		err = fmt.Errorf("unknown subcommand %q (want diff, count, mutate, time or all)", cmd)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "supexp:", err)
		os.Exit(1)
	}
}
