// Copyright 2021 Praetorian Security, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// 5 vulnerabilities should be reported: callsite_order_vuln, closure_vuln,
// closure_param_vuln, interface_source_vuln and interface_dispatch_vuln
package main

import (
	"bufio"
	"fmt"
	"os"
	"os/exec"
)

func tainted_input() string {
	reader := bufio.NewReader(os.Stdin)
	fmt.Print("Enter command: ")
	text, _ := reader.ReadString('\n')
	return text
}

// passthrough returns its argument unchanged
func passthrough(s string) string {
	return s
}

// passthrough is called with a constant before it is called with user input;
// the tainted call site must still be flagged
func callsite_order_vuln() {
	_ = passthrough("safe constant")
	cmd := exec.Command("sh", "-c", passthrough(tainted_input()))
	cmd.Run()
}

// the sink only ever receives a constant even though passthrough is called
// with tainted data elsewhere; this must NOT be flagged
func callsite_order_safe() {
	_ = passthrough(tainted_input())
	cmd := exec.Command("sh", "-c", passthrough("safe constant"))
	cmd.Run()
}

// taint through a variable captured by a closure must be flagged
func closure_vuln() {
	userInput := tainted_input()
	wrap := func() string { return userInput }
	cmd := exec.Command("sh", "-c", wrap())
	cmd.Run()
}

// taint through a closure parameter must be flagged
func closure_param_vuln() {
	run := func(s string) string { return s }
	cmd := exec.Command("sh", "-c", run(tainted_input()))
	cmd.Run()
}

// taint sourced inside an interface implementation must be flagged at the
// interface call site
type StringSource interface {
	Get() string
}

type inputSource struct{}

func (inputSource) Get() string { return tainted_input() }

func interface_source_vuln() {
	var s StringSource = inputSource{}
	cmd := exec.Command("sh", "-c", s.Get())
	cmd.Run()
}

// taint flowing through an interface call into an implementation whose
// parameter reaches a sink must be flagged
type Runner interface {
	Run(string)
}

type cmdRunner struct{}

func (cmdRunner) Run(s string) {
	cmd := exec.Command("sh", "-c", s)
	cmd.Run()
}

func interface_dispatch_vuln() {
	var r Runner = cmdRunner{}
	r.Run(tainted_input())
}

func callsites_main() {
	callsite_order_vuln()
	callsite_order_safe()
	closure_vuln()
	closure_param_vuln()
	interface_source_vuln()
	interface_dispatch_vuln()
}
