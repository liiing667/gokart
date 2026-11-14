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

/*
Package util implements underlying functionality for building and traversing call graphs,
configuraing and building analyzers and generating findings
*/
package util

import (
	"bufio"
	"bytes"
	"fmt"
	"go/token"
	"go/types"
	"os"
	"runtime"
	"strings"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/ssa"

	"github.com/segmentio/fasthash/fnv1a"
)

type ReturnSet = []ssa.Value

// ReturnValues returns a set of the return values of the function
func ReturnValues(fn *ssa.Function) []ReturnSet {
	res := []ReturnSet{}

	for _, block := range fn.DomPreorder() {
		// a returning block ends in a Return instruction and has no successors
		if len(block.Succs) != 0 {
			continue
		}

		if ret, ok := block.Instrs[len(block.Instrs)-1].(*ssa.Return); ok {
			res = append(res, ret.Results[:])
		}
	}

	return res
}

// CGRelation is a struct that contains information about an instruction and a function in the call graph
type CGRelation struct {
	Instr *ssa.Call
	Fn    *ssa.Function
}
type CallGraph map[string][]CGRelation

// InvokeKey returns the call graph key under which interface (invoke-mode) calls
// to a method with the given name are stored
func InvokeKey(methodName string) string {
	return "invoke:" + methodName
}

// InvokeImplKey returns the call graph key under which methods (potential
// interface implementations) with the given name are registered
func InvokeImplKey(methodName string) string {
	return "impl:" + methodName
}

// AnalyzeFunction updates the CallGraph to contain relations between callee and caller functions. This should be called once on every function in a local package
func (cg CallGraph) AnalyzeFunction(fn *ssa.Function) {
	// Register methods so that interface (invoke-mode) calls can be resolved
	// to their possible implementations
	if fn.Signature.Recv() != nil {
		key := InvokeImplKey(fn.Name())
		cg[key] = append(cg[key], CGRelation{nil, fn})
	}
	for _, block := range fn.DomPreorder() {
		for _, instr := range block.Instrs {
			switch instr := instr.(type) {
			case *ssa.Call:
				if callee := instr.Call.StaticCallee(); callee != nil {
					// Update the callgraph
					// Note: StaticCallee resolves direct closure (MakeClosure) calls as well
					cg[callee.String()] = append(cg[callee.String()], CGRelation{instr, fn})
				} else if instr.Call.IsInvoke() {
					// Record interface method calls so that taint can be traced
					// through dynamic dispatch to the concrete implementations
					key := InvokeKey(instr.Call.Method.Name())
					cg[key] = append(cg[key], CGRelation{instr, fn})
				}
			}
		}
	}
}

// ParamIndex returns the index of a parameter within its parent function's parameter list, or -1 if not found
func ParamIndex(p *ssa.Parameter) int {
	for i, arg := range p.Parent().Params {
		if p == arg {
			return i
		}
	}
	return -1
}

// ResolveParam returns the caller nodes of a parameter. This is used for tracing parameters back to their source.
func (cg CallGraph) ResolveParam(p *ssa.Parameter) []*ssa.Value {
	// Determine which argument we are in the parent function
	pFunc := p.Parent()
	pIdx := ParamIndex(p)
	if pIdx < 0 {
		return nil
	}
	// Find all the places the function is called
	relations := cg[pFunc.String()]
	// If the parent function is a method, also consider interface (invoke-mode)
	// call sites whose receiver may dispatch to this implementation
	if recv := pFunc.Signature.Recv(); recv != nil {
		relations = append(relations, cg.matchingInvokes(pFunc, recv.Type())...)
	}
	callerNodes := make([]*ssa.Value, 0, len(relations))
	for _, rel := range relations {
		if rel.Instr.Call.IsInvoke() {
			// For invoke-mode calls the receiver is the call value itself and
			// Args holds only the actual parameters
			if pIdx == 0 {
				callerNodes = append(callerNodes, &rel.Instr.Call.Value)
			} else if pIdx-1 < len(rel.Instr.Call.Args) {
				callerNodes = append(callerNodes, &rel.Instr.Call.Args[pIdx-1])
			}
		} else if pIdx < len(rel.Instr.Call.Args) {
			// Static (method) calls include the receiver as the first argument
			callerNodes = append(callerNodes, &rel.Instr.Call.Args[pIdx])
		}
	}
	return callerNodes
}

// matchingInvokes returns the interface call sites whose receiver type may be
// implemented by the given method receiver type
func (cg CallGraph) matchingInvokes(pFunc *ssa.Function, recvType types.Type) []CGRelation {
	var matches []CGRelation
	for _, rel := range cg[InvokeKey(pFunc.Name())] {
		iface, ok := rel.Instr.Call.Value.Type().Underlying().(*types.Interface)
		if !ok {
			continue
		}
		if types.Implements(recvType, iface) {
			matches = append(matches, rel)
			continue
		}
		if _, isPtr := recvType.(*types.Pointer); !isPtr && types.Implements(types.NewPointer(recvType), iface) {
			matches = append(matches, rel)
		}
	}
	return matches
}

// ResolveInvoke returns the possible implementations of an interface
// (invoke-mode) method call
func (cg CallGraph) ResolveInvoke(call *ssa.CallCommon) []*ssa.Function {
	if !call.IsInvoke() {
		return nil
	}
	iface, ok := call.Value.Type().Underlying().(*types.Interface)
	if !ok {
		return nil
	}
	var fns []*ssa.Function
	for _, rel := range cg[InvokeImplKey(call.Method.Name())] {
		fn := rel.Fn
		if fn == nil || fn.Signature.Recv() == nil {
			continue
		}
		recvType := fn.Signature.Recv().Type()
		if types.Implements(recvType, iface) {
			fns = append(fns, fn)
			continue
		}
		if _, isPtr := recvType.(*types.Pointer); !isPtr && types.Implements(types.NewPointer(recvType), iface) {
			fns = append(fns, fn)
		}
	}
	return fns
}

// Memoize adds a TaintKey to the Taint Map while updating the metadata
func (ta TaintAnalyzer) Memoize(key TaintKey, vulnerable bool) {
	// get the current map status
	map_status := ta.taint_map[key]
	// increment the count
	new_count := map_status.Count + 1
	// create the new MapData struct
	mapping := MapData{Mapped: map_status.Mapped, Vulnerable: map_status.Vulnerable, Count: new_count}
	// update the Taint Map
	ta.taint_map[key] = mapping
}

// SSAvalToHash returns the hash of an ssa.Value to be used in the Taint Map
func SSAvalToHash(val *ssa.Value) uint64 {
	// convert the de-referenced ssa.Value to a byte array
	b_arrayPointer := []byte(fmt.Sprintf("%v", *val))
	// convert the byte array to a string
	val_string := string(b_arrayPointer)
	// if the ssa.Value has a parent, add that to the val_string to be used in the hash. Otherwise just hash the val_string
	if (*val).Parent() != nil {
		b_arrayParent := (*val).Parent().String()
		val_string += b_arrayParent
	}

	// hash the val_string
	hash := fnv1a.HashString64(val_string)
	return hash
}

// TaintKey uniquely identifies an ssa.Value within a specific calling context.
// Caching taint results per (value, context) pair keeps a verdict computed for
// one call site from leaking into the analysis of another call site.
type TaintKey struct {
	Value   uint64
	Context uint64
}

// CallContext is a call-string style stack of the call instructions through
// which the taint analysis descended into the current function body
type CallContext []*ssa.Call

// maxContextDepth bounds the length of a CallContext (call-string k-limiting) so
// that recursive call cycles produce a finite number of distinct contexts
const maxContextDepth = 4

// PushContext returns a new CallContext with the given call appended, dropping
// the oldest frame if the context exceeds the maximum depth
func PushContext(ctx CallContext, call *ssa.Call) CallContext {
	newCtx := make(CallContext, len(ctx)+1)
	copy(newCtx, ctx)
	newCtx[len(ctx)] = call
	if len(newCtx) > maxContextDepth {
		newCtx = newCtx[len(newCtx)-maxContextDepth:]
	}
	return newCtx
}

// MatchCallContext returns the index of the innermost context frame that calls
// the given function, or -1 if there is no such frame
func MatchCallContext(ctx CallContext, fn *ssa.Function) int {
	for i := len(ctx) - 1; i >= 0; i-- {
		if ctx[i].Call.StaticCallee() == fn {
			return i
		}
	}
	return -1
}

// HashContext returns a hash of a CallContext to be used in the TaintKey
func HashContext(ctx CallContext) uint64 {
	var sb strings.Builder
	for _, call := range ctx {
		fmt.Fprintf(&sb, "%p;", call)
	}
	return fnv1a.HashString64(sb.String())
}

// GrabSourceCode retrieves the specified line of source code from the specified file
func GrabSourceCode(filename string, lineNumber int) string {

	fileHandle, _ := os.Open(filename)
	defer fileHandle.Close()

	var buff bytes.Buffer
	scanner := bufio.NewScanner(fileHandle)
	scanner.Split(bufio.ScanLines)

	counter := 0

	for scanner.Scan() {
		counter++
		if lineNumber == counter {
			buff.WriteString(scanner.Text())
			break
		}
	}
	return buff.String()
}

// GenerateTaintedCode returns a TaintedCode struct that stores information (source code, filename, linenumber) for a line of code
func GenerateTaintedCode(pass *analysis.Pass, parent *ssa.Function, position token.Pos) TaintedCode {
	vulnerable_code := pass.Fset.Position(position)

	// Evaluate $GOROOT environment variable so correct filepath is generated.
	expanded_filename := os.ExpandEnv(vulnerable_code.Filename)
	if _, err := os.Stat(expanded_filename); os.IsNotExist(err) {
		if strings.Contains(vulnerable_code.Filename, "$GOROOT") {
			vulnerable_code.Filename = strings.Replace(vulnerable_code.Filename, "$GOROOT", runtime.GOROOT(), 1)
		} else {
			vulnerable_code.Filename = "WARNING: Could not find the file at path: " + vulnerable_code.Filename
		}
	} else {
		vulnerable_code.Filename = expanded_filename
	}

	vulnerable_source_code := GrabSourceCode(vulnerable_code.Filename, vulnerable_code.Line)

	var parent_function_name string
	var parent_function_args string
	if parent == nil {
		parent_function_name = "<no parent>"
		parent_function_args = "<no parent - no args>"
	} else {
		parent_function_name = parent.Name()
		parent_function_args = strings.Split(parent.Signature.String(), "func")[1]
	}
	tainted_code := TaintedCode{
		SourceCode:     vulnerable_source_code,
		SourceFilename: vulnerable_code.Filename,
		SourceLineNum:  vulnerable_code.Line,
		ParentFunction: parent_function_name + " " + parent_function_args,
	}
	return tainted_code
}
