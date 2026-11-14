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

package util

import (
	"go/token"
	"log"
	"strings"

	"golang.org/x/tools/go/analysis"

	"golang.org/x/tools/go/ssa"
)

// TaintedCode is a struct that contains information about the vulnerable line of code
type TaintedCode struct {
	SourceCode     string
	SourceFilename string
	SourceLineNum  int
	ParentFunction string
}

//MapData is a struct that contains information about each hash
type MapData struct {
	Mapped     bool // whether a hash has already been mapped
	Vulnerable bool // whether a hash has been found vulnerable
	Count      int  // the number of times a hash has been visited
}

// TaintAnalyzer is a struct that contains information about each taint analyzer
type TaintAnalyzer struct {
	taint_map   map[TaintKey]MapData
	TaintSource []TaintedCode
	pass        *analysis.Pass
	location    token.Pos
}

// CreateTaintAnalyzer returns a new TaintAnalyzer struct
func CreateTaintAnalyzer(pass *analysis.Pass, location token.Pos) TaintAnalyzer {
	return TaintAnalyzer{
		make(map[TaintKey]MapData),
		[]TaintedCode{},
		pass,
		location,
	}
}

// ContainsTaint analyzes the ssa.Value, recursively traces the value to all possible sources, and returns True if any of the sources are vulnerable. It returns False otherwise.
func (ta *TaintAnalyzer) ContainsTaint(startCall *ssa.CallCommon, val *ssa.Value, cg CallGraph) bool {
	return ta.ContainsTaintRecurse(startCall, val, cg, 0, []ssa.Value{}, CallContext{})
}

func (ta *TaintAnalyzer) ContainsTaintRecurse(startCall *ssa.CallCommon, val *ssa.Value, cg CallGraph, depth int, visitedMutable []ssa.Value, ctx CallContext) bool {
	if *val == nil {
		return false
	}
	if Config.Debug {
		out := ""
		for i := 0; i < depth; i++ {
			out += "  "
		}
		log.Printf("%s%s (%T)\n", out, *val, *val)
	}

	call, isCall := (*val).(*ssa.Call)
	if isCall {
		//A function call cannot become tainted from itself This is due to a bug with how we handle referrers. Since we
		//check all function calls, past and future, we need to make sure to ignore the starting function call
		//This makes sure we dont duplicate findings by having one parameter infect other parameters
		if startCall == &call.Call {
			return false
		}
	}

	//We have already seen this buffer, assume its fine
	for _, visitedVal := range visitedMutable {
		if *val == visitedVal {
			return false
		}
	}

	// Memoize the ssa.Value
	key := TaintKey{Value: SSAvalToHash(val), Context: HashContext(ctx)}
	map_status1 := ta.taint_map[key]
	ta.Memoize(key, map_status1.Vulnerable)
	// Store the memoization status in map_status
	map_status := ta.taint_map[key]

	// if the ssa.Value hash has been seen over fifty times, return false because it is likely an infinite loop
	if map_status.Count > 20 {
		if Config.Debug {
			log.Printf("Overflow detected, breaking the infinite loop")
		}

		return false
	}
	// if the ssa.Value hash has already been mapped, return it's vulnerable status
	if map_status.Mapped {
		return map_status.Vulnerable
	}

	//default set vulnerable to false, this may not be necessary anymore
	vulnerable := false

	switch expr := (*val).(type) {
	case *ssa.Const:
		vulnerable = false
	case *ssa.Parameter:
		// Check if this function call is part of the tainted function source list
		globalPkgName := (expr).Parent().Pkg.Pkg.Name()
		if val, ok := VulnGlobalFuncs[globalPkgName]; ok {
			for _, funcName := range val {
				if (expr).Name() == funcName {
					vulnerable = true
				}
			}
		}

		for pkg, types_ := range VulnTypes {
			for _, type_ := range types_ {
				if strings.TrimPrefix(expr.Type().String(), "*") == pkg+"."+type_ {
					vulnerable = true
				}
			}
		}

		// If we reached this parameter by descending through a specific call
		// site, resolve it to the argument of that call site only. Otherwise
		// take the union of every known call site of the parent function.
		pIdx := ParamIndex(expr)
		callIdx := MatchCallContext(ctx, expr.Parent())
		if callIdx >= 0 && pIdx >= 0 && pIdx < len(ctx[callIdx].Call.Args) {
			arg := ctx[callIdx].Call.Args[pIdx]
			vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &arg, cg, depth+1, visitedMutable, ctx[:callIdx]) //loop B
		} else {
			for _, callerArg := range cg.ResolveParam(expr) {
				vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, callerArg, cg, depth+1, visitedMutable, ctx) //loop B
			}
		}
	case *ssa.FreeVar:
		// Resolve the free variable to the value bound at the closure creation site
		parent := expr.Parent()
		bindingIdx := -1
		for i, freeVar := range parent.FreeVars {
			if freeVar == expr {
				bindingIdx = i
				break
			}
		}
		if bindingIdx >= 0 {
			resolved := false
			// If we descended through a specific closure call, use the bindings of that closure
			for i := len(ctx) - 1; i >= 0; i-- {
				if mc, ok := ctx[i].Call.Value.(*ssa.MakeClosure); ok && mc.Fn == parent && bindingIdx < len(mc.Bindings) {
					binding := mc.Bindings[bindingIdx]
					vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &binding, cg, depth+1, visitedMutable, ctx[:i])
					resolved = true
					break
				}
			}
			if !resolved {
				// Otherwise take the union of the bindings of every recorded closure call site
				for _, rel := range cg[parent.String()] {
					if mc, ok := rel.Instr.Call.Value.(*ssa.MakeClosure); ok && mc.Fn == parent && bindingIdx < len(mc.Bindings) {
						binding := mc.Bindings[bindingIdx]
						vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &binding, cg, depth+1, visitedMutable, ctx)
					}
				}
			}
		}
	case *ssa.Function:
		// Assume that the user cannot create their own functions
		vulnerable = false
	case *ssa.Field:
		vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.Next:
		vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &expr.Iter, cg, depth+1, visitedMutable, ctx)
	case *ssa.TypeAssert:
		vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.Range:
		vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.Phi:
		mapping := MapData{Mapped: true, Vulnerable: false}
		ta.taint_map[key] = mapping
		for _, edge := range (*expr).Edges {

			// this if statement is to prevent infiinite loop
			if edge != expr {
				vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &edge, cg, depth+1, visitedMutable, ctx)
			}
		}
	case *ssa.UnOp:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.BinOp:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx) || ta.ContainsTaintRecurse(startCall, &expr.Y, cg, depth+1, visitedMutable, ctx)
	case *ssa.Extract:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.Tuple, cg, depth+1, visitedMutable, ctx)
	case *ssa.Call:
		callFunc, ok := (expr.Call.Value).(*ssa.Function)
		if ok {
			globalPkgName := callFunc.Pkg.Pkg.Name()
			if val, ok := VulnGlobalFuncs[globalPkgName]; ok {
				for _, funcName := range val {
					if callFunc.Name() == funcName {
						vulnerable = true
					}
				}
			}
		}
		if dest := expr.Common().StaticCallee(); dest != nil {
			returns := ReturnValues(dest)

			/* If return values of function can't be determined then we run under the assumption
			 * that if you can trust the arguments to the function, then you can trust the return value of the function.
			 */
			if len(returns) > 0 {
				// Record the call site as context so that parameters and free
				// variables of the callee resolve to this specific call
				newCtx := PushContext(ctx, expr)
				for _, retval := range returns {
					if len(retval) > 0 {
						vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &retval[0], cg, depth+1, visitedMutable, newCtx)
					}
				}
			} else {
				for _, arg := range expr.Call.Args {

					vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &arg, cg, depth+1, visitedMutable, ctx) //loop C
				}
			}
		} else {
			// The callee is not statically known (interface dispatch, function
			// values, ...). For interface calls, trace the return values of
			// every possible implementation.
			resolved := false
			if expr.Call.IsInvoke() {
				newCtx := PushContext(ctx, expr)
				for _, impl := range cg.ResolveInvoke(&expr.Call) {
					resolved = true
					for _, retval := range ReturnValues(impl) {
						if len(retval) > 0 {
							vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &retval[0], cg, depth+1, visitedMutable, newCtx) //loop C
						}
					}
				}
			}
			if !resolved {
				for _, arg := range expr.Call.Args {
					vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &arg, cg, depth+1, visitedMutable, ctx) //loop C
				}
				ta.pass.Reportf(ta.location, "Warning: Couldn't evaluate function statically")
			}
		}
	case *ssa.Slice:
		valSlice := ssa.Slice(*expr)
		valSliceX := valSlice.X
		vulnerable = ta.ContainsTaintRecurse(startCall, &valSliceX, cg, depth+1, visitedMutable, ctx) //loop D
		refs := valSlice.Referrers()
		for _, ref := range *refs {
			expr, isVal := ref.(ssa.Value)
			if isVal {
				newMutable := make([]ssa.Value, len(visitedMutable)+1)
				copy(newMutable, visitedMutable)
				newMutable = append(newMutable, *val)
				vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &expr, cg, depth+1, newMutable, ctx)
			}
		}
	case *ssa.MakeSlice:
		// MakeSlice is only used for new allocations and, as such, is
		// inherently safe.
		vulnerable = false
	case *ssa.Convert:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.ChangeType:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.MakeInterface:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.MakeMap:
		vulnerable = false
	case *ssa.MakeClosure:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.Fn, cg, depth+1, visitedMutable, ctx)
		for _, val := range expr.Bindings {
			vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &val, cg, depth+1, visitedMutable, ctx)
		}
	case *ssa.Lookup:
		// Traces not only the collection but also the source of the index
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx) || ta.ContainsTaintRecurse(startCall, &expr.Index, cg, depth+1, visitedMutable, ctx)
	case *ssa.Index:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx) || ta.ContainsTaintRecurse(startCall, &expr.Index, cg, depth+1, visitedMutable, ctx)
	case *ssa.ChangeInterface:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.IndexAddr:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.FieldAddr:
		vulnerable = ta.ContainsTaintRecurse(startCall, &expr.X, cg, depth+1, visitedMutable, ctx)
	case *ssa.Alloc:
		// Check all the references to this memory
		alloc_refs := expr.Referrers()
		vulnerable = false

		mapping := MapData{Mapped: true, Vulnerable: false}
		ta.taint_map[key] = mapping

		for alloc_item := range *alloc_refs {
			alloc_ref := (*alloc_refs)[alloc_item]

			switch instr := (alloc_ref).(type) {
			case *ssa.IndexAddr:
				for indexaddr_ref_idx := range *instr.Referrers() {
					indexaddr_ref := (*instr.Referrers())[indexaddr_ref_idx]
					switch instr2 := (indexaddr_ref).(type) {
					// If the variable is assigned to something else, check
					// the new assignment
					case *ssa.Store:
						if ta.ContainsTaintRecurse(startCall, &instr2.Val, cg, depth+1, visitedMutable, ctx) { //loop A -- I think this might be causing the problem
							vulnerable = true
						}
					}
				}

			case *ssa.FieldAddr:
				for _, ref := range *instr.Referrers() {
					expr, isStore := (ref).(*ssa.Store)
					if isStore {
						newMutable := make([]ssa.Value, len(visitedMutable)+1)
						copy(newMutable, visitedMutable)
						newMutable = append(newMutable, *val)
						vulnerable = vulnerable || ta.ContainsTaintRecurse(startCall, &expr.Val, cg, depth+1, newMutable, ctx)
					}
				}
			}

			var items []*ssa.Value
			operand_items := alloc_ref.Operands(items)
			for operand_idx := range operand_items {
				if ta.ContainsTaintRecurse(startCall, operand_items[operand_idx], cg, depth+1, visitedMutable, ctx) {
					vulnerable = true
				}
			}
		}
	case *ssa.Global:
		if Config.Debug {
			test := GenerateTaintedCode(ta.pass, (*val).Parent(), (*val).Pos())
			log.Println("Global variable found: ", test.SourceCode, " in file ", test.SourceFilename)
		}
		vulnerable = !Config.GlobalsSafe
		globalPkgName := (expr).Package().Pkg.Name()
		if Config.Debug {
			log.Println("expr", expr, expr.Package())
			log.Println("gloablPkgName", globalPkgName, *val)
			log.Println(VulnGlobalVars)
		}

		if val, ok := VulnGlobalVars[globalPkgName]; ok {
			for _, funcName := range val {
				if (expr).Name() == funcName {
					if Config.Debug {
						log.Println(expr.Name())
						log.Println(funcName)
					}

					vulnerable = true
				}
			}
		}
	case nil:
		vulnerable = false
	default:
		vulnerable = true
		if Config.Debug {
			log.Printf("Unknown SSA type found: %T\n", expr)
		}
	}

	// Memoize the ssa.Value along with whether or not it is vulnerable
	ta.taint_map[key] = MapData{Mapped: true, Vulnerable: vulnerable, Count: ta.taint_map[key].Count}

	/* If the taint analysis reaches a vulnerable ssa.Value,
	 * then store the information about the state to display to the analyst as untrusted input.
	 */
	if vulnerable {
		tempTaintedCode := GenerateTaintedCode(ta.pass, (*val).Parent(), (*val).Pos())
		if tempTaintedCode.SourceLineNum > 0 {

			// Make sure that we don't output duplicate source code lines in Verbose Output
			duplicateSourceCode := false
			for _, current := range ta.TaintSource {
				if tempTaintedCode.SourceLineNum == current.SourceLineNum {
					duplicateSourceCode = true
					break
				}
			}

			if !duplicateSourceCode {
				ta.TaintSource = append(ta.TaintSource, tempTaintedCode)
			}
		}
	}

	return vulnerable
}
