Module process.T

use stdlib


use seq.T

type process is record abortedx:boolean, a:seq.word, resultb:T

Function aborted(p:process.T)boolean builtin.usemangle

Function message(p:process.T)seq.word if aborted.p then a.p else"normal exit"

Function result(p:process.T)T
 assert not.aborted.p report"no result of aborted process"
 // The compiler has a special case to handle accessing process resultb
 because if the type T is a structure of more than one element, then compiler would normally assume 
 the elements are store at resultb and not a pointer to the type T. //
 resultb.p
 

Function deepcopy(a:T)T builtin.usemangle

Function sizeoftype:T int builtin.usemangle



