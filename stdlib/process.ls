Module process.T

use seq.T

use stdlib

type process is record abortedx:boolean, a:seq.word, resultb:T

Builtin aborted(p:process.T)boolean

Function message(p:process.T)seq.word if aborted.p then a.p else"normal exit"

Function result(p:process.T)T
 assert not.aborted.p report"no result of aborted process"
  // The compiler has a special case to handle accessing process resultb because if the type T is a structure of more than one element, then compiler would normally assume the elements are store at resultb and not a pointer to the type T. //
  processresult.p

Builtin deepcopy(a:T)T

Builtin sizeoftype:T int

Builtin processresult(p:process.T)T