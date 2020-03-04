Module process.T

use stdlib


type process is record abortedx:boolean, a:seq.word, resultb:T

Function aborted(p:process.T)boolean builtin.usemangle

Function message(p:process.T)seq.word 
 if aborted.p then a.p else"normal exit"

Function result(p:process.T)T 
 assert not.aborted.p report"no result of aborted process"
  subresult(p, 2)

function subresult(a:process.T, b:int)T builtin."PARAM 1 PARAM 2 IDXUC"

Note:Must access result of process with function result rather than using field resultb because if the type T is a structure of more than one element, the compile would assume the elements are store at resultb and not a pointer to the type T.

Function process(T)process.T builtin.usemangle

______________

