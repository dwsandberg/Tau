#!/bin/bash tau stdlib webassembly testgraphw testgraph.

Module webassembly

Library webassembly funcidx knownWfunc printfunc wasm wasm2 wasmcompile
uses stdlib
exports wasm wasm1 wasm2 wasmcompile webassembly

* usegraph exclude standard seq set otherseq bits encoding UTF8 stack

use UTF8

use bits

use compilerfront

use format

use libraryModule

use standard

use symbol2

use wasmcompile

use wasmconstant

use seq.byte

use seq.char

use seq.int

use set.int

use seq.mytype

use seq.symbol

use set.symbol

use set.symdef

use process.seq.word

use seq.seq.word

use IO2

Function entrypoint(s:UTF8)UTF8
let args = towords.s
let p = process.glue(args_1, args << 1)
HTMLformat.if aborted.p then message.p else result.p


function glue(lib:word, pages:seq.word)seq.word
{problem is same symbol is used in different onclicks}
let includetemplate = false
let libname = [lib]
let info2 = getlibrarysrc.libname
let exports = "tausupport inputoutput" + info2_3
let r = 
 compilerfront("wasm"
 , lib
 , getlibrarysrc.info2_1 + info2 << 3
 , {dependentlibs}empty:loadedresult
 , exports
 )
let syms2 = 
 for syms2 = empty:seq.symbol, m ∈ mods.r do
  if name.modname.m ∈ info2_3 then
   for txt3 = syms2, e ∈ exports.m do txt3 + (symbolrefdecode.r)_(toint.e)/for(txt3)
  else syms2
 /for({should check for dup names on syms}syms2)
let scriptstart = 
 for txt = "<script>  /br", sym ∈ syms2 do
  let f = 
   for args = "", i ∈ arithseq(nopara.sym, 1, 1)do args + "a b c d e f g h i j k l m n o p q r s t u v w x y z"_i + ", "/for([name.sym] + "(" + args >> 1 + ")")
  {Cannot just call reclaimspace after call to function f because f may be interpreted and return control will waiting for 
a callback. javascript global inprogress counts the number of callbacks we are waiting for. if inprogress is zero then 
it is safe to reclaim space.}
  txt
  + "function"
  + f
  + "{exports."
  + f
  + "; if(inprogress==0)exports.reclaimspace();} /br"
 /for(txt)
let prg = asset.prg.r
let discard99 = oldconstants.prg
let discard2 = wasmcompile(typedict.r, prg, syms2, [lib])
let script = 
 if includetemplate then
  toseqbyte.toUTF8."<script>" + getfile:byte("webassembly/template.js")
  + toseqbyte.toUTF8."</script>"
 else toseqbyte.toUTF8.' <script src="/webassembly/template.js"> </script> '
for txt = "", page ∈ pages
while page ∉ ". ."
do let pagehtml = getfile:byte([lib] + "/" + page + ".html")
let htmlname = "tmp/" + page + ".html"
let discard = 
 createfile(htmlname
 , pagehtml+script
 + toseqbyte.toUTF8(scriptstart + '  /br pageinit("' + lib + '", ' + page + "); </script>")
 )
txt + ' <a href="' + merge("//localhost/" + htmlname + '"> ') + page
+ "</a>"
/for(" /< noformat" + txt + " />" + discard2)

Function findsymbol(prg:set.symdef, symname:seq.word)seq.symbol
for actionsym = empty:seq.symbol, sym ∈ toseq.prg do
 if[name.sym.sym] = symname then actionsym + sym.sym else actionsym
/for(assert length.actionsym = 1 report"findsymbol" + symname
actionsym)

Function doc seq.word
"Steps to call function f1 as a process.
/br 1. Create a record, R. The first two fields are deepcopy function for the result type of f1 and seq.word. The third field 
is the webassembly funcidx. The remain fields are the actual parameters of f1.
/br 2. get typeidx for f1. Let assume the typeidx is 45.
/br 3. create at compile time a function processX45 that takes the record R and funcidx of f1 as parameters, unpacks the record 
R and calls the third field in R. In this case it will call f1. 
/br 4. call the javascript function callprocess with R and function index of processX45 as parameters.
/br 5. callprocess will call exported function,  /em processbody, with R and processX45 as parameters 
/br 6. processbody will call  /em processX45 with R as parameter in a new process context and restore the orignal context when it 
finishes. if the first field of R is not zero then it will deepcopy the result. Finally it will release any space used by the 
new process.
/br 7. If f1 aborts then processbody will catch the error and call exported function  /em handleerror 
/br 8.  /em handleerror restores the parent process context and copies the errormessage to the parent process. Finally it will 
release any space used by the process" 