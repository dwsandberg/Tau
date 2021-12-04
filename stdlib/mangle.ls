module mangle

use inputoutput

use libraryModule

use mytype

use standard

use symbol

use otherseq.char

use process.int

use seq.int

use seq.liblib

use seq.mytype

use otherseq.symbol

use otherseq.word

use set.word

function mangledname(s:symbol) seq.word
 assert not.isempty.worddata.s report "mangledname"+print.s
if wordname.s ∈ "entrypoint" then "entrypoint" 
else if wordname.s ∈ "addlibrarywords" ∧ name.module.s ∈ "main2"then
"addlibrarywordsZmain2Zliblib" 
else if name.module.s ∈ "internal"then [extname.s] else ""



Function mangledname(extname:set.symdef, s:symbol)word
 let t1=mangledname.s
if not.isempty.t1 then t1_1 else
   name.first.getCode(extname,s)


Function extname(sym:symbol)word
let name1 = "set+-/ * ? toint=> >> << ∨ ∧ tan cos sin sqrt GEP"
let i = findindex(name.sym, name1)
if i ≤ length.name1 then
 merge.["set ADD SUB DIV MUL ORD toint EQ GT SHR SHL OR AND tan cos sin sqrt GEP"_i
 , abstracttypename.last.paratypes.sym
 ]
else name.sym

______

builtin dlsymbol(cstr)int

Function funcaddress(sym:symbol)int
let name0 = mangledname.sym
let t = if isempty.name0 then 0 else dlsymbol.tocstr.name0
if t > 0 then t
else
 for name = "", ll ∈ loadedLibs
 while isempty.name
 do let l = decoderef.ll
 let idx = findindex(sym, l)
 if idx ≤ length.l then libname.ll + "$$" + toword.idx else name
 /for(assert not.isempty.name report"funcaddress error" + print.sym+stacktrace
 dlsymbol.tocstr.[ merge.name])

Builtin createthreadI(int, int, int, seq.int, int)process.int

Builtin createthreadI(int, int, int, seq.UTF8, int)process.int


Function internalstacktrace seq.word
for acc = "", @e ∈ callstack.30 << 2 do acc + " /br" + printfunc.addresstosymbol2.@e /for(acc)

function printfunc(name:seq.char)seq.word
 if last.name = char1."$"then [ encodeword.name]
else 
 let i = findindex(char1."$", name)
 let library = encodeword.subseq(name, 1, i - 1)
 let idx = toint.encodeword.subseq(name, i + 2, length.name)
 for name2 = "", ll ∈ loadedLibs
 while isempty.name2
 do if first.libname.ll = library then print.(decoderef.ll)_idx else name2
 /for(if isempty.name2 then [ encodeword.name]else name2 /if)

builtin callstack(n:int)seq.int

builtin addresstosymbol2(a:int)seq.char 


____________

Function callentrypoint(arg:UTF8) seq.word
let entry= for acc=empty:seq.symbol,  sym /in decoderef.last.loadedLibs  do
     if not.isconst.sym /and name.sym /in "entrypoint" then acc+sym else acc
     /for(acc)
    if length.entry /ne 1 then "Entry problem"
    else 
    let sym=entry_1
  let t = funcaddress.sym
  let dcret = deepcopySym.resulttype.sym
  let adcret = funcaddress.dcret
    let dc = deepcopySym.seqof.typeword
  let adc = funcaddress.dc
   if not( t > 0  /and adcret > 0 /and adc > 0) then
    "ERROR"+[toword.t,toword.adcret,toword.adc]
  else
    let p = createthreadI(adcret, adc, t, [arg], {buildargcodeI.sym} 4)
    if aborted.p then message.p
   else "OK"
   
   use UTF8
   
   use seq.liblib
   
   use mangle 
   
   use bitcast.UTF8
   
   use bitcast.int
   
   use seq.int
   
   use process.int