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

Function mangledname(options:seq.word, s:symbol)word
if wordname.s ∈ "main" ∧ name.module.s ∈ "main2"then"main2"_1
else if wordname.s ∈ "addlibrarywords" ∧ name.module.s ∈ "main2"then
"addlibrarywordsZmain2Zliblib"_1
else if name.module.s ∈ "internal"then extname.s else first.externalname.options

function externalname(options:seq.word)seq.word
toseq(asset.options \ asset."COMPILETIME NOINLINE INLINE PROFILE STATE VERYSIMPLE")

Function extname(sym:symbol)word
let name1 ="set +-/ * ? toint = > >> << ∨ ∧ tan cos sin sqrt GEP"
let i = findindex(name.sym, name1)
if i ≤ length.name1 then
 merge.["set ADD SUB DIV MUL ORD toint EQ GT SHR SHL OR AND tan cos sin sqrt GEP"_i
 , abstracttypename.last.paratypes.sym
 ]
else name.sym

______

builtin dlsymbol(cstr)int

Function funcaddress(sym:symbol)int
let name0 =
 if wordname.sym ∈ "main" ∧ name.module.sym ∈ "main2"then"main2"
 else if wordname.sym ∈ "addlibrarywords" ∧ name.module.sym ∈ "main2"then
 "addlibrarywordsZmain2Zliblib"
 else if name.module.sym ∈ "internal"then [ extname.sym]else""
let t = if isempty.name0 then 0 else dlsymbol.tocstr.name0
if t > 0 then t
else
 for name ="", ll ∈ loadedLibs
 while isempty.name
 do let l = decoderef.ll
 let idx = findindex(sym, l)
 if idx ≤ length.l then libname.ll + "$$" + toword.idx else name
 /for(assert not.isempty.name report"funcaddress error" + print.sym
 dlsymbol.tocstr.[ merge.name])

Builtin createthreadI(int, int, int, seq.int, int)process.int

Function internalstacktrace seq.word
for acc ="", @e ∈ callstack.30 << 2 do acc + " /br" + printfunc.addresstosymbol2.@e /for(acc)

function printfunc(name:seq.char)seq.word
if last.name = char1."$"then [ encodeword.name]
else
 let i = findindex(char1."$", name)
 let library = encodeword.subseq(name, 1, i - 1)
 let idx = toint.encodeword.subseq(name, i + 2, length.name)
 for name2 ="", ll ∈ loadedLibs
 while isempty.name2
 do if first.libname.ll = library then print.(decoderef.ll)_idx else name2
 /for(if isempty.name2 then [ encodeword.name]else name2 /if)

builtin callstack(n:int)seq.int

builtin addresstosymbol2(a:int)seq.char 