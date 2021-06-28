Module libdesc

use fileio

use standard

use symbol

use pro2gram

 
use seq.liblib


use otherseq.mytype

use set.mytype

use seq.parc

use seq.symbol

use set.symbol

use otherseq.word

use set.word

use encoding.seq.char

use seq.seq.int

use seq.seq.word

/use  program

use seq.encodingpair.seq.char

function print(l:seq.mytype) seq.word for acc="(",t=l do acc+print.t /for(acc+")")

use seq.symbolref

use set.symbolref

function ?(a:symbolref,b:symbolref) ordering toint.a ? toint.b
  
Function libdesc(info:compileinfo, prg:pro2gram) seq.symbol
let symstoexport2=   for  acc=empty:seq.symbolref ,  m=  mods.info do
          acc+  defines.m+exports.m
        /for( for acc2=empty:set.symbol, r=toseq.asset.acc do 
        acc2 +(symbolrefdecode.info)_toint.r
         /for(acc2))
{let symstoexport= asset.symbolrefdecode.info
assert symstoexport2=symstoexport report "NOT SMAE"}
let discard=for    idx=1,sym=symbolrefdecode.info do
  assert toint.symbolref.sym=idx report "lib problem"
   idx+1
  /for(idx)
let code=for  acc=empty:seq.symbol,        sym=toseq.symstoexport2 do
         acc+for refs=empty:seq.symbol, sym2=[sym]+
         if isabstract.module.sym then getCode(prg, sym)
            else libcode(getCode(prg, sym),symstoexport2) do
          refs+Lit.toint.symbolref.sym2 /for(addseq.refs)
        /for(addseq.acc)
 for  decoderef = empty:seq.symbol, sym = symbolrefdecode do 
       decoderef +addlibsym(sym, symstoexport2)
    /for( 
[ addseq.decoderef  
 ,addseq.for acc = empty:seq.symbol, @e = mods.info do acc + addlibraryMod(@e)/for(acc)
 ,code
])



Function libcode(code1:seq.symbol,toexport:set.symbol) seq.symbol
let code = removeoptions.code1
 let z = if length.code < 15 then
 let x = removeconstant.code
  if for acc = true, @e = x do
   acc
   ∧ (isconst.@e 
   ∨ (name.module.@e = "builtin"_1 ∧ para.module.@e    ∈ [ typereal, typeint] )
   ∨ isspecial.@e
   ∨ islocal.@e
   ∨ @e ∈ toexport)
  /for(acc)then
   x
  else empty:seq.symbol
 else empty:seq.symbol
 let optionsx = getoption.code1
  { assert isempty.optionsx ∨ optionsx ∈ ["STATE","INLINE","VERYSIMPLE INLINE","STATE INLINE","BUILTIN","BUILTIN COMPILETIME","PROFILE","STATE BUILTIN","COMPILETIME STATE","COMPILETIME","PROFILE STATE","INLINE STATE","NOINLINE STATE"]report"X"+ optionsx z }
  if"BUILTIN"_1 ∈ optionsx ∨ "COMPILETIME"_1 ∈ optionsx ∨ not.isempty.z then
   z + Words.optionsx + Optionsym
  else z
  
----------------------------------

use mytype

use bits

function addlibsym(s:symbol,toexport:set.symbol)symbol
  let t=module.s
 let lib=if not.isabstract.module.s /and s /in toexport then "compiled"_1 else library.module.s
 Constant2.[ Words.worddata.s, Word.lib,Word.name.t,addmytype.para.t,   
  addseq.for acc = empty:seq.symbol, @e = types.s do acc + addmytype.@e /for(acc)
 , Lit.toint.raw.s,Lit.extrabits.s  
 , if isFref.s then addseq.[addlibsym((zcode.s)_1,toexport)]else Words.""
 , Record.[ typeptr, typeword,typeword, typeptr 
 , typeptr
 , typeint, typeint, typeptr]]

function addmytype(t:mytype)symbol 
 addseq.for acc = empty:seq.symbol, e = typerep.t do
  acc + Constant2.[ Word.name.e, Word.module.e, Word.library.e, Record.[ typeint, typeint, typeint]]
  /for(acc)
 
function addseq(s:seq.symbol)symbol Constant2(s + Sequence(typeptr, length.s))


  
function addlibraryMod(m:libraryModule)symbol
 let e = addseq.for acc = empty:seq.symbol, @e = exports.m do acc + Lit.toint.@e /for(acc)
 let d = if isabstract.modname.m then  addseq.for acc = empty:seq.symbol, @e = defines.m do acc + Lit.toint.@e /for(acc)
 else e
 let t=modname.m
  Constant2.[ Word.library.t, Word.name.t, addmytype.para.t
    , e
    ,addseq.for acc = empty:seq.symbol, @e = uses.m do acc + addmytype.@e /for(acc)
    , d
    , addseq.for acc2=empty:seq.symbol ,tl=types.m do
         acc2+addseq.for acc = empty:seq.symbol, @e = tl do acc + addmytype.@e /for(acc)
       /for(acc2)
  , Record.[ typeword, typeword, typeptr, typeptr, typeptr, typeptr,typeptr]]


--------------------------

Export type:liblib

Export type:parc

type liblib is libname:seq.word, words:seq.encodingpair.seq.char,unused:int, timestamp:int
, profiledata:seq.parc ,decoderef:seq.symbol,newmods:seq.libraryModule
, code:seq.seq.symbolref

type parc is head:word, tail:word, counts:int, clocks:int, space:int, unused:int

Function parc(head:word, tail:word, counts:int, clocks:int, spacex:int)parc parc(head, tail, counts, clocks, spacex, 0)

Export head(parc)word

Export tail(parc)word

Export counts(parc)int

Export code(liblib) seq.seq.symbolref 

Export clocks(parc)int

Export space(parc)int

Export timestamp(liblib)int

Export decoderef(liblib) seq.symbol

Export newmods(liblib) seq.libraryModule

Export libname(liblib)seq.word


Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

builtin loadedlibs2 seq.liblib

Function loadedLibs seq.liblib loadedlibs2



Function unloadlib(a:seq.word)int unloadlib.tocstr.a

use seq.libraryModule
  


builtin unloadlib(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[ a]

builtin loadlib(cstr)int 