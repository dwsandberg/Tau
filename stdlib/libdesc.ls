Module libdesc

use fileio

use standard

use symbol

use program

 
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


use seq.encodingpair.seq.char

function print(l:seq.mytype) seq.word for acc="(",t=l do acc+print.t /for(acc+")")

use seq.symbolref

use set.symbolref

use seq.seq.symbolref

Function ?(a:symbolref,b:symbolref) ordering toint.a ? toint.b
  
Function libdesc(info:compileinfo, prg:program) seq.symbol
let symstoexport2=   for  acc=empty:seq.symbolref ,  m=  mods.info do
          acc+  defines.m+exports.m
        /for( for acc2=empty:set.symbol, r=toseq.asset.acc do 
        acc2 +(symbolrefdecode.info)_toint.r
         /for(acc2))
let code2=for  acc=empty:seq.seq.symbolref,        sym=toseq.symstoexport2 do
                  acc+  for acc2=[symbolref.sym],sym2 =
                           if isabstract.module.sym then getCode(prg, sym)
                           else libcode(getCode(prg, sym),symstoexport2)   
                        do 
                        if isFref.sym2 then
                             acc2+ symbolref.PreFref+ symbolref.first.zcode.sym2
                        else
                          acc2+symbolref.sym2
                       /for(acc2)
                /for (acc)
let all=for all=empty:seq.symbolref,a=code2 do all+a /for(asset.all)
        let dd=symbolrefdecode
 for  decoderef = empty:seq.symbol,  r =  toseq.all  do
     let sym=dd_toint.r 
     let lib=if not.isabstract.module.sym /and sym /in symstoexport2 then "compiled"_1 else library.module.sym 
       decoderef +addlibsym(sym, lib)
    /for( 
[ addseq.decoderef  
 ,addseq.for acc = empty:seq.symbol, @e = mods.info do acc + addlibraryMod(@e,all)/for(acc)
 ,{code} for  acc=empty:seq.symbol,       a=code2 do  acc+addseqsymbolref(a,all) /for(addseq.acc)
])

use otherseq.symbolref


Function libcode(code1:seq.symbol,toexport:set.symbol) seq.symbol
let code = removeoptions.code1
 let z = if length.code < 15 then
 let x = removeconstant.code
  if for acc = true, @e = x do
   acc
   ∧ (isconst.@e 
   ∨ (name.module.@e = "builtin"_1 ∧ para.module.@e    ∈ [ typereal, typeint] )
   ∨ isspecial.@e
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

function addlibsym(s:symbol,lib:word)symbol
 assert not.isFref.s report "Fref problem"
  let t=module.s
  Constant2.[ Words.worddata.s, Word.lib,Word.name.t,addmytype.para.t,   
  addseq.for acc = empty:seq.symbol, @e = types.s do acc + addmytype.@e /for(acc)
 , Lit.toint.raw.s,Lit.extrabits.s  
 , Words.""
 , Record.[ typeptr, typeword,typeword, typeptr 
 , typeptr
 , typeint, typeint, typeptr]]

function addmytype(t:mytype)symbol 
 addseq.for acc = empty:seq.symbol, e = typerep.t do
  acc + Constant2.[ Word.name.e, Word.module.e, Word.library.e, Record.[ typeint, typeint, typeint]]
  /for(acc)
 
function addseq(s:seq.symbol)symbol Constant2(s + Sequence(typeptr, length.s))


  
function addseqsymbolref(s:seq.symbolref,all:set.symbolref) symbol
addseq.for acc = empty:seq.symbol, r = s do acc +  Lit.binarysearch(toseq.all,r)  /for(acc)

function addlibraryMod(m:libraryModule,all:set.symbolref)symbol
 let e = addseqsymbolref(exports.m  ,all)
 let d = if isabstract.modname.m then  addseqsymbolref(defines.m  ,all)
 else e
 let t=modname.m
  Constant2.[ Word.library.t, Word.name.t, addmytype.para.t
    , e
    ,{addseq.for acc = empty:seq.symbol, @e = uses.m do acc + addmytype.@e /for(acc)} Words.""
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