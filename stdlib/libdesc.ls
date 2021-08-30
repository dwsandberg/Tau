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

type libdescresult is liblibflds:seq.symbol
      ,profilearcs:set.seq.symbol,newmap:set.symbolref,profiledata:seq.int
      
Export profilearcs(libdescresult) set.seq.symbol

Export liblibflds(libdescresult) seq.symbol


Export profiledata(libdescresult )seq.int

Export type:libdescresult

use seq.parc

use set.seq.symbol

use seq.seq.symbol

use otherseq.symbol
              
   
  
Function libdesc(info:compileinfo, prg:program ) libdescresult
{ mods.info are only the exported modules }
let symstoexport2={roots.info}   for  acc=empty:seq.symbolref ,  m=  mods.info do
          acc+  exports.m
        /for( for acc2=empty:set.symbol, r=toseq.asset.acc do 
        acc2 +(symbolrefdecode.info)_toint.r
         /for(acc2))
let code2=for  acc=empty:seq.seq.symbolref,        sym=toseq.symstoexport2 do
            { assert not(isInternal.sym /and name.sym /in ">>" )report "KKK"+print.sym +"C"+print.getCode(prg, sym)
             }               let ref=symbolref.sym
                        acc+  for acc2=[ref],sym2 =
                           if isabstract.module.sym then getCode(prg, sym)
                           else libcode( getCode(prg, sym) ,symstoexport2)   
                        do 
                        if isFref.sym2 then
                             acc2+ symbolref.PreFref+ symbolref.basesym.sym2
                        else
                          acc2+symbolref.sym2
                       /for(acc2)
                /for (acc)
let profilearcs=for acc=empty:set.seq.symbol , sd=tosymdefs.prg do 
           if  "PROFILE"_1 /nin getoption.code.sd then acc
           else 
        for txt=acc ,sym =toseq.asset.code.sd  do 
          if isconstantorspecial.sym /or isInternal.sym then txt 
          else txt+ [sym.sd, sym ] 
        /for(txt)
        /for(acc)
let all0=for acc=empty:seq.symbolref ,arc=toseq.profilearcs do acc+symbolref.arc_1+symbolref.arc_2 /for(acc)     
let all=for all=all0,a=code2 do all+a /for(asset.all)
{ all is used to establish new mapping of symbols to symbolrefs}
let profiledata = for acc = [  1,  cardinality.profilearcs], arc = toseq.profilearcs do
 acc + [   binarysearch(toseq.all,symbolref.arc_1) , binarysearch(toseq.all,symbolref.arc_2), 0, 0, 0, 0]
/for(acc)
let dd=symbolrefdecode
   for  decoderef = empty:seq.symbol, idx= toseq.all     do
        decoderef +addlibsym(dd_toint.idx)
    /for( libdescresult( [
  addseq.decoderef  
 ,addseq.for acc = empty:seq.symbol, @e = mods.info do acc + addlibraryMod(@e,all)/for(acc)
 ,{code} for  acc=empty:seq.symbol, a=code2 do  acc+addseqsymbolref(a,all) /for( addseq.acc)
 ],profilearcs,all,profiledata)
 )

use otherseq.symbolref

use set.int

Function libcode(code1:seq.symbol,toexport:set.symbol) seq.symbol
let code = removeoptions.code1
 let z = if length.code < 15 then
 let x = removeconstantcode.code
  if for acc = true, @e = x do
   acc
   ∧ (isconst.@e 
   ∨ ( isBuiltin.@e   ∧ para.module.@e    ∈ [ typereal, typeint] )
   ∨ isspecial.@e
    ∨ @e ∈ toexport)
  /for(acc)then
   x
  else empty:seq.symbol
 else empty:seq.symbol
 let optionsx = getoption.code1
  { assert isempty.optionsx ∨ optionsx ∈ ["STATE","INLINE","VERYSIMPLE INLINE","STATE INLINE","BUILTIN","BUILTIN COMPILETIME","PROFILE","STATE BUILTIN","COMPILETIME STATE","COMPILETIME","PROFILE STATE","INLINE STATE","NOINLINE STATE"]report"X"+ optionsx z }
  if "COMPILETIME"_1 ∈ optionsx ∨ not.isempty.z then
   z + Words.optionsx + Optionsym
  else z
  
----------------------------------

use mytype

use bits

function addlibsym(s:symbol )symbol
 assert not.isFref.s report "Fref problem" +stacktrace
  let t=module.s
  Constant2.[ Words.worddata.s, Word.library.t,Word.name.t,addmytype.para.t,   
  addseq.for acc = empty:seq.symbol, @e = types.s do acc + addmytype.@e /for(acc)
 , Lit.toint.raw.s,Lit.extrabits.s  
 , Record.[ typeptr, typeword,typeword, typeptr 
 , typeptr
 , typeint, typeint]]

function addmytype(t:mytype)symbol 
 addseq.for acc = empty:seq.symbol, e = typerep.t do
  acc + Constant2.[ Word.name.e, Word.module.e, Word.library.e, Record.[ typeint, typeint, typeint]]
  /for(acc)
 
function addseq(s:seq.symbol)symbol Constant2(s + Sequence(typeptr, length.s))


  
function addseqsymbolref(s:seq.symbolref,all:set.symbolref) symbol
addseq.for acc = empty:seq.symbol, r = s do acc +  Lit.binarysearch(toseq.all,r)  /for(acc)

function addlibraryMod(m:libraryModule,all:set.symbolref)symbol
 let e = addseqsymbolref(exports.m  ,all)
 let types=addseq.for acc2=empty:seq.symbol ,tl=types.m do
         acc2+addseq.for acc = empty:seq.symbol, @e = tl do acc + addmytype.@e /for(acc)
       /for(acc2)
 let t=modname.m
  Constant2.[ Word.library.t, Word.name.t, addmytype.para.t
    , e
    , types
  , Record.[ typeword, typeword, typeptr, typeptr, typeptr]]


--------------------------

Export type:liblib

Export type:parc

type liblib is libname:seq.word, words:seq.encodingpair.seq.char,unused:int, timestamp:int
, profiledata:seq.parc ,decoderef:seq.symbol,newmods:seq.libraryModule
, code:seq.seq.symbolref

type parc is caller:symbolref, callee:symbolref, counts:int, clocks:int, 
space:int, unused:int

 
Function parc(caller:symbol, callee:symbol)parc 
parc(symbolref.caller, symbolref.callee, 0,0, 0, 0)



Function =(a:parc,b:parc)boolean toint.callee.a=toint.callee.b /and toint.caller.a=toint.caller.b

Export caller(parc) symbolref

Export callee(parc) symbolref

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

Function unloadlib(a:seq.word)int unloadlib2.tocstr.a

use seq.libraryModule
  
builtin unloadlib2(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[ a]

builtin loadlib(cstr)int 