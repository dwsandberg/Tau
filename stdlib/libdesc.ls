Module libdesc

use fileio

use standard

use symbol

use pro2gram

use seq.firstpass

use seq.liblib

use seq.myinternaltype

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

use program

use seq.encodingpair.seq.char

function print(l:seq.mytype) seq.word for acc="(",t=l do acc+print.t /for(acc+")")

  
Function libdesc(info:compileinfo, prg:pro2gram) seq.symbol
let symstoexport= asset.symbolrefdecode.info
let set2 = for acc = empty:seq.symbol, sym = symbolrefdecode.info do 
   let code = if isabstract.module.sym then getCode(prg, sym)
            else libcode(getCode(prg, sym),symstoexport)
       acc+addlibsym(cleansymbol(sym, code),symstoexport)
    /for(acc)
[ addseq.set2  
 ,addseq.for acc = empty:seq.symbol, @e = mods.info do acc + addlibraryMod(@e)/for(acc)
]



function libcode(code1:seq.symbol,toexport:set.symbol) seq.symbol
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
  ,addseq.for acc = empty:seq.symbol, @e = zcode.s do acc + addlibsym(@e,toexport) /for(acc)
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

type parc is head:word, tail:word, counts:int, clocks:int, space:int, unused:int

Function parc(head:word, tail:word, counts:int, clocks:int, spacex:int)parc parc(head, tail, counts, clocks, spacex, 0)

Export head(parc)word

Export tail(parc)word

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

Export timestamp(liblib)int

Export decoderef(liblib) seq.symbol

Export newmods(liblib) seq.libraryModule

Export libname(liblib)seq.word

/Export mods(liblib)seq.firstpass

Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

builtin loadedlibs2 seq.liblib

Function loadedLibs seq.liblib loadedlibs2

Function libmodules(dependentlibs:seq.word)seq.firstpass
 for acc = empty:seq.firstpass, l = loadedLibs do acc +
  if(libname.l)_1 ∈ dependentlibs then  acc+cvtnewmods(newmods.l,decoderef.l) 
  else acc
  /for(acc)


Function unloadlib(a:seq.word)int unloadlib.tocstr.a

use seq.libraryModule
  
 
Function  cvtnewmods(ll:seq.libraryModule,decoderef:seq.symbol) seq.firstpass
for acc=empty:seq.firstpass,m=ll  do
   let e=  for acc2=empty:set.symbol,r=exports.m do  acc2+ (decoderef)_toint.r /for(acc2)
   let d= for acc2=empty:set.symbol,r=defines.m do  acc2+ (decoderef)_toint.r /for(acc2)
   let types=  for acc2=empty:seq.myinternaltype, t=types.m do
      acc2+myinternaltype(if isabstract.modname.m then "undefined"_1
    else "defined"_1, abstracttype.first.t, module2.first.t, t << 1 )
      /for(acc2)
         acc+firstpass(modname.m, uses.m, d, e, types)
 /for(acc)

builtin unloadlib(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[ a]

builtin loadlib(cstr)int 