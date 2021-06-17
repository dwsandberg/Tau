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

Function libdesc(alltypes:type2dict, p:pro2gram, templates:pro2gram, mods:seq.firstpass, exports:seq.word)symbol
let mods2 = for acc = empty:seq.firstpass, @e = mods do acc + tolibmod(alltypes, p, templates, exports, @e)/for(acc)
let symstoexport = for acc = empty:set.symbol, @e = mods2 do acc ∪ defines.@e /for(acc)
∪ for acc = empty:set.symbol, @e = mods2 do acc ∪ exports.@e /for(acc)
let set2 = asset.for acc = empty:seq.symbol, @e = toseq.symstoexport do acc + tolibsym(p, templates, symstoexport, @e)/for(acc)
let t1 = asset.for acc = empty:seq.symbol, @e = toseq.set2 do acc + zcode.@e /for(acc)
addseq.for acc = empty:seq.symbol, @e = mods2 do acc + addlibmod(set2, @e)/for(acc)

function tolibmod(alltypes:type2dict, p:pro2gram, templates:pro2gram, exports:seq.word, m:firstpass)seq.firstpass
 if  name.module.m ∉ exports then empty:seq.firstpass
 else
  let defines = if isabstract.module.m then defines.m else exports.m
  let types = for acc = empty:seq.myinternaltype, s = toseq.defines do 
  if istype.s then
     let it2=flatwithtype(alltypes, resulttype.s)
      acc
    +   
    myinternaltype(if isabstract.module.m then "undefined"_1
    else "defined"_1, abstracttype.first.it2, module2.first.it2, it2 << 1 ) 
   else acc
  /for(acc)
  let uses = if isabstract.module.m then uses.m else empty:seq.mytype
   [ firstpass(module.m, uses, defines, exports.m, types)]

function tolibsym(p:pro2gram, templates:pro2gram, toexport:set.symbol, sym:symbol)symbol
let code = if isabstract.module.sym then getCode(templates, sym)
else
 let code1 = getCode(p, sym)
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
cleansymbol(sym, code)

----------------------------------

use mytype

use bits

function addlibsym(s:symbol)symbol
 let t=module.s
 Constant2.[ Words.worddata.s, Word.library.t,Word.name.t,addmytype.para.t,   
  addseq.for acc = empty:seq.symbol, @e = types.s do acc + addmytype.@e /for(acc)
 , Lit.toint.raw.s,Lit.extrabits.s  
  ,addseq.for acc = empty:seq.symbol, @e = zcode.s do acc + addlibsym.@e /for(acc)
 , Record.[ typeptr, typeword,typeword, typeptr 
 , typeptr
 , typeint, typeint, typeptr]]

function addmytype(t:mytype)symbol 
 addseq.for acc = empty:seq.symbol, e = typerep.t do
  acc + Constant2.[ Word.name.e, Word.module.e, Word.library.e, Record.[ typeint, typeint, typeint]]
  /for(acc)
 
function addseq(s:seq.symbol)symbol Constant2(s + Sequence(typeptr, length.s))

function addlibmod(toexport:set.symbol, m:firstpass)symbol
 { symbols in m are replaced with the symbol from toexport which has zcode to form programele }
 let exports = toexport ∩ exports.m
 let defines = if isabstract.module.m then toexport ∩ defines.m else exports
 let e = addseq.for acc = empty:seq.symbol, @e = toseq.exports do acc + addlibsym.@e /for(acc)
 let d = if isabstract.module.m then
  addseq.for acc = empty:seq.symbol, @e = toseq.defines do acc + addlibsym.@e /for(acc)
 else e
  let t=module.m
  Constant2.[ Word.library.t, Word.name.t, addmytype.para.t, addseq.for acc = empty:seq.symbol, @e = uses.m do acc + addmytype.@e /for(acc), d, e, Words."", Words."", addseq.for acc = empty:seq.symbol, @e = types.m do acc + addinternaltype.@e /for(acc), Words.""
  , Record.[ typeword, typeword, typeptr, typeptr, typeptr, typeptr, typeptr, typeptr, typeptr, typeptr]]

function addinternaltype(i:myinternaltype)symbol
let t=module.i
 Constant2.[ Word."defined"_1, Word.name.i, Word.library.t,Word.name.t,addmytype.para.t, 
 addseq.for acc = empty:seq.symbol, @e = subflds.i do acc + addmytype.@e /for(acc),
  Record.[ typeint, typeint, typeword,typeword,typeptr, typeptr]]

--------------------------

Export type:liblib

Export type:parc

type liblib is libname:seq.word, words:seq.encodingpair.seq.char, mods:seq.firstpass, timestamp:int, profiledata:seq.parc

type parc is head:word, tail:word, counts:int, clocks:int, space:int, unused:int

Function parc(head:word, tail:word, counts:int, clocks:int, spacex:int)parc parc(head, tail, counts, clocks, spacex, 0)

Export head(parc)word

Export tail(parc)word

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

Export timestamp(liblib)int

Export libname(liblib)seq.word

Export mods(liblib)seq.firstpass

Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

builtin loadedlibs2 seq.liblib

Function loadedLibs seq.liblib loadedlibs2

Function libmodules(dependentlibs:seq.word)seq.firstpass
 for acc = empty:seq.firstpass, @e = loadedLibs do acc + libmodules(dependentlibs, @e)/for(acc)

function libmodules(dependentlibs:seq.word, l:liblib)seq.firstpass
 if(libname.l)_1 ∈ dependentlibs then mods.l else empty:seq.firstpass

Function unloadlib(a:seq.word)int unloadlib.tocstr.a

builtin unloadlib(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[ a]

builtin loadlib(cstr)int 