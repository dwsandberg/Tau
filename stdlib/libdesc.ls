Module libdesc

use fileio

use standard

use symbol

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

use seq.encodingpair.seq.char

Function libdesc(alltypes:typedict, p:program, templates:program, mods:seq.firstpass, exports:seq.word)symbol
 let mods2 = for @e ∈ mods, acc = empty:seq.firstpass ; acc + tolibmod(alltypes, p, templates, exports, @e)
 let symstoexport = for @e ∈ mods2, acc = empty:set.symbol ; acc ∪ defines.@e ;
 ∪ for @e ∈ mods2, acc = empty:set.symbol ; acc ∪ exports.@e
 let set2 = asset.for @e ∈ toseq.symstoexport, acc = empty:seq.symbol ; acc + tolibsym(p, templates, symstoexport, @e)
 let t1 = asset.for @e ∈ toseq.set2, acc = empty:seq.symbol ; acc + zcode.@e
  addseq.for @e ∈ mods2, acc = empty:seq.symbol ; acc + addlibmod(set2, @e)

function tolibmod(alltypes:typedict, p:program, templates:program, exports:seq.word, m:firstpass)seq.firstpass
 if not(abstracttype.modname.m ∈ exports)then empty:seq.firstpass
 else
  let defines = if isabstract.modname.m then defines.m else exports.m
  let types = for @e ∈ toseq.defines, acc = empty:seq.myinternaltype ; acc + libtypes2(alltypes, p, templates, @e)
  let uses = if isabstract.modname.m then uses.m else empty:seq.mytype
   [ firstpass(modname.m, uses, defines, exports.m, empty:seq.symbol, empty:set.symbol, types)]

function printtotype(a:seq.word, i:int, result:seq.word)mytype
 if isempty.result then printtotype(a, i + 1, result + a_i)
 else if i > length.a then mytype.result
 else printtotype(a, i + 2, [ a_(i + 1)] + result)

function libtypes2(alltypes:typedict, p:program, templates:program, s:symbol)seq.myinternaltype
 if istypeexport.s then
 let it = findelement(alltypes, resulttype.s)_1
   [ if isabstract.modname.it then myinternaltype("undefined"_1, name.it, modname.it, subflds.it)else it]
 else empty:seq.myinternaltype

function tolibsym(p:program, templates:program, toexport:set.symbol, sym:symbol)symbol
 let cleansym = [ if isempty.zcode.sym then sym else symbol(fsig.sym, module.sym, returntype.sym)]
 let code = if isabstract.modname.sym then code.lookupcode(templates, sym)
 else
  let code1 = code.lookupcode(p, sym)
  let code = removeoptions.code1
  let z = if length.code < 15 then
  let x = removeconstant.code
    if for @e ∈ x, acc = true ; acc
    ∧ (isconst.@e ∨ module.@e ∈ ["int builtin","real builtin"] ∨ isspecial.@e
    ∨ islocal.@e
    ∨ @e ∈ toexport)then
    x
    else empty:seq.symbol
  else empty:seq.symbol
  let optionsx = getoption.code1
   \\ assert isempty.optionsx &or optionsx &in ["STATE","INLINE","VERYSIMPLE INLINE","STATE INLINE","BUILTIN","BUILTIN COMPILETIME","PROFILE","STATE BUILTIN","COMPILETIME STATE","COMPILETIME","PROFILE STATE","INLINE STATE","NOINLINE STATE"]report"X"+ optionsx z \\
   if"BUILTIN"_1 ∈ optionsx ∨ "COMPILETIME"_1 ∈ optionsx ∨ not.isempty.z then
   z + Words.optionsx + Optionsym
   else z
  symbol(fsig.sym, module.sym, returntype.sym, cleansym + code)

----------------------------------

function addlibsym(s:symbol)symbol
 Constant2.[ Words.fsig.s, Words.module.s, Words.returntype.s, addseq.for @e ∈ zcode.s, acc = empty:seq.symbol ; acc + addlibsym.@e, Lit.extrabits.s, Record.[ typeptr, typeptr, typeptr, typeptr, typeptr]]

function addmytype(t:mytype)symbol Words.typerep.t

function addseq(s:seq.symbol)symbol Constant2(s + Sequence(mytype."ptr", length.s))

function addlibmod(toexport:set.symbol, m:firstpass)symbol
 \\ symbols in m are replaced with the symbol from toexport which has zcode to form programele \\
 let exports = toexport ∩ exports.m
  \\ assert not(modname.m = mytype."standard")report"HHH"+ print.modname.m + toseq.exports @ +("", print.@e)\\
  let defines = if isabstract.modname.m then toexport ∩ defines.m else exports
  let e = addseq.for @e ∈ toseq.exports, acc = empty:seq.symbol ; acc + addlibsym.@e
  let d = if isabstract.modname.m then addseq.for @e ∈ toseq.defines, acc = empty:seq.symbol ; acc + addlibsym.@e
  else e
   Constant2.[ addmytype.modname.m, addseq.for @e ∈ uses.m, acc = empty:seq.symbol ; acc + addmytype.@e, d, e, Words."", Words."", addseq.for @e ∈ types.m, acc = empty:seq.symbol ; acc + addinternaltype.@e, Words."", Record.[ typeptr, typeptr, typeptr, typeptr, typeptr, typeptr, typeptr, typeptr]]

function addinternaltype(t:myinternaltype)symbol
 Constant2.[ Word.kind.t, Word.name.t, addmytype.modname.t, addseq.for @e ∈ subflds.t, acc = empty:seq.symbol ; acc + addmytype.@e, Record.[ typeint, typeint, typeptr, typeptr]]

--------------------------

Export type:liblib

Export type:parc

type liblib is record libname:seq.word, words:seq.encodingpair.seq.char, mods:seq.firstpass, timestamp:int, profiledata:seq.parc

type parc is record head:word, tail:word, counts:int, clocks:int, space:int, unused:int

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

Function libmodules(dependentlibs:seq.word)seq.firstpass for @e ∈ loadedLibs, acc = empty:seq.firstpass ; acc + libmodules(dependentlibs, @e)

function libmodules(dependentlibs:seq.word, l:liblib)seq.firstpass if(libname.l)_1 ∈ dependentlibs then mods.l else empty:seq.firstpass

Function unloadlib(a:seq.word)int unloadlib.tocstr.a

builtin unloadlib(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[ a]

builtin loadlib(cstr)int