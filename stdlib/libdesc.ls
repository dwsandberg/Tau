Module libdesc

use encoding.seq.char

use seq.encodingpair.seq.char

use seq.firstpass

use seq.seq.int


use seq.liblib

use seq.myinternaltype

use otherseq.mytype

use set.mytype

use process.parc

use standard

use seq.symbol

use set.symbol

use symbol

use otherseq.word

use seq.seq.word


use set.word

Function libdesc(alltypes:typedict, p:program, templates:program, mods:seq.firstpass, exports:seq.word)symbol
 let mods2 = mods @ +(empty:seq.firstpass, tolibmod(alltypes, p, templates, exports, @e))
 let symstoexport = mods2 @ ∪(empty:set.symbol, defines.@e)
 ∪ (mods2 @ ∪(empty:set.symbol, exports.@e))
  let set2 = asset(toseq.symstoexport @ +(empty:seq.symbol, tolibsym(p, templates, symstoexport, @e)))
  let t1=  asset(  toseq.set2 @ +(empty:seq.symbol,zcode.@e)) 
 // assert false report "libsymbols"+ toseq.t1  @+("", if isconst.@e &or islocal.@e &or isspecial.@e 
  &or @e &in set2 
  &or  (fsig.@e )_1 &in "apply3" then "" else EOL+ print.@e) //
 // assert symbol("false","standard","boolean") &in set2 report "missing false" //
 addseq(mods2 @ +(empty:seq.symbol, addlibmod(set2, @e)))

function tolibmod(alltypes:typedict, p:program, templates:program, exports:seq.word, m:firstpass)seq.firstpass
 if not(abstracttype.modname.m ∈ exports)then empty:seq.firstpass
 else
  let defines = if isabstract.modname.m then defines.m else exports.m
  let types = toseq.defines @ +(empty:seq.myinternaltype, libtypes2(alltypes, p, templates, @e))
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
  let code = code.lookupcode(p, sym)
   if length.code < 15 then
     let x = removeconstant.code
     if  x @ &and(true,   isconst.@e ∨     module.@e &in [ " int builtin", "real builtin"] ∨ isspecial.@e  ∨ islocal.@e 
     ∨  @e &in toexport)   then x 
     else  
      empty:seq.symbol  
   else empty:seq.symbol
   symbol(fsig.sym, module.sym, returntype.sym, cleansym + code)
  
----------------------------------

function addlibsym(s:symbol)symbol
 Constant2
 .[ Words.fsig.s, Words.module.s, Words.returntype.s, addseq(zcode.s @ +(empty:seq.symbol, addlibsym.@e)), Lit.extrabits.s, Record."ptr ptr ptr ptr ptr"]

function addmytype(t:mytype)symbol Words.typerep.t

function addseq(s:seq.symbol)symbol
 Constant2([ Stdseq, Lit.length.s] + s
 + Record("int, int" + constantseq(length.s,"ptr"_1)))

function addlibmod(toexport:set.symbol, m:firstpass)symbol
 // symbols in m are replaced with the symbol from toexport which has zcode to form programele //
 let exports = toexport ∩ exports.m
  // assert not(modname.m=mytype."standard") report "HHH"+print.modname.m+toseq.exports @ +("",print.@e)
// let defines = if isabstract.modname.m then toexport ∩ defines.m else exports
 let e = addseq(toseq.exports @ +(empty:seq.symbol, addlibsym.@e))
 let d = if isabstract.modname.m then addseq(toseq.defines @ +(empty:seq.symbol, addlibsym.@e))else e
  Constant2
  .[ addmytype.modname.m, addseq(uses.m @ +(empty:seq.symbol, addmytype.@e)), d, e, Words."", Words."", addseq(types.m @ +(empty:seq.symbol, addinternaltype.@e)), Words."", Record."ptr ptr ptr ptr ptr ptr ptr ptr"]

function addinternaltype(t:myinternaltype)symbol
 Constant2
 .[ Word.kind.t, Word.name.t, addmytype.modname.t, addseq(subflds.t @ +(empty:seq.symbol, addmytype.@e)), Record."int int ptr ptr"]

--------------------------

Export type:liblib

Export type:parc

type liblib is record libname:seq.word, words:seq.encodingpair.seq.char, mods:seq.firstpass, timestamp:int, profiledata:seq.parc

type parc is record head:word, tail:word, counts:int, clocks:int, space:int, unused:int


Function parc(head:word, tail:word, counts:int, clocks:int, spacex:int )parc
  parc(head,tail,counts,clocks,spacex,0)

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

Function libmodules(dependentlibs:seq.word)seq.firstpass loadedLibs @ +(empty:seq.firstpass, libmodules(dependentlibs, @e))

function libmodules(dependentlibs:seq.word, l:liblib)seq.firstpass if(libname.l)_1 ∈ dependentlibs then mods.l else empty:seq.firstpass

Function unloadlib(a:seq.word)int unloadlib.tocstr.a

builtin unloadlib(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[ a]

builtin loadlib(cstr)int

use fileio