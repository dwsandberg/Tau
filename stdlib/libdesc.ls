Module libdesc

use encoding.seq.char

use seq.encodingpair.seq.char

use seq.firstpass

use seq.seq.int

use seq.int

use seq.liblib

use seq.myinternaltype

use otherseq.mytype

use seq.mytype

use stdlib

use seq.symbol

use set.symbol

use symbol

use otherseq.word

use seq.seq.word

use seq.word

use set.word

Function libdesc(pin:program, templates:program, mods:seq.firstpass, exports:seq.word, rootsigs:seq.symbol)symbol
 let p = pin ∩ asset.rootsigs
 let closed = @(+, filterbuiltin, empty:seq.symbol, toseq.asset.@(+, exportcode.p, rootsigs, rootsigs))
 let d = @(+, tolibsym(p, templates), empty:seq.symbol, closed)
 let libmods = @(+, tolibmod(p, templates, exports), empty:seq.firstpass, mods)
 + libmod(mytype."$other", d, empty:seq.symbol, empty:seq.mytype)
  addseq.@(+, addlibmod, empty:seq.symbol, libmods)

function filterbuiltin(s:symbol)seq.symbol if isbuiltin.module.s then empty:seq.symbol else [ s]

function tolibmod(p:program, templates:program, exports:seq.word, m:firstpass)seq.firstpass
 if not(abstracttype.modname.m in exports)then empty:seq.firstpass
 else
  let abstract = isabstract.modname.m
  let e = @(+, tolibsym(p, templates), empty:seq.symbol, toseq.exports.m)
  let d = if abstract then @(+, tolibsym(p, templates), empty:seq.symbol, toseq.defines.m)else empty:seq.symbol
   [ libmod(modname.m, d, e, if abstract then uses.m else empty:seq.mytype)]

Function exportcode(p:program, s:symbol)seq.symbol
 let code = code.lookupcode(p, s)
  if length.code < 15 then removeconstant.code else empty:seq.symbol

function tolibsym(p:program, templates:program, sym:symbol)seq.symbol
 if isconstantorspecial.sym then empty:seq.symbol
 else
  let cleansym = [ if isempty.zcode.sym then sym else symbol(fsig.sym, module.sym, returntype.sym)]
  let code = if isabstract.mytype.module.sym then code.lookupcode(templates, sym)else removeconstant.exportcode(p, sym)
   [ symbol(fsig.sym, module.sym, returntype.sym, cleansym + code)]

----------------------------------

function addlibsym(s:symbol)symbol
 Constant2
 .[ Words.fsig.s, Words.module.s, Words.returntype.s, addseq.@(+, addlibsym, empty:seq.symbol, zcode.s), Lit.extrabits.s, Record.[ mytype."ptr", mytype."ptr", mytype."ptr", mytype."ptr", mytype."int"]]

function addmytype(t:mytype)symbol Words.towords.t

function addseq(s:seq.symbol)symbol
 Constant2([ Lit.0, Lit.length.s] + s
 + Record([ mytype."int", mytype."int"] + constantseq(length.s, mytype."ptr")))

function addlibmod(s:firstpass)symbol
 Constant2
 .[ addmytype.modname.s
 , addseq.@(+, addmytype, empty:seq.symbol, uses.s)
 , addseq.@(+, addlibsym, empty:seq.symbol, toseq.defines.s)
 , addseq.@(+, addlibsym, empty:seq.symbol, toseq.exports.s)
 , Words.""
 , Words.""
 , Words.""
 , Record
 .[ mytype."ptr", mytype."ptr", mytype."ptr", mytype."ptr", mytype."ptr", mytype."ptr", mytype."ptr"]]

--------------------------

Export type:liblib

Export type:parc

type liblib is record libname:seq.word, words:seq.encodingpair.seq.char, mods:seq.firstpass, timestamp:int, profiledata:seq.parc

type parc is record head:word, tail:word, counts:int, clocks:int, space:int

Export parc(head:word, tail:word, counts:int, clocks:int, space:int)parc

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

Builtin loadedlibs seq.liblib

Function libmod(modname:mytype, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype)firstpass
 firstpass(modname, uses, asset.defines, asset.exports, empty:seq.symbol, empty:set.symbol, empty:seq.myinternaltype)

function tofirstpass(m:firstpass)seq.firstpass
 [ firstpass(modname.m, uses.m, defines.m, exports.m, empty:seq.symbol, empty:set.symbol, @(+, libtypes, empty:seq.myinternaltype, toseq.defines.m))]

function alllibsym(l:liblib)seq.symbol
 toseq(@(∪, defines, empty:set.symbol, mods.l) ∪ @(∪, exports, empty:set.symbol, mods.l))

Function otherlibsyms(dict:set.symbol, l:seq.liblib)program
 program(asset.@(+, alllibsym, empty:seq.symbol, l) - knownlibsyms.l)

function knownlibsyms(l:liblib)seq.symbol toseq.defines.last.mods.l

function knownlibsyms(l:seq.liblib)set.symbol asset.@(+, knownlibsyms, empty:seq.symbol, l)

function addfirstpass(s:seq.firstpass, l:seq.liblib)seq.firstpass
 if isempty.l then s else s + @(+, tofirstpass, empty:seq.firstpass, mods.l_1)

function addfirstpass(l:liblib)seq.firstpass @(+, tofirstpass, empty:seq.firstpass, mods.l)

Function dependentlibs(dependentlibs:seq.word)seq.liblib @(+, filter(dependentlibs), empty:seq.liblib, loadedlibs)

Function libsymbols(dict:set.symbol, l:seq.liblib)program @(addknown.dict, identity, emptyprogram, l)

function addknown(dict:set.symbol, p:program, l:liblib)program program(toset.p ∪ defines.last.mods.l)

function libtypes(s:symbol)seq.myinternaltype
 if not(returntype.s = "internaltype" ∨ (fsig.s)_1 = "type"_1)then
 empty:seq.myinternaltype
 else
  let code = zcode.s
   assert module.code_2 = "$words"report"NON" + @(+, print,"", code)
   let a = if true ∧ towords.parameter.modname.s in ["T",""]then fsig.code_2
   else replaceT(print.parameter.modname.s, fsig.code_2)
    [ tomyinternaltype.a]

function removeconstant(s:seq.symbol)seq.symbol @(+, removeconstant, empty:seq.symbol, s)

function removeconstant(s:symbol)seq.symbol if module.s = "$constant"then removeconstant.zcode.s else [ s]

Function libfirstpass(l:seq.liblib)seq.firstpass @(+, addfirstpass, empty:seq.firstpass, l)

function filter(s:seq.word, l:liblib)seq.liblib if(libname.l)_1 in s then [ l]else empty:seq.liblib