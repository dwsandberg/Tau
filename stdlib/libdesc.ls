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

Function libdesc(p:program, templates:program, mods:seq.firstpass, exports:seq.word)symbol
 let mods2=@(+,tolibmod.exports,empty:seq.firstpass,mods)
 let  defs=@(&cup,defines,empty:set.symbol,mods2) 
 let  symstoexport= defs &cup @(&cup,exports,empty:set.symbol,mods2)
  let libmods1 = @(+, tolibmod(p, templates,  symstoexport), empty:seq.firstpass, mods2)
    let dd=toseq.@(&cup,roots,empty:set.symbol,libmods1)
  let libmods=libmods1+ libmod(mytype."$other",   dd, empty:seq.symbol, empty:seq.mytype)
  addseq.@(+, addlibmod, empty:seq.symbol, libmods)

   function   roots(m :firstpass) set.symbol  if isabstract.modname.m  then empty:set.symbol else  exports.m    

Function exportcode(p:program, toexport:set.symbol, s:symbol)seq.symbol
 let code = code.lookupcode(p, s)
  if length.code < 15 then 
   let x=removeconstant.code 
    if @(+,filterx.toexport,0,x) =0 then x else empty:seq.symbol
  else empty:seq.symbol

function tolibmod(p:program, templates:program, toexport:set.symbol,  m:firstpass)firstpass
  let e = @(+, tolibsym(p,templates, toexport), empty:seq.symbol, toseq.exports.m)
  let d =   @(+, tolibsym(p,templates,toexport), empty:seq.symbol, toseq.defines.m) 
    libmod(modname.m, d, e,   uses.m  ) 

function  tolibmod(exports:seq.word,m:firstpass) seq.firstpass
  if not(abstracttype.modname.m in exports) then empty:seq.firstpass
 else
 [ if   isabstract.modname.m  then libmod(modname.m, toseq.defines.m, toseq.exports.m,  uses.m   )
  else libmod(modname.m, empty:seq.symbol, toseq.exports.m,  empty:seq.mytype  )]

   
 
 function filterx(toexport:set.symbol, s:symbol) int 
    if isconst.s then
      if isFref.s then   @(+,filterx.toexport,0,constantcode.s) else 0
    else if  isbuiltin.module.s &or isspecial.s  &or s in toexport then 0
    else 1  

function tolibsym(p:program, templates:program, toexport:set.symbol, sym:symbol)seq.symbol
 if isconstantorspecial.sym then empty:seq.symbol
 else
  let cleansym = [ if isempty.zcode.sym then sym else symbol(fsig.sym, module.sym, returntype.sym)]
  let code = if isabstract.modname.sym then code.lookupcode(templates, sym) else exportcode(p,toexport, sym)  
   [ symbol(fsig.sym, module.sym, returntype.sym, cleansym + code)]

----------------------------------

function addlibsym(s:symbol)symbol
 Constant2
 .[ Words.fsig.s, Words.module.s, Words.returntype.s, addseq.@(+, addlibsym, empty:seq.symbol, zcode.s), Lit.extrabits.s, Record.[ typeptr, typeptr, typeptr, typeptr, typeint]]

function addmytype(t:mytype)symbol Words.typerep.t

function addseq(s:seq.symbol)symbol
 Constant2([ Lit.0, Lit.length.s] + s
 + Record([ typeint, typeint] + constantseq(length.s, typeptr)))

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
 .[ typeptr, typeptr, typeptr, typeptr, typeptr, typeptr, typeptr]]

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
   assert length.code > 1 &and module.code_2 = "$words"report"NON" +print.s+"/"+ @(+, print,"", code)
   let a = if true ∧ typerep.parameter.modname.s in ["T",""]then fsig.code_2
   else replaceT(print.parameter.modname.s, fsig.code_2)
    [ tomyinternaltype.a]

function removeconstant(s:seq.symbol)seq.symbol @(+, removeconstant, empty:seq.symbol, s)

function removeconstant(s:symbol)seq.symbol if module.s = "$constant"then removeconstant.zcode.s else [ s]

Function libfirstpass(l:seq.liblib)seq.firstpass @(+, addfirstpass, empty:seq.firstpass, l)

function filter(s:seq.word, l:liblib)seq.liblib if(libname.l)_1 in s then [ l]else empty:seq.liblib