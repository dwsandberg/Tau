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
 let mods2=@(+,tolibmod(p,templates,exports),empty:seq.firstpass,mods)
 let symstoexport= @(&cup,defines,empty:set.symbol,mods2) &cup @(&cup,exports,empty:set.symbol,mods2)
 let set2=asset.@(+, tolibsym(p,templates, symstoexport), empty:seq.symbol, toseq.symstoexport)
addseq.@(+, addlibmod( set2),empty:seq.symbol,mods2)

/function isinternaltype(s:symbol) set.symbol if (fsig.s)_1="type"_1 &and resulttype.s=mytype."internaltype" then asset.[s]
else empty:set.symbol

function  tolibmod(p:program, templates:program,exports:seq.word,m:firstpass) seq.firstpass
  if not(abstracttype.modname.m in exports) then empty:seq.firstpass
 else
   let defines=if isabstract.modname.m  then  defines.m else exports.m
     let types   =@(+, libtypes2(p,templates), empty:seq.myinternaltype,  toseq.defines)  
   let uses = if isabstract.modname.m  then uses.m else empty:seq.mytype  
   [ firstpass(modname.m, uses,  defines,  exports.m, empty:seq.symbol, empty:set.symbol,empty:seq.myinternaltype)]

   
  function libtypes2(p:program,templates:program,s:symbol)seq.myinternaltype
 if not(returntype.s = "internaltype" ∨ (fsig.s)_1 = "type"_1)then
 empty:seq.myinternaltype
 else
  let code =  if isabstract.modname.s then  code.lookupcode(templates,s) else code.lookupcode(p,s)
    assert length.code > 0 &and module.code_1 = "$words"report"NON2" +print.s+"/"+ @(+, print,"", code)
    let k=tomyinternaltype.fsig.code_1
     [if isabstract.modname.s then
       k
     else 
       if iscomplex.modname.k then  changesubflds(k,@(+,replaceT(parameter.modname.k),empty:seq.mytype,subflds.k))
       else k 
     ]
      
 
function tolibsym(p:program, templates:program, toexport:set.symbol, sym:symbol) symbol
   let cleansym = [ if isempty.zcode.sym then sym else symbol(fsig.sym, module.sym, returntype.sym)]
  let code = if isabstract.modname.sym then code.lookupcode(templates, sym) else
 let code = code.lookupcode(p, sym)
  if length.code < 15 then 
   let x=removeconstant.code 
    if @(+,filterx.toexport,0,x) =0 then x else empty:seq.symbol
  else empty:seq.symbol
       symbol(fsig.sym, module.sym, returntype.sym, cleansym + code) 

function filterx(toexport:set.symbol, s:symbol) int 
    if isconst.s then
      if isFref.s then   @(+,filterx.toexport,0,constantcode.s) else 0
    else if  isbuiltin.module.s &or isspecial.s  &or s in toexport then 0
    else 1  

----------------------------------

function addlibsym(s:symbol)symbol
 Constant2
 .[ Words.fsig.s, Words.module.s, Words.returntype.s, addseq.@(+, addlibsym, empty:seq.symbol, zcode.s), Lit.extrabits.s, Record.[ typeptr, typeptr, typeptr, typeptr, typeint]]

function addmytype(t:mytype)symbol Words.typerep.t

function addseq(s:seq.symbol)symbol
 Constant2([ Lit.0, Lit.length.s] + s
 + Record([ typeint, typeint] + constantseq(length.s, typeptr)))
 
 function addlibmod( toexport:set.symbol,  m:firstpass) symbol
 // symbols in m are replaced with the symbol from toexport which has zcode to form programele // 
 let exports=  toexport &cap exports.m 
 let defines= if isabstract.modname.m then  toexport &cap defines.m  else exports
 let types=@(+, libtypes, empty:seq.myinternaltype, toseq.defines)
// let a=@(seperator.";",towords,"",types) 
 let b=@(seperator.";",towords,"",types.m) 
assert a=b &or subseq(a,1,3)="record UTF8 UTF8" report "DIFF"+a+"&br"+b //
  let e= addseq.@(+, addlibsym, empty:seq.symbol, toseq.exports )
 let d= if isabstract.modname.m then  addseq.@(+, addlibsym, empty:seq.symbol, toseq.defines )  else e
 Constant2
 .[ addmytype.modname.m 
 , addseq.@(+, addmytype, empty:seq.symbol, uses.m )
 , d
 , e
 , Words.""
 , Words.""
 , addseq.@(+, addinternaltype, empty:seq.symbol, types)
 , Words.""
 , Record
 .[ typeptr, typeptr, typeptr, typeptr, typeptr, typeptr, typeptr, typeptr]]
 
function addinternaltype(t:myinternaltype) symbol
Constant2.[ Word.kind.t,Word.name.t,addmytype.modname.t
 ,addseq.@(+, addmytype, empty:seq.symbol, subflds.t)
, Record
 .[ typeint,typeint, typeptr, typeptr ]]
 
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


Function libmodules(dependentlibs:seq.word)seq.firstpass @(+, libmodules(dependentlibs), empty:seq.firstpass, loadedlibs)
 
function libmodules(dependentlibs:seq.word, l:liblib) seq.firstpass if(libname.l)_1 in dependentlibs then mods.l else empty:seq.firstpass

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


