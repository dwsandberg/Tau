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

Function libdesc(alltypes:typedict,p:program, templates:program, mods:seq.firstpass, exports:seq.word)symbol
 let mods2=@(+,tolibmod(alltypes,p,templates,exports),empty:seq.firstpass,mods)
 let symstoexport= @(&cup,defines,empty:set.symbol,mods2) &cup @(&cup,exports,empty:set.symbol,mods2)
 let set2=asset.@(+, tolibsym(p,templates, symstoexport), empty:seq.symbol, toseq.symstoexport)
addseq.@(+, addlibmod( set2),empty:seq.symbol,mods2)


function  tolibmod(alltypes:typedict,p:program, templates:program,exports:seq.word,m:firstpass) seq.firstpass
  if not(abstracttype.modname.m in exports) then empty:seq.firstpass
 else
   let defines=if isabstract.modname.m  then  defines.m else exports.m
    let types   =@(+, libtypes2(alltypes,p,templates), empty:seq.myinternaltype,  toseq.defines)  
   let uses = if isabstract.modname.m  then uses.m else empty:seq.mytype  
   [ firstpass(modname.m, uses,  defines,  exports.m, empty:seq.symbol, empty:set.symbol,types)]


function  printtotype(a:seq.word,i:int, result:seq.word) mytype
  if isempty.result then printtotype(a,i+1,result+a_i)
  else if i > length.a then mytype.result
  else       printtotype(a,i+2,[a_(i+1)]+result)
   
use set.mytype

  
   
function libtypes2(alltypes:typedict,p:program,templates:program,s:symbol)seq.myinternaltype
 if istypeexport.s   then 
      let it=findelement(alltypes,resulttype.s)_1  
  [   if  isabstract.modname.it then 
    myinternaltype("undefined"_1,name.it,modname.it,subflds.it) 
   else it]
 else  empty:seq.myinternaltype
    
        
 
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
 .[ Words.fsig.s, Words.module.s, Words.returntype.s, addseq.@(+, addlibsym, empty:seq.symbol, zcode.s), Lit.extrabits.s
 , Record."ptr ptr ptr ptr ptr"]

function addmytype(t:mytype)symbol Words.typerep.t

function addseq(s:seq.symbol)symbol
 Constant2([ Lit.0, Lit.length.s] + s
 + Record("int,int" + constantseq(length.s, "ptr"_1)))
 
 function addlibmod( toexport:set.symbol,  m:firstpass) symbol
 // symbols in m are replaced with the symbol from toexport which has zcode to form programele // 
 let exports=  toexport &cap exports.m 
 let defines= if isabstract.modname.m then  toexport &cap defines.m  else exports
   let e= addseq.@(+, addlibsym, empty:seq.symbol, toseq.exports )
 let d= if isabstract.modname.m then  addseq.@(+, addlibsym, empty:seq.symbol, toseq.defines )  else e
 Constant2
 .[ addmytype.modname.m 
 , addseq.@(+, addmytype, empty:seq.symbol, uses.m )
 , d
 , e
 , Words.""
 , Words.""
 , addseq.@(+, addinternaltype, empty:seq.symbol, types.m)
 , Words.""
 , Record."ptr ptr ptr ptr ptr ptr ptr ptr"]
  
function addinternaltype(t:myinternaltype) symbol
Constant2.[ Word.kind.t,Word.name.t,addmytype.modname.t
 ,addseq.@(+, addmytype, empty:seq.symbol, subflds.t)
, Record."int int ptr ptr"]
  
--------------------------

Export type:liblib

Export type:parc

use process.parc

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

function removeconstant(s:seq.symbol)seq.symbol @(+, removeconstant, empty:seq.symbol, s)

function removeconstant(s:symbol)seq.symbol if module.s = "$constant"then removeconstant.zcode.s else [ s]

use process.seq.parc

Export deepcopy(seq.parc) seq.parc

