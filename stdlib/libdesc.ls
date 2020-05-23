

Module libdesc

use stdlib

use symbol

use seq.firstpass

use seq.fsignrep


use seq.seq.int

use intercode

use libscope

use seq.seq.word

use seq.word

use seq.symbol

use set.symbol

use set.word

use seq.int

use seq.libsym

use worddict.libsym

use otherseq.libsym


use funcsig

Function libdesc(p:prg,intercode:intercode, mods:seq.firstpass, known:symbolset)seq.libmod
  let mods2=@(+,cleansimple.known,empty:seq.firstpass,mods) 
  let abstract=@(+,abstractmods(known),empty:seq.libmod,mods)
   let rootsigs=@(+,tosig,empty:seq.sig,toseq.getroots(mods2)) 
  let closed=toexport(p,empty:set.sig,asset.rootsigs)   
      let d=@(+,tolibsym(p,known),empty:seq.libsym,toseq.closed )    
    let z=@(add,identity,emptyworddict:worddict.libsym,d) 
     @(+,libmod(z),abstract,mods2)
+ libmod(false,"$other"_1, sort.d, empty:seq.libsym, empty:seq.mytype)



function  abstractmods( known:symbolset,f:firstpass) seq.libmod
  if not.exportmodule.f &or not.isabstract.modname.f then empty:seq.libmod
  else  
    let d=sort.@(+,aslibsym.known,empty:seq.libsym,toseq.defines.f)
    let e=sort.@(+,aslibsym.known,empty:seq.libsym,toseq.exports.f)
    [libmod(true, abstracttype.modname.f,d,e, uses.f)]
    
function aslibsym(known:symbolset,sym1:symbol) libsym  
let sym2=lookupsymbol(known,mangledname.sym1)
let sym=if isdefined.sym2 then sym2 else 
assert src.sym1="STUB" report print2.sym1 sym1
libsym(resulttype.sym,mangledname.sym,stripparsedfunc.src.sym )
     
function stripparsedfunc(src:seq.word) seq.word
if length.src > 0 ∧ (src)_1 = "parsedfunc"_1 then
         subseq(src ,toint.(src)_2 + 3, length.src) else src
      
use set.sig

function   toexport(p:prg,processed:set.sig, toprocess:set.sig) set.sig
   if isempty.toprocess then 
     // asset.@(+,filterFref,empty:seq.sig,toseq.processed) // processed else 
    let q= asset.@(+,exportcode.p,empty:seq.sig,     toseq.toprocess)
      toexport(p,processed &cup toprocess, q-processed)

function filterFref(s:sig) seq.sig
  if s=IDXUC then empty:seq.sig else 
 if isconst.s then 
  let rep=decode.s 
   if module.rep="$fref" then 
   // assert not(fsig.rep="FREF Q5FZllvmtypezotherseqZTzcseqZint") report fsig.rep+toword.length.code.rep //
   empty:seq.sig
   else [s]
   else [s   ]
   
 use seq.sig
  
function find4(p:prg, known:symbolset, mangledname:word) libsym 
   tolibsym(p,lookupsymbol(known,mangledname) )
    
     
function cleansym(known:symbolset,s:symbol) symbol 
      let sym2=lookupsymbol(known,mangledname.s) 
      if isdefined.sym2 then sym2 else s
     
function cleansimple(a:symbolset,m:firstpass)  seq.firstpass
    if not.exportmodule.m &or isabstract.modname.m then empty:seq.firstpass else  
 [ firstpass(  modname.m  , uses.m,     empty:set.symbol  , 
 @(+, cleansym.a, empty:set.symbol, toseq.exports.m), empty:seq.symbol, empty:set.symbol, exportmodule.m  )]


 
  
function find(t:worddict.libsym,s:symbol) seq.libsym lookup(t,mangledname.s)

function libmod (t:worddict.libsym, f:firstpass) seq.libmod
     if not.exportmodule.f &or isabstract.modname.f then empty:seq.libmod
     else  
       let e=sort.@(+,find(t),empty:seq.libsym,toseq.exports.f)
       assert length.e=cardinality.exports.f report "DIFF libmods"
      [libmod(false, abstracttype.modname.f,empty:seq.libsym,e, empty:seq.mytype)]
    
use seq.libmod

use seq.mytype

function add(t:worddict.libsym,l:libsym) worddict.libsym  add(t,fsig.l,l) 
  

function astext(p:prg,s:sig)seq.word
 let rep= lookuprep(p,s)
 let f = towords2x.rep
  if f_1 = "CONSTANT"_1 then   astext5(p,cleancode.rep)+"RECORD"+toword.length.cleancode.rep
   else if f_1 in "SET WORD WORDS LOCAL LIT  RECORD FREF EXITBLOCK BR BLOCK DEFINE"then f else [ f_1]

function astext5(p:prg, d:seq.sig)seq.word @(+, astext(p),"", d)

 
         
 use seq.char       

function tolibsym(p:prg,sym:symbol) libsym
 let s=   tosig.sym      
 let   rep=lookuprep(p,s)
 let t=astext5(p,exportcode.rep) 
         libsym(resulttype.sym, mangledname.sym,t)
         
    

function tolibsym(p:prg,known:symbolset,s:sig ) seq.libsym
  let rep=lookuprep(p,s)
  if module.rep in ["$","$constant","$int","local","$word","$words","$fref"] 
   &or fsig.rep="getinstance(T erecord)" &or s=IDXUC then empty:seq.libsym else
  let sym=lookupsymbol(known,mangledname.rep)
  assert isdefined.sym report "U"+print.[s]
   let t=astext5(p,exportcode.rep) 
        [ libsym(resulttype.sym,mangledname.sym,t)]

----------------------------------

function addlibsym(s:libsym) sig
      constant.[wordsig.fsig.s  ,wordssig.returntype.s ,wordssig.instruction.s]
     


function addmytype(t:mytype) sig  wordssig.(towords.t)

use seq.mytype

function addseq(s:seq.sig) sig  
constant.([ lit.0, lit.length.s ]+s )

 
function addlibmod(s:libmod) sig 
    constant.[lit.if parameterized.s then 1 else 0
     ,wordsig.modname.s
     ,addseq.@(+,addlibsym,empty:seq.sig,defines.s)
      ,addseq.@(+,addlibsym,empty:seq.sig,exports.s)
    ,addseq.@(+,addmytype,empty:seq.sig,uses.s)]

Function addlibmods(s:seq.libmod,i:intercode) intercode
    let last=addseq.@(+,addlibmod,empty:seq.sig,s)
     addtointercode(i)

_______________________________      
     
   
   function tosymbol(ls:libsym)symbol
 let d = codedown.fsig.ls
 assert length.d > 1 report "tosymbol2"+fsig.ls
 symbol(d_1_1,mytype.d_2,@(+, mytype, empty:seq.mytype, subseq(d, 3, length.d)),mytype.returntype.ls,instruction.ls)
 
function tofirstpass(m:libmod)  firstpass
  firstpass(mytype.if parameterized.m then"T" + modname.m else [ modname.m], uses.m, 
 @(+, tosymbol, empty:set.symbol, defines.m), 
 @(+, tosymbol, empty:set.symbol, exports.m), empty:seq.symbol, empty:set.symbol, false )
 
function addknown(a:symbolset,l:seq.liblib) symbolset   
 if isempty.l then a else @(+, tosymbol, a, defines.last.mods.l_1)


function addfirstpass(s:seq.firstpass,l:seq.liblib) seq.firstpass  
 if isempty.l then s else  s+@(+, tofirstpass, empty:seq.firstpass, mods.l_1)

Function libknown(dependentlibs:seq.word) symbolset 
  @(addknown, filter(dependentlibs),emptysymbolset   , loadedlibs)
 
use seq.liblib

Function libfirstpass(dependentlibs:seq.word) seq.firstpass
  @(addfirstpass, filter(dependentlibs),empty:seq.firstpass   , loadedlibs)

function filter(s:seq.word,l:liblib)  seq.liblib   if (libname.l)_1 in s then [l] else empty:seq.liblib
