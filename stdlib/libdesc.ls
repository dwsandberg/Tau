

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
  let abstract=@(+,abstractmods(known),empty:seq.libmod,mods)
  let rootsigs=@(+,tosig,empty:seq.sig,toseq.getroots(mods))
 // let closed=toexport(p,empty:set.sig,asset.rootsigs) //
    let t=@(&cup,getmore,empty:set.symbol,mods)
  let b=@(+,tolibsym(p,known),empty:seq.libsym,toseq.t)
  assert length.rootsigs=cardinality.t report "XXX"
    let have=@(+,fsig,empty:set.word,b)
  let d=close(p,intercode,known,b,have,empty:seq.libsym) 
    let x1=asset.@(+,fsig,"",d)
   // let x2=asset.@(+,mangledname,"",toseq.closed) //
   // assert length.d=cardinality.closed report "XXXY"+toseq(x2-x1)  //
 // let d=@(+,tolibsym(p,known),empty:seq.libsym,toseq.closed )  //
  let z=@(add,identity,emptyworddict:worddict.libsym,d) 
  @(+,libmod(z),abstract,mods)
+ libmod(false,"$other"_1, sort.d, empty:seq.libsym, empty:seq.mytype)

function  mangledname(s:sig) seq.word 
let rep=decode.s
if (module.rep)_1 in "local $int $constant $ $word $words" then empty:seq.word
else [mangledname.rep]

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
     
  
function getmore(f:firstpass) set.symbol
   if not.exportmodule.f &or isabstract.modname.f then empty:set.symbol
  else  
    exports.f
    
   

      
function filter(  i:int,result:seq.word, src:seq.word) seq.word
 if i > length.src then result
  else
  let name = src_i
   if name in "builtinZinternal1Zwordzseq builtinZinternal1Zinternal1 if  IDXUC getinstanceZbuiltinZTzerecord
   STATEZinternal1Zinternal1 IDXUCZbuiltinZintZint optionZbuiltinZwordZTzseq " then filter( i + 1,result, src)
   else if name in "SET LIT LOCAL WORD DEFINE
    RECORD APPLY LOOPBLOCK  CONTINUE FINISHLOOP CRECORD BLOCK EXITBLOCK BR" then filter( i + 2, result,src)
   else if name = "FREF"_1 then filter( i+2,result+src_(i+1),src)
   else  if name = "WORDS COMMENT"_1 then
   filter( i + toint.src_(i + 1) + 2,result, src)
   else  filter( i+1, result+name,src)
     
 function calls(a:libsym) seq.word   
   let d= codedown.fsig.a
   assert length.d > 1 report "IN calls"+fsig.a
   if (d_2)_1="T"_1 then empty:seq.word else 
   filter(1,"",instruction.a)

   
      
function stripparsedfunc(src:seq.word) seq.word
if length.src > 0 ∧ (src)_1 = "parsedfunc"_1 then
         subseq(src ,toint.(src)_2 + 3, length.src) else src
      
use set.sig

function   toexport(p:prg,processed:set.sig, toprocess:set.sig) set.sig
   if isempty.toprocess then processed else 
    let q= asset.@(+,exportcode.p,empty:seq.sig,     toseq.toprocess)
      toexport(p,processed &cup toprocess, q-processed)

   
 use seq.sig
  
function find4(p:prg, known:symbolset, mangledname:word) libsym
   tolibsym(p,known,lookupsymbol(known,mangledname) )
    
function close(p:prg,intercode:intercode,   known:symbolset,toprocess:seq.libsym,have:set.word,processed:seq.libsym) seq.libsym 
     let more=asset.@(+,calls,"",toprocess)-have
     if isempty.more then processed+toprocess else 
    let new=@(+,find4(p,known),empty:seq.libsym,toseq.more)
     close(p,intercode,known,new,have &cup more,processed+toprocess)
     

 
  
function find(t:worddict.libsym,s:symbol) seq.libsym lookup(t,mangledname.s)

function libmod (t:worddict.libsym, f:firstpass) seq.libmod
     if not.exportmodule.f &or isabstract.modname.f then empty:seq.libmod
     else  
       let e=sort.@(+,find.t,empty:seq.libsym,toseq.exports.f)
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

function tolibsym(p:prg,known:symbolset,sym:symbol) libsym
 let s=   tosig.sym      
 let   rep=lookuprep(p,s)
// assert mangledname.rep=mangledname.sym 
 &or mangledname.sym in "lastZwordzseqZTzseq lastZintzseqZTzseq isemptyZcharzseqZTzseq"
 report "HJK"+print.[s]+mangledname.sym+"/"+mangledname.rep
 let sym2=lookupsymbol(known,mangledname.sym)  
   assert resulttype.sym= resulttype.sym2 &and mangledname.sym=mangledname.sym2 report "XXX"+print.sym+
     "/"+print.sym2 //
    let t=astext5(p,exportcode.rep) 
         libsym(resulttype.sym,mangledname.sym,t)
         
    

function tolibsym(p:prg,known:symbolset,s:sig ) libsym
  let rep=lookuprep(p,s)
  let sym=lookupsymbol(known,mangledname.rep)
   let t=astext5(p,exportcode.rep) 
         libsym(resulttype.sym,mangledname.sym,t)

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
 assert length.d > 1 report "tosymbol"+fsig.ls
 let modname = mytype.d_2
 let paratypes = @(+, mytype, empty:seq.mytype, subseq(d, 3, length.d))
 let newparatypes=@(+, replaceT.parameter.modname, empty:seq.mytype, paratypes)
 let mc = manglechars(d_1_1, modname, paratypes)
  symbol(fsig.ls, mytype.returntype.ls, newparatypes, d_1_1, modname, instruction.ls, mc)
  
   function tosymbol2(ls:libsym)symbol
 let d = codedown.fsig.ls
 assert length.d > 1 report "tosymbol"+fsig.ls
 let modname = mytype.d_2
 let paratypes = @(+, mytype, empty:seq.mytype, subseq(d, 3, length.d))
 let newparatypes=@(+, replaceT.parameter.modname, empty:seq.mytype, paratypes)
 let mc = manglechars(d_1_1, modname, paratypes)
  let b=symbol(fsig.ls, mytype.returntype.ls,paratypes, d_1_1, modname, instruction.ls, mc)
  assert paratypes=newparatypes report "JKLH"+ fsig.ls
  b

use mangle

/function  fixmangled(a:word) word
let d = codedown.a
 assert length.d > 1 report "fixmangled"+a
 if (length.d_2 )=1 &or (length(d_2)=2 &and d_2_1="T"_1) &or length.d=2  then a
 else let modname = mytype.d_2
 let paratypes = @(+, mytype, empty:seq.mytype, subseq(d, 3, length.d))
 let newparatypes=@(+, replaceT.parameter.modname, empty:seq.mytype, paratypes)
  mangle (d_1_1 , modname, newparatypes)

 

function tofirstpass(m:libmod)  firstpass
 if parameterized.m then
  firstpass(mytype.if parameterized.m then"T" + modname.m else [ modname.m], uses.m, 
 @(+, tosymbol2, empty:set.symbol, defines.m), 
 @(+, tosymbol2, empty:set.symbol, exports.m), empty:seq.symbol, empty:set.symbol, false )
 else 
   firstpass(mytype.[modname.m] , uses.m, 
 @(+, tosymbol, empty:set.symbol, defines.m), 
 @(+, tosymbol, empty:set.symbol, exports.m), empty:seq.symbol, empty:set.symbol, false )


Function tofirstpass(l:liblib)seq.firstpass @(+, tofirstpass, empty:seq.firstpass, mods.l)

Function addknown(a:symbolset,l:liblib) symbolset   @(+, tosymbol, a, defines.last.mods.l)
