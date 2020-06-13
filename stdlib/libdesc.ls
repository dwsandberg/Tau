

Module libdesc

use stdlib


use seq.firstpass

use seq.fsignrep


use seq.seq.int

use intercode

use libscope

use seq.seq.word

use seq.word


use set.word

use seq.int

use seq.libsym

use otherseq.libsym

use seq.expmod


use funcsig

use set.sig

use seq.sig

use seq.libmod

use seq.mytype

Function libdesc(p:prg,simple:seq.expmod,abstract2:seq.expmod) sig
    let abstract3= @(+,tolibmod(p,true),empty:seq.libmod,abstract2)
  let rootsigs=@(+,exports,empty:seq.sig,simple)  
  let closed=toexport(p,empty:set.sig,asset.rootsigs)   
  let d=@(+,tolibsym(p),empty:seq.libsym,toseq.closed )    
  let libmods=    @(+,tolibmod(p,false),abstract3,simple)
       + libmod(false,"$other"_1, sort.d, empty:seq.libsym, empty:seq.mytype)
addseq.@(+,addlibmod,empty:seq.sig,libmods)
       
function print(a:libsym) seq.word [fsig.a]+instruction.a

function print(a:libmod) seq.word  "&br &br define &br"+ @(seperator."&br",print,"",defines.a)+"&br &br export &br"+
 @(seperator."&br",print,"",exports.a)

 function tolibmod(p:prg,abstract:boolean,m:expmod) libmod
  let e=@(+,tolibsym.p,empty:seq.libsym,exports.m)
   let d=@(+,tolibsym.p,empty:seq.libsym,defines.m)
  libmod(abstract, modname.m,d,e, uses.m)

function   toexport(p:prg,processed:set.sig, toprocess:set.sig) set.sig
   if isempty.toprocess then  processed else 
    let q= asset.@(+,exportcode.p,empty:seq.sig,     toseq.toprocess)
      toexport(p,processed &cup toprocess, q-processed)

 Function exportcode(f:fsignrep) seq.sig
           if length.code.f  < 15 then 
             if fsig.f="wordencoding" &and module.f="words"  then 
                empty:seq.sig
             else 
             code.f else empty:seq.sig
           
    Function exportcode(p:prg,s:sig) seq.sig
       exportcode.lookuprep(p,s)
  

       
function astext(p:prg,s:sig)seq.word
 let rep= lookuprep(p,s)
 let f = towords2x.rep
  if f_1 = "CONSTANT"_1 then   astext5(p,cleancode.rep)+"RECORD"+toword.length.cleancode.rep
   else if f_1 in "SET WORD WORDS LOCAL LIT  RECORD FREF EXITBLOCK BR BLOCK DEFINE"then f else [ f_1]

function astext5(p:prg, d:seq.sig)seq.word @(+, astext(p),"", d)

/use seq.char

function tolibsym(p:prg,s:sig ) seq.libsym
   let rep=lookuprep(p,s)
   if module.rep in ["$","$constant","$int","local","$word","$words","$fref"] 
   &or fsig.rep="xgetinstance(T erecord)" &or s=IDXUC then empty:seq.libsym else
  // assert not("T"_1 in fsig.rep) &and( (fsig.rep)_1 in "EQ OPAQUE" &or
    not(  char1.":" in  decodeword.(fsig.rep)_1))
    report print.[s] //
 let t=astext5(p,if isabstract.mytype.module.rep then code.rep else exportcode.rep) 
 // assert length.t =0 &or not(t_1="EXITBLOCK"_1) report "KLP"+t //
 let t2= if length.t > 0 &and t_1="EXITBLOCK"_1 then subseq(t,5,length.t)
  else t
            [ libsym(mytype.returntype.rep,mangledname.rep,t2)]

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

_______________________________      
     
   
 