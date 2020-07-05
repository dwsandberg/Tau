

Module libdesc

use stdlib

use symbol

use seq.symbol

use set.symbol

use seq.firstpass

use seq.fsignrep


use seq.seq.int

use intercode

use libscope

use seq.seq.word

use seq.word


use set.word

use seq.int



use funcsig

use set.sig

use seq.sig

use seq.libmod

use seq.mytype

use mytype

Function libdesc(p:prg,templates:program,mods:seq.firstpass,exports:seq.word,rootsigs:seq.sig) sig
  let closed=toexport(p,empty:set.sig,asset.rootsigs)  
  let simplesyms=@(+,tosymbol2,empty:seq.symbol,toseq.closed)
  let d=@(+,tolibsym(p,templates),empty:seq.symbol,simplesyms )    
    let libmods=  @(+,tolibmod(p,templates,exports),empty:seq.libmod,mods)
       + libmod(false,"$other"_1, d, empty:seq.symbol, empty:seq.mytype)
addseq.@(+,addlibmod,empty:seq.sig,libmods)
       
/function print(a:libsym) seq.word [fsig.a]+instruction.a

/function print(a:libmod) seq.word  "&br &br define &br"+ @(seperator."&br",print,"",defines.a)+"&br &br export &br"+
 @(seperator."&br",print,"",exports.a)

 function tolibmod(p:prg,templates:program,exports:seq.word,m:firstpass) seq.libmod
  if  not(   abstracttype.modname.m   in exports )  then empty:seq.libmod else
  let abstract=isabstract.modname.m
    let e=@(+,tolibsym(p,templates),empty:seq.symbol,toseq.exports.m)
   let d=if abstract then @(+,tolibsym(p,templates),empty:seq.symbol,toseq.defines.m) else empty:seq.symbol
  [libmod(modname.m,d,e, if abstract then uses.m else empty:seq.mytype)]



function tosymbol2(s:sig) seq.symbol
   let f=decode.s
   if  module.f = "$constant" then empty:seq.symbol
   else if module.f="$fref" then [Fref.tosymbol.(cleancode.f)_1]
   else [symbol(fsig.f,module.f,returntype.f)]

function   toexport(p:prg,processed:set.sig, toprocess:set.sig) set.sig
   if isempty.toprocess then  processed else 
    let q= asset.@(+,exportcode.p,empty:seq.sig,     toseq.toprocess)
      toexport(p,processed &cup toprocess, q-processed)

 Function exportcode(f:fsignrep) seq.sig
           if length.cleancode.f  < 15 then 
             if fsig.f="wordencoding" &and module.f="words"  then 
                empty:seq.sig
             else 
             cleancode.f else empty:seq.sig
           
    Function exportcode(p:prg,s:sig) seq.sig
       exportcode.lookuprep(p,s)
  
  Function exportcode(p:prg,s:symbol) seq.sig
    if fsig.s="wordencoding" &and module.s="words"  then  empty:seq.sig
    else 
      let f=lookuprep(p,tosig.s)
           if length.cleancode.f  < 15 then 
             cleancode.f else empty:seq.sig
 
function astext(p:prg,s:symbol)seq.word
 let module=module.s 
 let fsig=fsig.s
 let code=if  module="local" then "LOCAL"+fsig
   else if  module="$int"  then "LIT"+fsig
   else if module="$words" then "WORDS"+toword.length.fsig+fsig
   else if module="$word" then "WORD"+fsig
   else if module="$" then fsig
   else if module in [ "$constant"] then 
    assert false report "should not get here"+print.s
     fsig
   else if module in ["$fref"] then 
     "FREF"+mangledname.(zcode.s)_1
   else if last.module ="para"_1 then "LOCAL"+(module)_1
   else [mangledname.s,toword.nopara.s]
 if code_1 in "SET WORD WORDS LOCAL LIT APPLY RECORD 
 FREF EXITBLOCK BR BLOCK DEFINE"then code else [ code_1]

       
function astext(p:prg,s:sig)seq.word
 let rep= lookuprep(p,s)
 let f = towords2x.rep
  if f_1 = "CONSTANT"_1 then   @(+, astext(p),"", cleancode.rep)+"RECORD"+toword.length.cleancode.rep
   else if f_1 in "SET WORD WORDS LOCAL LIT APPLY RECORD FREF EXITBLOCK BR BLOCK DEFINE"then f else [ f_1]

function tolibsym(p:prg,templates:program,sym:symbol ) seq.symbol
    if module.sym in ["$","$constant","$int","local","$word","$words","$fref"] 
    then empty:seq.symbol else
    let txt=if isabstract.mytype.module.sym then 
     let t=lookupcode(templates,sym)
          @(+, astext(p),"",  code.t)
    else @(+, astext(p),"",exportcode(p,sym ))
             [ symbol(fsig.sym,module.sym, returntype.sym ,empty:seq.symbol,txt )]

----------------------------------

function addlibsym(s:symbol) sig
      constant.[wordssig.fsig.s ,wordssig.module.s ,wordssig.returntype.s ,wordssig."",wordssig.instruction.s]

function addmytype(t:mytype) sig  wordssig.(towords.t)

use seq.mytype

function addseq(s:seq.sig) sig  
constant.([ lit.0, lit.length.s ]+s )

function addlibmod(s:libmod) sig 
    constant.[lit.if isabstract.modname.s then 1 else 0
     ,wordsig.abstracttype.modname.s
     ,addseq.@(+,addlibsym,empty:seq.sig,defines.s)
      ,addseq.@(+,addlibsym,empty:seq.sig,exports.s)
    ,addseq.@(+,addmytype,empty:seq.sig,uses.s)]

_______________________________      
     
   
 