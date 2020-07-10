
run mylib testnew

Module libdesc

use stdlib

use symbol

use seq.symbol

use set.symbol

use seq.firstpass



use seq.seq.int


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
  let simplesyms=@(+,tosymbol,empty:seq.symbol,toseq.closed)
  let d=@(+,tolibsym(p,templates),empty:seq.symbol,simplesyms )    
    let libmods=  @(+,tolibmod(p,templates,exports),empty:seq.libmod,mods)
       + libmod(false,"$other"_1, d, empty:seq.symbol, empty:seq.mytype)
addseq.@(+,addlibmod,empty:seq.sig,libmods)
       

 function tolibmod(p:prg,templates:program,exports:seq.word,m:firstpass) seq.libmod
  if  not(   abstracttype.modname.m   in exports )  then empty:seq.libmod else
  let abstract=isabstract.modname.m
    let e=@(+,tolibsym(p,templates),empty:seq.symbol,toseq.exports.m)
   let d=if abstract then @(+,tolibsym(p,templates),empty:seq.symbol,toseq.defines.m) else empty:seq.symbol
  [libmod(modname.m,d,e, if abstract then uses.m else empty:seq.mytype)]

function   toexport(p:prg,processed:set.sig, toprocess:set.sig) set.sig
   if isempty.toprocess then  processed else 
    let q= asset.@(+,exportcode.p,empty:seq.sig,     toseq.toprocess)
      toexport(p,processed &cup toprocess, q-processed)

           
Function exportcode(p:prg,s:sig) seq.sig
        let f=decode.s
        if fsig.f="wordencoding" &and module.f="words"  then  empty:seq.sig else
        let cd=lookupcode(p,s)
        if isempty.cd then constantcode.f
        else  
           if length.code.cd_1   < 15 then  code.cd_1    else empty:seq.sig
              
use seq.target
  
 Function exportcode(p:prg,s:symbol) seq.symbol
    if fsig.s="wordencoding" &and module.s="words"  then  empty:seq.symbol
    else 
      let f=lookupcode(p,tosig.s)
      if isempty.f  then empty:seq.symbol
      else     if length.code.f_1  < 15 then 
           @(+,sigtosyms.p,empty:seq.symbol,code.f_1) else empty:seq.symbol
             
             
  function   sigtosyms(p:prg,s:sig) seq.symbol
            let f=decode.s
              if module.f ="$fref" then 
                [Fref.sigtosyms(p,(constantcode.f)_1)_1]
              else if module.f = "$constant" then
               @(+,sigtosyms.p,empty:seq.symbol,constantcode.f)+Record.length.constantcode.f
              else [tosymbol.s]
                     
function tolibsym(p:prg,templates:program,sym:symbol ) seq.symbol
    if module.sym in ["$","$constant","int $","local","$word","$words","$fref"] 
    then empty:seq.symbol else
    if isabstract.mytype.module.sym then 
     let t=lookupcode(templates,sym)
              [ symbol(fsig.sym,module.sym, returntype.sym ,[sym]+code.t )]
    else 
      let code=exportcode(p,sym )
                  [ symbol(fsig.sym,module.sym, returntype.sym ,[sym]+code )]
   

----------------------------------

function addlibsym(s:symbol) sig
      constant.[wordssig.fsig.s ,wordssig.module.s ,wordssig.returntype.s ,addseq.@(+,addlibsym,empty:seq.sig,zcode.s),lit.0]

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


   
 