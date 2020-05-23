Module intercode


use otherseq.seq.int

use seq.seq.int

use libscope


use stdlib

use seq.symbol

use symbol



use funcsig

use seq.sig

 use seq.fsignrep

use encoding.fsignrep

use seq.seq.sig

use otherseq.seq.sig

use set.word


type intercode is record  coding:seq.fsignrep, defines:seq.int

Defines are ipointers into coding that indicate which functions are defined.


Codes give a seq of integers which are indices into coding


 
Function  addtointercode(i:intercode) intercode
 let a=orderadded.efsignrep
  intercode(  coding.i+subseq(a,length.coding.i+1,length.a),defines.i)
  
Function  intercode (sigreps:seq.fsignrep,defines:seq.int) intercode export
    
Function coding(i:intercode)seq.fsignrep export


Function ?(a:sig,b:sig) ordering valueofencoding.a ? valueofencoding.b


Function type:sig internaltype export

Function lowerbits(sig) int export 


function defines(intercode)seq.int export


Function type:fsignrep internaltype export


Function type:intercode internaltype export


Function towords2x(a:fsignrep) seq.word   export

Function returntype(s:fsignrep)seq.word export


Function constant(args:seq.sig) sig export
        
Function wordsig(w:word) sig export
 
Function wordssig(w:seq.word) sig export

Function lit(i:int) sig export


Function cleancode(a:fsignrep) seq.sig code.a 

Function nopara(fsignrep) int export

Function fsig(fsignrep) seq.word export

Function mangledname(fsignrep) word export

Function module(fsignrep) seq.word export

Function optionOp sig export

Function =(sig,sig) boolean export

_______________

 
Function getroots(s:seq.firstpass) set.symbol   @(&cup,getroots,empty:set.symbol, s)

function  getroots( f:firstpass) set.symbol  if exportmodule.f &and length.towords.modname.f = 1  then
  exports.f  else empty:set.symbol
  
  
 

  Function exportcode(f:fsignrep) seq.sig
           if length.code.f  < 15 then 
             if fsig.f="wordencoding" &and module.f="words"  then 
                empty:seq.sig
             else 
             code.f else empty:seq.sig
           
    Function exportcode(p:prg,s:sig) seq.sig
       exportcode.lookuprep(p,s)
  


use set.symbol

use seq.firstpass
    
/function addfunction(allfunctions:symbolset, mangled:word) sig
     let s2 = lookupsymbol(allfunctions, mangled)
     let a = codedown.mangled
     aseinst([ mangled, toword(length.a - 2)],empty:seq.sig, resulttype.s2)   

Function tosig(s:symbol) sig  
     sig ([name.s] , paratypes.s, modname.s , empty:seq.sig,resulttype.s)

function astext(coding:seq.fsignrep, i:sig)seq.word
 let t = towords2x.coding_lowerbits.i
  if t_1 = "LIT"_1 then [ t_2]
  else if t_1 = "LOCAL"_1 then [ merge.["%"_1, t_2]]
  else if t_1 = "WORDS"_1 then
  '"' + subseq(t, 3, length.t) + '"'
  else
    if t_1 in "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then t + " &br"else t

function ithfunc(a:intercode, i:int)seq.word
 towords2x.(coding.a)_i + @(+, astext.coding.a,"",cleancode.(coding.a)_i) 



Function towords2x(f:fsignrep) seq.word
let module=module.f 
let fsig=fsig.f
if  module="local" then "LOCAL"+fsig
   else if  module="$int"  then "LIT"+fsig
   else if module="$words" then "WORDS"+toword.length.fsig+fsig
   else if module="$word" then "WORD"+fsig
   else if module in ["$"," $constant","$fref"] then fsig
   else [mangledname.f,toword.nopara.f]


Function print(a:intercode)seq.seq.word @(+, ithfunc.a,empty:seq.seq.word, defines.a)