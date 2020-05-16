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


type intercode is record  xcoding:seq.fsignrep, defines:seq.int

Defines are ipointers into coding that indicate which functions are defined.


Codes give a seq of integers which are indices into coding


 
Function  addtointercode(i:intercode) intercode
 let a=orderadded 
  intercode(  xcoding.i+subseq(a,length.coding.i+1,length.a),defines.i)
  
Function  intercode2(sigreps:seq.fsignrep,defines:seq.int) intercode
   intercode(  sigreps  ,defines)
   
function orderadded seq.fsignrep  orderadded.efsignrep

function aseinst(f:fsignrep) sig sig.encode(efsignrep, f) 

Function type:sig internaltype export

Function lowerbits(sig) int export 

Function ?(a:sig,b:sig) ordering valueofencoding.a ? valueofencoding.b


Function coding(i:intercode)seq.fsignrep xcoding.i


function defines(intercode)seq.int export


Function type:fsignrep internaltype export


Function type:intercode internaltype export


Function cleancode(a:fsignrep) seq.sig code.a 

Function towords(a:fsignrep) seq.word  export

Function returntype(s:fsignrep)seq.word export

Function mangledname2(a:fsignrep)word (towords.a)_1

function aseinst(w:seq.word,code:seq.sig)sig aseinst(w,code,mytype."?")

Function aseinst(w:seq.word )sig aseinst(w,empty:seq.sig,mytype."?")
 
function aseinst(w:seq.word,code:seq.sig,typ:mytype) sig
 aseinst.fsignrep( "", "", 1,  code, towords.typ,w)


Function asinstconstant(t:seq.sig) sig aseinst("CONSTANT"+@(+,toword,"",t),t)

 function toword(s:sig) word  toword.lowerbits.valueofencoding.s
 
_______________


        
function addfunction(allfunctions:symbolset, mangled:word) sig
     let s2 = lookupsymbol(allfunctions, mangled)
     let a = codedown.mangled
     aseinst([ mangled, toword(length.a - 2)],empty:seq.sig, resulttype.s2)   


/function astext(coding:seq.inst, i:int)seq.word towords.coding_lowerbits.i

function astext(coding:seq.fsignrep, i:sig)seq.word
 let t = towords.coding_lowerbits.i
  if t_1 = "LIT"_1 then [ t_2]
  else if t_1 = "LOCAL"_1 then [ merge.["%"_1, t_2]]
  else if t_1 = "WORDS"_1 then
  '"' + subseq(t, 3, length.t) + '"'
  else
    if t_1 in "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then t + " &br"else t

function ithfunc(a:intercode, i:int)seq.word
 towords.(coding.a)_i + @(+, astext.coding.a,"",cleancode.(coding.a)_i) 
 
 

Function print(a:intercode)seq.seq.word @(+, ithfunc.a,empty:seq.seq.word, defines.a)