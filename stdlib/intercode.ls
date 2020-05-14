Module intercode


use otherseq.seq.int

use seq.seq.int

use libscope


use stdlib

use seq.symbol

use symbol

use seq.tree.seq.word

use tree.seq.word

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


function addcodes(allfunctions:symbolset, a:seq.seq.sig, f:symbol)seq.seq.sig 
let t=prepb(allfunctions, codetree.f)
replace(a,   lowerbits.valueofencoding.addfunction(allfunctions,mangledname.f),t )

Function convert2(allfunctions:symbolset, s:seq.symbol)intercode
 let discard=basesigs
 let ms=@(+,mangledname,"",s)
 let defines = @(add2, addfunction.allfunctions, empty:seq.int, ms)
 let codes=@(addcodes.allfunctions, identity, dseq.empty:seq.sig, s)
  intercode(setcode(orderadded,codes, 1,empty:seq.fsignrep),defines)
  
function  add2(s:seq.int,f:sig) seq.int   s+  lowerbits.valueofencoding.f

   
function  setcode(coding:seq.fsignrep,codes:seq.seq.sig,i:int,result:seq.fsignrep) seq.fsignrep
   if i > length.coding then result
   else  
    let a=coding_i
    if (towords.a)_1 in "CONSTANT FREF" then
      setcode(coding,codes,i+1,result+a)
    else
     let t=fsignrep( fsig.a, module.a, 1,  codes_i,returntype.a,towords.a)
     setcode(coding,codes,i+1,result+t)

Function prepb(allfunctions:symbolset, t:tree.seq.word)seq.sig
 let inst = inst.t
  if inst in "PARAM"then [ aseinst.[ inst, toword(- toint.arg.t - 1)]]
  else if inst in "LIT LOCAL   WORD  WORDS"then [ aseinst.label.t]
   else  if inst = "DEFINE"_1 then
  prepb(allfunctions, t_1) + aseinst(label.t)  
  else  if inst = "SET"_1 then
  prepb(allfunctions, t_1) + aseinst("DEFINE" + arg.t) + prepb(allfunctions, t_2)
   + aseinst.[ inst, arg.t]
  else  if inst = "LOOPBLOCK"_1 then
  // number of sons of loop block may have change with optimization //
   let firstvar = arg.last.sons.t
    @(+, prepb.allfunctions, empty:seq.sig, subseq(sons.t, 1, nosons.t - 1))
    + aseinst("LIT" + firstvar)
    + aseinst.[ inst, toword.nosons.t]
  else if inst = "CRECORD"_1 then 
       let z=   @(+, prepb.allfunctions, empty:seq.sig, sons.t)
       assert length.z=nosons.t report "???"
   [ asinstconstant.z]
   else if inst ="FREF"_1 then
    let z=addfunction(allfunctions,(label.t)_2)
   [ aseinst(label.t,[z])]
  else 
   @(+, prepb.allfunctions, empty:seq.sig, sons.t)
   + if inst in "IDXUC    CONTINUE RECORD  FINISHLOOP   EXITBLOCK BLOCK BR"
   then [ aseinst.[ inst, toword.nosons.t]]
   else if inst = "STATE"_1 then empty:seq.sig
   else [addfunction(allfunctions,inst)]
       
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
   // if t_1 ="SET"_1 then""else //
   if t_1 in "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then t + " &br"else t

function ithfunc(a:intercode, i:int)seq.word
 towords.(coding.a)_i + @(+, astext.coding.a,"",cleancode.(coding.a)_i) 
 
 

Function print(a:intercode)seq.seq.word @(+, ithfunc.a,empty:seq.seq.word, defines.a)