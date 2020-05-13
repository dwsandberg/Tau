Module intercode

use seq.inst

use otherseq.seq.int

use seq.seq.int

use libscope


use stdlib

use seq.symbol

use symbol

use seq.tree.seq.word

use tree.seq.word

type intercode is record  coding:seq.inst, defines:seq.int

Defines are ipointers into coding that indicate which functions are defined.


Codes give a seq of integers which are indices into coding

function intercode(coding:seq.inst, defines:seq.int)intercode export



use funcsig

use seq.sig

Function type:sig internaltype export

Function lowerbits(sig) int export 

Function cleancode(a:inst) seq.sig code.torep.a 

function coding(intercode)seq.inst export

function defines(intercode)seq.int export

Function type:inst internaltype export

Function type:intercode internaltype export


type inst is record torep:fsignrep

function inst(towords:seq.word,returntype:mytype, code:seq.int) inst
  inst.fsignrep( "", "", 1, @(+,ecvt,empty:seq.sig,code), towords.returntype,towords)
  
Function towords(a:inst) seq.word  towords.torep.a

Function returntype(a:inst) mytype  mytype.returntype.torep.a



Function toinst(a:seq.fsignrep) seq.inst
@(+,toinst,empty:seq.inst,a)



function toinst(a:fsignrep) inst  let t=inst.lowerbits.a
let b=encode(einst,t)
t


 use seq.fsignrep

use encoding.fsignrep

function assignencoding(l:int, a:inst) int l+1 

function aseinst(w:seq.word,code:seq.int)int 
aseinst(w,code,mytype."?")

Function aseinst(w:seq.word )int 
  aseinst(w,empty:seq.int,mytype."?")
 
function  aseinst(w:seq.word,code:seq.int,typ:mytype) int
aseinst.inst(w,typ,code )


Function aseinst(f:inst) int
 valueofencoding.encode(einst, f)

  lowerbits.sig.encode(efsignrep, torep.f) 

Function asinstconstant(t:seq.int) int aseinst("CONSTANT"+@(+,toword,"",t),t)

 
function castsig(a:int) sig builtin."PARAM 1"
 
 
Function mangledname(a:inst)word(towords.a)_1

Function nopara(a:inst)int toint.(towords.a)_2


function towords(a:inst)seq.word export

function returntype(a:inst)mytype export

_______________

type einst is encoding inst

function hash(a:inst)int hash.towords.torep.a

function =(a:inst, b:inst)boolean towords.torep.a = towords.torep.b

function addcodes(allfunctions:symbolset, a:seq.seq.int, f:symbol)seq.seq.int 
let t=prepb(allfunctions, codetree.f)
replace(a, addfunction(allfunctions,mangledname.f),t )


Function additionalinst(i:int) seq.inst subseq(orderadded.einst,i,length.orderadded.einst)


Function convert2(allfunctions:symbolset, s:seq.symbol)intercode
 let ms=@(+,mangledname,"",s)
 let defines = @(+, addfunction.allfunctions, empty:seq.int, ms)
 let codes=@(addcodes.allfunctions, identity, dseq.empty:seq.int, s)
  intercode(setcode(orderadded.einst,codes, 1,empty:seq.inst),defines)

use set.word
   
function  setcode(coding:seq.inst,codes:seq.seq.int,i:int,result:seq.inst) seq.inst
   if i > length.coding then result
   else  
    let a=coding_i
    if (towords.a)_1 in "CONSTANT FREF" then
      setcode(coding,codes,i+1,result+a)
    else
     setcode(coding,codes,i+1,result+inst(towords.a,returntype.a,codes_i))

Function prepb(allfunctions:symbolset, t:tree.seq.word)seq.int
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
    @(+, prepb.allfunctions, empty:seq.int, subseq(sons.t, 1, nosons.t - 1))
    + aseinst("LIT" + firstvar)
    + aseinst.[ inst, toword.nosons.t]
  else if inst = "CRECORD"_1 then 
       let z=   @(+, prepb.allfunctions, empty:seq.int, sons.t)
       assert length.z=nosons.t report "???"
   [ asinstconstant.z]
   else if inst ="FREF"_1 then
    let z=addfunction(allfunctions,(label.t)_2)
   [ aseinst(label.t,[z])]
  else 
   @(+, prepb.allfunctions, empty:seq.int, sons.t)
   + if inst in "IDXUC    CONTINUE RECORD  FINISHLOOP   EXITBLOCK BLOCK BR"
   then [ aseinst.[ inst, toword.nosons.t]]
   else if inst = "STATE"_1 then empty:seq.int
   else [addfunction(allfunctions,inst)]
       
function addfunction(     allfunctions:symbolset, mangled:word) int
     let s2 = lookupsymbol(allfunctions, mangled)
         let a = codedown.mangled
            aseinst([ mangled, toword(length.a - 2)],empty:seq.int, resulttype.s2)   


/function astext(coding:seq.inst, i:int)seq.word towords.coding_lowerbits.i

function astext(coding:seq.inst, i:sig)seq.word
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