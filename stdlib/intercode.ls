Module intercode


use otherseq.seq.int

use seq.seq.int

use libscope


use stdlib




use funcsig

use seq.sig

 use seq.fsignrep

use encoding.fsignrep

use seq.seq.sig

use otherseq.seq.sig

/use set.word

use set.sig


type intercode is record  coding:seq.fsignrep, defines:seq.sig, uses:set.sig,modlist:sig

Defines are pointers into coding that indicate which functions are defined.

Codes give a seq of integers which are indices into coding
  
Function  intercode (sigreps:seq.fsignrep,defines:seq.sig,  uses:set.sig,modlist:sig) intercode export
    
Function coding(i:intercode)seq.fsignrep export

Function ?(a:sig,b:sig) ordering valueofencoding.a ? valueofencoding.b

Function type:sig internaltype export

Function lowerbits(sig) int export 

Function defines(i:intercode)seq.sig  export

Function uses(i:intercode)set.sig  export

Function type:fsignrep internaltype export

Function modlist(fs:intercode) sig  export

sig(last.coding.fs)

Function type:intercode internaltype export

Function returntype(s:fsignrep)seq.word export


/Function constant(args:seq.sig) sig export
        
/Function wordsig(w:word) sig export
 
/Function wordssig(w:seq.word) sig export

/Function lit(i:int) sig export


Function cleancode(a:fsignrep) seq.sig code.a 

Function nopara(fsignrep) int export

Function fsig(fsignrep) seq.word export

Function mangledname(fsignrep) word export

Function module(fsignrep) seq.word export

Function optionOp sig export

Function =(sig,sig) boolean export

_______________



use seq.firstpass

use seq.mytype


type expmod is record modname:word, exports:seq.sig,defines:seq.sig,uses:seq.mytype

function type:expmod internaltype export

function exports(expmod) seq.sig export

function defines(expmod) seq.sig export

function modname(expmod)  word export

function uses(expmod)  seq.mytype export

function expmod(modname:word, exports:seq.sig,defines:seq.sig,uses:seq.mytype) expmod export
    


function astext(coding:seq.fsignrep, i:sig)seq.word
 let t = towords2x.coding_lowerbits.i
  if t_1 = "LIT"_1 then [ t_2]
  else if t_1 = "LOCAL"_1 then [ merge.["%"_1, t_2]]
  else if t_1 = "WORDS"_1 then
  '"' + subseq(t, 3, length.t) + '"'
  else
    if t_1 in "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then t + " &br"else t

function ithfunc(a:intercode, i:sig)seq.word
let coding=(coding.a)_lowerbits.i
 towords2x.coding + @(+, astext.coding.a,"",cleancode.coding) 



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