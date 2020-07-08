Module intercode


use stdlib

use funcsig

use seq.sig

 use seq.fsignrep

use encoding.fsignrep

use seq.seq.sig

use otherseq.seq.sig


use seq.target


Function ?(a:sig,b:sig) ordering valueofencoding.a ? valueofencoding.b

Function type:sig internaltype export

Function type:prg internaltype export

Function lowerbits(sig) int export 

Function type:fsignrep internaltype export

Function getsigencoding seq.encodingrep.fsignrep export

Function sig(encoding.fsignrep)sig export

Function returntype(s:fsignrep)seq.word export

Function constantcode(s:fsignrep) seq.sig export

Function noparafsignrep(fsignrep) int export

Function fsig(fsignrep) seq.word export

Function mangledname(fsignrep) word export

Function module(fsignrep) seq.word export

Function optionOp sig export

Function =(sig,sig) boolean export

Function code(target) seq.sig export

Function type:target internaltype export

Function lookupcode (p:prg, s:sig) seq.target export
