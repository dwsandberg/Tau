#!/usr/local/bin/tau

Module stdlib 

Library stdlib UTF8 bitpackedseq bits blockseq codegen codetemplates  deepcopy encoding fileio format graph groupparagraphs intercode internalbc ipair libdescfunc libscope llvm main2 opt2 oseq packedseq parse pass1 pass2 persistant persistantseq prims process real reconstruct seq set stack stacktrace symbol textio tree worddict xxhash 
 timestamp maindict uses 
 exports UTF8 bits blockseq  deepcopy encoding fileio format graph groupparagraphs 
 internalbc ipair  libscope llvm main2  unsafe packedseq   process real reconstruct seq set stack stacktrace 
 stdlib  textio tree prims symbol timestamp ioseq dataio maindict symbol intercode pass2  libdescfunc otherseq words mangle


use UTF8

use seq.int

use seq.seq.int

use seq.seq.word

use seq.word

use xxhash

use otherseq.int

use otherseq.word

use words




type ordering is record toint:int

type boolean is record toint:int

* Useful constants

Function openpara word {"("_1 }

Function closepara word {")"_1 }

Function comma word {","_1 }

Function openbracket word {"["_1 }

Function closebracket word {"]"_1 }

Function colon word {":"_1 }

Function space word encodeword.[ char.32]

Function EOL word encodeword.[ char.10]





* EQ GT and LT are the possible results of ? operator

Function EQ ordering ordering.1

Function GT ordering ordering.2

Function LT ordering ordering.0

Function true boolean boolean.1

Function false boolean boolean.0

-----------------

Function toint(boolean)int export


Function-(i:int)int 0 - i

Function ?(a:int, b:int)ordering builtin.usemangle

Function ?(a:ordering, b:ordering)ordering toint.a ? toint.b

Function +(a:int, b:int)int builtin.usemangle

Function-(a:int, b:int)int builtin.usemangle

Function *(a:int, b:int)int builtin.usemangle

Function /(a:int, b:int)int builtin.usemangle

Function hash(i:int)int finalmix.hash(hashstart, i)

Function =(a:int, b:int)boolean builtin.usemangle

Function =(a:ordering, b:ordering)boolean toint.a = toint.b

Function =(a:boolean, b:boolean)boolean toint.a = toint.b

Function toword(o:ordering)word {"LT EQ GT"_(toint.o + 1)}

Function ∧(a:ordering, b:ordering)ordering 
 let x = a 
  if x = EQ then b else x

--------------------

Function ?(a:boolean, b:boolean)ordering toint.a ? toint.b

Function ∧(a:boolean, b:boolean)boolean 
 if a then b else // false // boolean.0

Function ∨(a:boolean, b:boolean)boolean 
 if a 
  then // true is not use so simple inline expansion is used to produce short circuit evaluation // 
   boolean.1 
  else b

Function not(a:boolean)boolean builtin.usemangle

Function abs(x:int)int if x < 0 then 0 - x else x

Function mod(x:int, y:int)int if x < 0 then x - x / y * y + y else x - x / y * y

Function >(a:int, b:int)boolean builtin.usemangle

Function <(a:int, b:int)boolean export

Function ≤(a:int, b:int)boolean export

Function ≥(a:int, b:int)boolean export

Function max(a:int, b:int)int if a > b then a else b

Function min(a:int, b:int)int if a < b then a else b

Function between(i:int, lower:int, upper:int)boolean i ≥ lower ∧ i ≤ upper

---------------------------



Function hash(a:seq.int)int finalmix.@(hash, identity, hashstart, a)



Function hash(a:seq.word)int finalmix.@(hash, hash, hashstart, a)




Function^(i:int, n:int)int @(*, identity, 1, constantseq(n, i))

Function pseudorandom(seed:int)int 
 let ah = 16807 
  let mh = 2147483647 
  let test = ah *(seed mod(mh / ah)) - mh mod ah *(seed /(mh / ah))
  if test > 0 then test else test + mh

function addrandom(s:seq.int, i:int)seq.int s + pseudorandom(s_length.s)

Function randomseq(seed:int, length:int)seq.int @(addrandom, identity, [ seed], constantseq(length - 1, 1))

Function randomint(i:int)seq.int builtin.usemangle

Function lines(a:seq.word, b:seq.word)seq.word a + EOL + b

Function seperator(sep:seq.word, s:seq.word, w:seq.word)seq.word 
 if length.s = 0 then w else s + sep + w

Function seperator(sep:seq.word, s:seq.word, w:word)seq.word 
 // Good for adding commas in seq of words. @(seperator(",", toword,"", [ 1, 2, 3])// 
  if length.s = 0 then [ w]else s + sep + w
  

Function hash(a:word)int export

Function ?(a:word, b:word)ordering export

Function =(a:word, b:word)boolean export

Function ≠(a:word, b:word)boolean export

Function ≠(a:int, b:int)boolean export
 
Function toword(n:int)word 
 // Covert integer to  a single word. // 
 export
 
Function toint(w:word)int 
 // Convert an integer represented as a word to an int // export
 
Function merge(a:seq.word)word 
 // make multiple words into a single word. // export

Function type:ordering internaltype  export

Function type:boolean internaltype  export

Function type:word  internaltype  export

Function type:seq.word  internaltype  export

Function type:seq.seq.word  internaltype  export

Function type:seq.int internaltype export


Function empty:seq.seq.word seq.seq.word  export

Function empty:seq.word  seq.word export

Function empty:seq.int  seq.int export

Function arithseq(int, int, int)seq.int export

Function constantseq(len:int, element:int)seq.int export

Function_(seq.word, int)word export

Function_(seq.seq.word, int)seq.word export

Function_(seq.int, int)int export

Function_(s:pseq.seq.word, i:int)seq.word export

Function_(pseq.int, int)int export

Function_(a:pseq.word, b:int)word export

Function length(seq.word)int export

Function length(seq.seq.word)int export

Function length(seq.int)int export

Function findindex(word, seq.word)int export

Function findindex(seq.word, seq.seq.word)int export

Function findindex(word, seq.word, int)int export

Function identity(seq.word)seq.word export

Function identity(word)word export

Function identity(int)int export

Function last(s:seq.word)word export

Function subseq(seq.seq.word, int, int)seq.seq.word export

Function subseq(seq.word, int, int)seq.word export

Function subseq(seq.int, int, int)seq.int export

Function in(word, seq.word)boolean export

Function in(seq.word, seq.seq.word)boolean export

Function in(int, seq.int)boolean export

Function =(seq.word, seq.word)boolean export

Function =(seq.int, seq.int)boolean export

Function +(seq.word, word)seq.word export

Function +(seq.int, seq.int)seq.int export

Function +(seq.int, int)seq.int export

Function last(seq.int) int export

Function +(seq.seq.word, seq.word)seq.seq.word export

Function +(seq.seq.word, seq.seq.word)seq.seq.word export

Function +(a:seq.word, b:seq.word)seq.word export


Function alphasort(a:seq.word)seq.word export 


Function alphasort(a:seq.seq.word)seq.seq.word export

  
* usegraph include  xxhash encoding   bits  words real subreal
stacktrace  textio reconstruct  UTF8  seq otherseq
blockseq packedseq bitpackedseq stdlib exclude stdlib seq  




* usegraph include  prims   tree  graph ipair libscope internalbc
process stack set   format groupparagraphs   dict fileio
exclude stdlib seq 

* usegraph include  main2 libscope display constant codegen convert 
 parse pass1  symbol libdescfunc  
codetemplates pass2 persistant   llvm  
reconstruct persistantseq opt2
symbol parse libdescfunc internalbc intercode cvttoinst codegen
exclude seq set otherseq stdlib bits tree graph UTF8 stack stacktrace real process  ipair deepcopy
bitpackedseq packedseq fileio blockseq textio encoding words
   

module words

use stdlib

use encoding.seq.int

use seq.char

use seq.alphaword

use otherseq.alphaword

use otherseq.int

use otherseq.char

use otherseq.seq.alphaword

use seq.alphaword



use seq.seq.alphaword



use UTF8

use words

Function type:word  internaltype  export


type wordencoding is encoding seq.char

Function wordencoding erecord.seq.char export

type word is record asencoding:encoding.seq.char

Function asencoding(w:word) encoding.seq.char export

Function word(encoding.seq.char) word export

Function add(erecord.seq.char,seq.encodingrep.seq.char) int export

Function encodeword(a:seq.char)word  word.encode(wordencoding,a)

Function decodeword(w:word)seq.char decode( wordencoding,asencoding.w)

Function hash(a:word)int hash.asencoding.a

Function =(a:word, b:word)boolean asencoding.a = asencoding.b

Function ?(a:word, b:word)ordering asencoding.a ? asencoding.b

Function merge(a:seq.word)word 
 // make multiple words into a single word. // encodeword.@(+, decodeword, empty:seq.char, a)

* Functions to perform alphabetical sorting

Function type:alphaword internaltype export


type alphaword is record toword:word

Function alphaword(word)alphaword export

Function toword(alphaword)word export

Function toalphaseq(a:seq.word)seq.alphaword 
 // This is just a type change and the compiler recognizes this and does not generate code // 
  @(+, alphaword, empty:seq.alphaword, a)

Function ?(a:alphaword, b:alphaword)ordering 
 if toword.a = toword.b then EQ else decodeword.toword.a ? decodeword.toword.b

Function towordseq(a:seq.alphaword)seq.word @(+, toword, empty:seq.word, a)

Function alphasort(a:seq.word)seq.word towordseq.sort.toalphaseq.a

Function ?(a:seq.alphaword, b: seq.alphaword)ordering export

use seq.seq.alphaword

Function alphasort(a:seq.seq.word)seq.seq.word 
 let b = @(+, toalphaseq, empty:seq.seq.alphaword, a)
  @(+, towordseq, empty:seq.seq.word, sort.b)


