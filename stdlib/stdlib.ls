#!/usr/local/bin/tau

Library stdlib UTF8 altgen bitpackedseq bits blockseq buildtree codegen codetemplates definestruct display fileio format graph groupparagraphs internalbc invertedseq ipair 
libdesc libdescfunc libscope llvm main opt2 oseq packedseq parse pass0 pass1a pass2 passcommon persistant pretty prims process processtypes real reconstruct seq set stack stacktrace symbol textio tree 
  cvttoinst newsymbol convertlibtyp newparse other intercode libdescfuncnew  main2
 uses 
 exports UTF8 bitpackedseq bits blockseq  display fileio format graph internalbc
  invertedseq ipair libdesc libscope llvm main oseq passcommon persistant prims process real 
  reconstruct seq set stack stacktrace stdlib textio tree   codetemplates intercode groupparagraphs codegen
  cvttoinst newsymbol pass2 persistantseq   other libdescfuncnew  main2
  
/Library stdlib
 UTF8 altgen bitpackedseq bits blockseq codegen codetemplates fileio format graph groupparagraphs   internalbc  invertedseq   ipair
 libscope llvm  oseq  packedseq pass2 persistant prims process real  reconstruct seq set stack stacktrace textio  tree    
 cvttoinst newsymbol   newparse other intercode libdescfuncnew  main2
  uses 
 exports stdlib UTF8 seq main2 reconstruct oseq stacktrace process real invertedseq ipair set graph textio blockseq packedseq
 deepcopy tree fileio pass2 stack newimp2 persistant persistantseq deepcopy llvm libscope internalbc
 

module stdlib

use UTF8

use oseq.alphaword

use oseq.int

use oseq.seq.alphaword

use seq.alphaword

use seq.int

use seq.moddesc

use seq.seq.alphaword

use seq.seq.int

use seq.seq.word

use seq.word

use stacktrace

use stdlib

use textio


type int

type ordering is record toint:int

type boolean is record toint:int

* Useful constants



Function openpara word {"("_1 }

Function closepara word {")"_1 }

Function comma word {","_1 }

Function openbracket word {"["_1 }

Function closebracket word {"]"_1 }

Function colon word {":"_1 }

Function space word encodeword.[ 32]

Function EOL word encodeword.[ 10]

Function commachar int 44

Function hyphenchar int 45

Function nbspchar int // no break space character // 160

* EQ GT and LT are the possible results of ? operator

Function EQ ordering ordering.1

Function GT ordering ordering.2

Function LT ordering ordering.0

Function true boolean boolean.1

Function false boolean boolean.0

-----------------

Function toint(boolean)int export

Function towords(a:seq.int)seq.word export

Function-(i:int)int 0 - i

Function ?(a:int, b:int)ordering builtin.usemangle

Function ?(a:ordering, b:ordering)ordering toint.a ? toint.b

Function +(a:int, b:int)int builtin.usemangle

Function-(a:int, b:int)int builtin.usemangle

Function *(a:int, b:int)int builtin.usemangle

Function /(a:int, b:int)int builtin.usemangle

Function hash(i:int)int builtin.usemangle

Function =(a:int, b:int)boolean builtin.usemangle

Function =(a:ordering, b:ordering)boolean toint.a = toint.b

Function =(a:boolean, b:boolean)boolean toint.a = toint.b

Function toword(o:ordering)word {"LT EQ GT"_(toint.o + 1)}

Function ∧(a:ordering, b:ordering)ordering 
 let x = a 
  if x = EQ then b else x

--------------------

Function ?(a:boolean, b:boolean)ordering toint.a ? toint.b

Function &and(a:boolean, b:boolean)boolean 
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

type wordencoding is encoding seq.int



type word is record bb:encoding.seq.int

Function encodeword(a:seq.int)word word.encode(a, wordencoding)

Function wordmapping seq.seq.int mapping.wordencoding

Function encoding(w:word)int encoding.bb.w

Function decode(w:word)seq.int decode(bb.w, wordencoding)

Function hash(a:seq.int)int @(+, hash, 0, a)

Function hash(a:seq.word)int @(+, hash, 0, a)

Function hash(a:word)int hash.encoding.a

Function ?(a:word, b:word)ordering encoding.a ? encoding.b

Function =(a:word, b:word)boolean encoding.a = encoding.b

Function ≠(a:word, b:word)boolean export

Function hasdigit(w:word)boolean 
 let l = decode.w 
  between(l_1, 48, 57)∨ l_1 = hyphenchar ∧ length.l > 1 ∧ between(l_2, 48, 57)

covert integer to sequence of characters

Function toword(n:int)word 
 // Covert integer to sequence of characters represented as a single word. // 
  encodeword.toseqint.toUTF8.n

/Function print(i:int)seq.word groupdigits.toUTF8.i

/function groupdigits(u:UTF8)seq.word let s = toseqint.u if length.s < 5 ∧(length.s < 4 ∨ s_1 = hyphenchar)then [ encodeword.s]else groupdigits.UTF8.subseq(s, 1, length.s-3)+ [ encodeword.subseq(s, length.s-2, length.s)]

Function toint(w:word)int 
 // Convert an integer represented as a word to and int // cvttoint(decode.w, 1, 0)

function cvttoint(s:seq.int, i:int, val:int)int 
 if i = 1 ∧ s_1 = hyphenchar 
  then cvttoint(s, i + 1, val)
  else if i > length.s 
  then if s_1 = hyphenchar then-val else val 
  else if s_i = nbspchar 
  then cvttoint(s, i + 1, val)
  else assert between(s_i, 48, 57)report"invalid digit"+ stacktrace 
  cvttoint(s, i + 1, val * 10 + s_i - 48)

Function merge(a:seq.word)word 
 // make multiple words into a single word. // encodeword.@(+, decode, empty:seq.int, a)

Function merge(a:word, b:word)word 
 // make two words into a single word // encodeword(decode.a + decode.b)

Function toUTF8(a:seq.word)UTF8 export

Function^(i:int, n:int)int @(*, identity, 1, constantseq(n, i))

Function pseudorandom(seed:int)int 
 let ah = 16807 
  let mh = 2147483647 
  let test = ah *(seed mod(mh / ah)) - mh mod ah *(seed /(mh / ah))
  if test > 0 then test else test + mh

function addrandom(s:seq.int, i:int)seq.int s + pseudorandom(s_length.s)

Function randomseq(seed:int, length:int)seq.int @(addrandom, identity, [ seed], constantseq(length - 1, 1))

/Function randombytes(i:int)seq.int builtin.usemangle

Function randomint(i:int)seq.int builtin.usemangle

Function lines(a:seq.word, b:seq.word)seq.word a + EOL + b

Function seperator(sep:seq.word, s:seq.word, w:seq.word)seq.word 
 if length.s = 0 then w else s + sep + w

Function seperator(sep:seq.word, s:seq.word, w:word)seq.word 
 // Good for adding commas in seq of words. @(seperator(",", toword,"", [ 1, 2, 3])// 
  if length.s = 0 then [ w]else s + sep + w

Function empty:seq.seq.word export

Function empty:seq.word export

Function empty:seq.int export

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

Function +(seq.seq.word, seq.word)seq.seq.word export

Function +(seq.seq.word, seq.seq.word)seq.seq.word export

Function +(a:seq.word, b:seq.word)seq.word export

* Functions to perform alphabetical sorting

type alphaword is record toword:word

Function alphaword(word)alphaword export

Function toword(alphaword)word export

Function toalphaseq(a:seq.word)seq.alphaword 
 // This is just a type change and the compiler recognizes this and does not generate code // 
  @(+, alphaword, empty:seq.alphaword, a)

Function ?(a:alphaword, b:alphaword)ordering 
 if encoding.toword.a = encoding.toword.b then EQ else decode.toword.a ? decode.toword.b

Function towordseq(a:seq.alphaword)seq.word @(+, toword, empty:seq.word, a)

Function alphasort(a:seq.word)seq.word towordseq.sort.toalphaseq.a

Function alphasort(a:seq.seq.word)seq.seq.word 
 let b = @(+, toalphaseq, empty:seq.seq.alphaword, a)
  @(+, towordseq, empty:seq.seq.word, sort.b)

* usegraph include real oseq textio UTF8 prims stacktrace libscope tree seq blockseq graph ipair invertedseq process stack set oseq packedseq format groupparagraphs fileio

* usegraph include libscope display constant codegen convert altgen parse pass1a pass0 buildtree processtypes definestruct symbol libdescfunc groupparagraphs etype codetemplates core sid pretty pass2 persistant libdesc passcommon main parts llvm reconstruct exclude seq set oseq stdlib tree graph UTF8 stack stacktrace real process libscope ipair

