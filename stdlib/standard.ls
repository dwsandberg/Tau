Module standard


use UTF8

use encoding.seq.char

use seq.char

use otherseq.int

use seq.seq.int

use seq.int

use otherseq.word

use seq.seq.word

use seq.word

use words

use xxhash

/Function type:int(a:int) int a

type ordering is record toint:int

type boolean is record toint:int

* Useful constants

Function space word encodeword.[ char.32]

* EQ GT and LT are the possible results of ? operator

Function EQ ordering ordering.1

Function GT ordering ordering.2

Function LT ordering ordering.0

Function true boolean boolean.1

Function false boolean boolean.0

-----------------

Export toint(boolean)int

Function-(i:int)int 0 - i

Builtin ?(a:int, b:int)ordering

Function ?(a:ordering, b:ordering)ordering toint.a ? toint.b

Builtin +(a:int, b:int)int

Builtin-(a:int, b:int)int

Builtin *(a:int, b:int)int

Builtin /(a:int, b:int)int

Function hash(i:int)int finalmix.hash(hashstart, i)

Builtin =(a:int, b:int)boolean

Function =(a:ordering, b:ordering)boolean toint.a = toint.b

Function =(a:boolean, b:boolean)boolean toint.a = toint.b

Function toword(o:ordering)word"LT EQ GT"_(toint.o + 1)

Function ∧(a:ordering, b:ordering)ordering
 let x = a
  if x = EQ then b else x

--------------------

Function ?(a:boolean, b:boolean)ordering toint.a ? toint.b

Function ∧(a:boolean, b:boolean)boolean if a then b else // false // boolean.0

Function ∨(a:boolean, b:boolean)boolean
 if a then // true is not use so simple inline expansion is used to produce short circuit evaluation // boolean.1 else b

 
Builtin not(a:boolean)boolean

Function abs(x:int)int if x < 0 then 0 - x else x

Function mod(x:int, y:int)int
 if x < 0 then x - x / y * y + y
 else x - x / y * y

Builtin >(a:int, b:int)boolean

Function <(a:int, b:int)boolean b > a

Function max(a:int, b:int)int if a > b then a else b

Function min(a:int, b:int)int if a < b then a else b

Function between(i:int, lower:int, upper:int)boolean i ≥ lower ∧ i ≤ upper

---------------------------

Function hash(a:seq.int)int finalmix(a @ hash(hashstart, @e))

Function hash(a:seq.word)int finalmix(a @ hash(hashstart, hash.@e))

Function^(i:int, n:int)int constantseq(n, i) @ *(1, @e)

Function pseudorandom(seed:int)int
 let ah = 16807
 let mh = 2147483647
 let test = ah * (seed mod (mh / ah)) - mh mod ah * (seed / (mh / ah))
  if test > 0 then test else test + mh

function addrandom(s:seq.int, i:int)seq.int s + pseudorandom.s_(length.s)

Function randomseq(seed:int, length:int)seq.int constantseq(length - 1, 1) @ addrandom([ seed], @e)

Builtin randomint(i:int)seq.int

Function list(a:seq.word,b:seq.word,c:seq.word) seq.word
 if isempty.a then c else if isempty.c then a else a + (b + c)

  Function EOL seq.word "&br"  

Export hash(a:word)int

Export ?(a:word, b:word)ordering

Export =(a:word, b:word)boolean

Export toword(n:int)word // Covert integer to a single word. //

Export toint(w:word)int // Convert an integer represented as a word to an int //

Export merge(a:seq.word)word // make multiple words into a single word. //

Export type:ordering

Export type:boolean

Export type:word

Export type:seq.word

Export type:seq.seq.word

Export type:seq.int

Export type:seq.char

Export type:encoding.seq.char

Export empty:seq.seq.word seq.seq.word

Export empty:seq.word seq.word

Export empty:seq.int seq.int

Export arithseq(int, int, int)seq.int

Export constantseq(len:int, element:int)seq.int

Export_(seq.word, int)word

Export_(seq.seq.word, int)seq.word

Export_(seq.int, int)int

Export length(seq.word)int

Export length(seq.seq.word)int

Export length(seq.int)int

Export findindex(word, seq.word)int

Export findindex(word, seq.word, int)int

Export last(s:seq.word)word

Export first(s:seq.word) word

Export subseq(seq.seq.word, int, int)seq.seq.word

Export subseq(seq.word, int, int)seq.word

Export subseq(seq.int, int, int)seq.int

Export ∈(word, seq.word)boolean

Export ∈(seq.word, seq.seq.word)boolean

Export ∈(int, seq.int)boolean

Export =(seq.word, seq.word)boolean

Export =(seq.int, seq.int)boolean

Export +(seq.word, word)seq.word

Export +(seq.int, seq.int)seq.int

Export +(seq.int, int)seq.int

Export last(seq.int)int

Export +(seq.seq.word, seq.word)seq.seq.word

Export +(seq.seq.word, seq.seq.word)seq.seq.word

Export +(a:seq.word, b:seq.word)seq.word

Export nbspchar char

Export alphasort(a:seq.word)seq.word

Export alphasort(a:seq.seq.word)seq.seq.word

type char is record toint:int

Function =(a:char, b:char)boolean toint.a = toint.b

Function ?(a:char, b:char)ordering toint.a ? toint.b

Function hash(a:char)int hash.toint.a

Export type:char

Export type:seq.char

Export length(seq.char)int

Export empty:seq.char seq.char

Export +(seq.char, seq.char)seq.char

Export isempty(seq.char)boolean

Export isempty(seq.word)boolean

Export isempty(seq.int)boolean


Export_(seq.char, int)char

Export_(pseq.char, int)char

Export subseq(seq.char, int, int)seq.char

Export =(seq.char, seq.char)boolean

Export +(seq.char, char)seq.char

Export toint(char)int

Export char(int)char

Function char1(s:seq.word)char(decodeword.s_1)_1

Export encodeword(a:seq.char)word

Export decodeword(w:word)seq.char

Export print(decimals:int, rin:real)seq.word

Export checkinteger(w:word)word

Export << (s:seq.word, i:int) seq.word   
           
Export >> (s:seq.word , i:int) seq.word   

* usegraph include xxhash encoding bits words real subreal stacktrace textio reconstruct UTF8 seq otherseq fileio standard 
exclude standard seq

* usegraph include prims tree graph ipair libscope internalbc process stack set format groupparagraphs bitpackedseq maindict worddict 
exclude standard seq

* usegraph include main2 libscope display constant codegen convert parse pass1 symbol libdesc codetemplates pass2 
persistant llvm postbind reconstruct persistantseq opt2 symbol parse libdesc internalbc 
intercode cvttoinst codegen pass2new codegennew funcsig interpreter
exclude seq set otherseq standard bits tree graph UTF8 stack stacktrace real ipair bitpackedseq 
fileio textio encoding words 

*