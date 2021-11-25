Module standard

use UTF8

use bits

use index

use inputoutput

use textio

use words

use xxhash

use seq.bit

use seq.byte

use seq.char

use otherseq.int

use otherseq.word

use encoding.seq.char

use seq.seq.int

use seq.seq.word

Export stacktrace seq.word

type ordering is toint:int

Export type:ordering

Function space word encodeword.[ char.32]

* EQ GT and LT are the possible results of ? operator

Function EQ ordering ordering.1

Function GT ordering ordering.2

Function LT ordering ordering.0

Function ?(a:ordering, b:ordering)ordering toint.a ? toint.b

Function =(a:ordering, b:ordering)boolean toint.a = toint.b

Function toword(o:ordering)word"LT EQ GT"_(toint.o + 1)

Function ∧(a:ordering, b:ordering)ordering if a = EQ then b else a

-----------------

type boolean is tointx:int

Export type:boolean

Export true boolean

builtin true boolean

Export false boolean

builtin false boolean

builtin not(a:boolean)boolean

Export not(a:boolean)boolean

builtin=(a:boolean, b:boolean)boolean

Export=(a:boolean, b:boolean)boolean

Function ?(a:boolean, b:boolean)ordering
if a then if b then { T T } EQ else { T F } GT
else if b then { F T } LT else { F F } EQ

Function ∧(a:boolean, b:boolean)boolean if a then b else false

Function ∨(a:boolean, b:boolean)boolean if a then true else b

______________

Function -(i:int)int 0 - i

Builtin ?(a:int, b:int)ordering

Builtin+(a:int, b:int)int

Builtin-(a:int, b:int)int

Builtin *(a:int, b:int)int

Builtin /(a:int, b:int)int

Function hash(i:int)int finalmix.hash(hashstart, i)

Builtin=(a:int, b:int)boolean

--------------------

Function abs(x:int)int if x < 0 then 0 - x else x

Function mod(x:int, y:int)int if x < 0 then x - x / y * y + y else x - x / y * y

Builtin >(a:int, b:int)boolean

Function <(a:int, b:int)boolean b > a

Function max(a:int, b:int)int if a > b then a else b

Function min(a:int, b:int)int if a < b then a else b

Function between(i:int, lower:int, upper:int)boolean i ≥ lower ∧ i ≤ upper

Function ^(i:int, n:int)int
{ * nth power of i } for acc = 1, @e ∈ constantseq(n, i)do acc * @e /for(acc)

---------------------

Export getfile:byte(name:seq.word)seq.byte

Export getfile:bit(name:seq.word)seq.bit

Export getfile:int(name:seq.word)seq.int

Export gettext(filename:seq.word)seq.seq.word breakparagraph.UTF8.getfile:byte(filename)

Function createfile(filename:seq.word, s:seq.word)int createfile(filename, toseqbyte.toUTF8.s)

Export createfile(name:seq.word, a:seq.byte)int

Export createfile(name:seq.word, a:seq.int)int

_______________

Function hash(a:seq.int)int finalmix.for acc = hashstart, @e ∈ a do hash(acc, @e)/for(acc)

Function hash(a:seq.word)int finalmix.for acc = hashstart, @e ∈ a do hash(acc, hash.@e)/for(acc)

Function pseudorandom(seed:int)int
let ah = 16807
let mh = 2147483647
let test = ah * (seed mod (mh / ah)) - mh mod ah * (seed / (mh / ah))
if test > 0 then test else test + mh

Function randomseq(seed:int, length:int)seq.int
for acc = [ seed], @e ∈ constantseq(length - 1, 1)do acc + pseudorandom.last.acc /for(acc)

Export randomint(i:int)seq.int

Function print(n:int)seq.word
let s = decodeUTF8.toUTF8.n
let sign = if n < 0 then"-"else""
let t = if n < 0 then s << 1 else s
sign
+ encodeword.if length.s < 5 then s
else
 for acc = empty:seq.char, i = 1, e ∈ s do
  next(acc + if(length.s - i) mod 3 = 2 ∧ i ≠ 1 then [ char.160, e]else [ e], i + 1)
 /for(acc)

Function EOL seq.word" /br"

Function break(s:seq.word, seperators:seq.word, includeseperator:boolean)seq.seq.word
let nosep = if includeseperator then 0 else 1
let l = 
 for acc = empty:seq.int, i = 1, e ∈ s do
  next(acc + if e ∈ seperators then [ i]else empty:seq.int, i + 1)
 /for(acc)
for acc = empty:seq.seq.word, i = 1, ele ∈ l + (length.s + 1)do
 next(acc + subseq(s, if i = 1 then 1 else l_(i - 1) + nosep, ele - 1), i + 1)
/for(acc)

Export hash(a:word)int

Export ?(a:word, b:word)ordering

Export=(a:word, b:word)boolean

Export toword(n:int)word { Covert integer to a single word. }

Export toint(w:word)int { Convert an integer represented as a word to an int }

Export merge(a:seq.word)word { make multiple words into a single word. }

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

Export_(arithmeticseq.int, int)int

Export constantseq(len:int, element:int)seq.int

Export_(seq.word, int)word

Export_(seq.seq.word, int)seq.word

Export_(seq.int, int)int

Export length(seq.word)int

Export length(seq.seq.word)int

Export length(seq.int)int

Export findindex(word, seq.word)int

Export last(s:seq.word)word

Export first(s:seq.word)word

Export subseq(seq.seq.word, int, int)seq.seq.word

Export subseq(seq.word, int, int)seq.word

Export subseq(seq.int, int, int)seq.int

Export ∈(word, seq.word)boolean

Export ∈(seq.word, seq.seq.word)boolean

Export ∈(int, seq.int)boolean

Export=(seq.word, seq.word)boolean

Export=(seq.int, seq.int)boolean

Export+(seq.word, word)seq.word

Export+(seq.int, seq.int)seq.int

Export+(seq.int, int)seq.int

Export last(seq.int)int

Export+(seq.seq.word, seq.word)seq.seq.word

Export+(seq.seq.word, seq.seq.word)seq.seq.word

Export+(a:seq.word, b:seq.word)seq.word

Export nbspchar char

Export alphasort(a:seq.word)seq.word

Export alphasort(a:seq.seq.word)seq.seq.word

type char is toint:int

Function =(a:char, b:char)boolean toint.a = toint.b

Function ?(a:char, b:char)ordering toint.a ? toint.b

Function hash(a:char)int hash.toint.a

Export type:char

Export type:seq.char

Export length(seq.char)int

Export empty:seq.char seq.char

Export+(seq.char, seq.char)seq.char

Export isempty(seq.char)boolean

Export isempty(seq.word)boolean

Export isempty(seq.int)boolean

Export_(seq.char, int)char

Export subseq(seq.char, int, int)seq.char

Export=(seq.char, seq.char)boolean

Export+(seq.char, char)seq.char

Export toint(char)int

Export char(int)char

Function char1(s:seq.word)char({ * First character of first word of s } decodeword.s_1)_1

Export encodeword(a:seq.char)word

Export decodeword(w:word)seq.char

Export print(decimals:int, rin:real)seq.word

Export checkinteger(w:word)word { * returns INTEGER if w can be evaluated as a integer; returns ILLEGAL if w starts out like an integer but has illegal characters in it. otherwise returns WORD. }

Export <<(s:seq.word, i:int)seq.word { removes i words from beginning of s }

Export >>(s:seq.word, i:int)seq.word { removes i words from end of s }

* usegraph include inputoutput xxhash encoding bits words real textio UTF8 set seq otherseq fileio standard bitstream 
 exclude standard seq

* usegraph include tree graph  process stack set format maindict tausupport program typedict mytype symbol exclude 
 standard seq bits otherseq

* usegraph include codetemplates codegennew internalbc llvmconstant llvm interpreter mangle persistant libdesc exclude 
 seq bits set otherseq standard UTF8 real stack

* usegraph include compilerfront main2 display parse passparse passsymbol pass2 postbind pass2 program typedict exclude 
 seq set otherseq standard bits graph UTF8 stack real fileio textio encoding words symbol types

Export type:index

Export+(i:index, b:int)index index(rep.i+b)

Export toindex(i:int)index assert i > 0 report"not a index"index(i-1)

Export toint(i:index)int rep.i+1 