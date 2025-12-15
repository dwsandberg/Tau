Module standard

use bits

use seq1.char

use seq.char

use sort.char

use seq1.int

use kernal

use word

use seq1.word

use seq.seq.word

Export char1(s:seq.word) char

Export type:boolean

Export type:char

Export toint(char) int

Export char(int) char

Export type:ordering

Export toword(n:int) word{Covert integer to a single word.}{From UTF8}

Export toint(w:word) int{Convert an integer represented as a word to an int}{From UTF8}

Export not(a:boolean) boolean{From internal}

Export =(a:boolean, b:boolean) boolean{From internal}

Export false boolean{From internal}

Export true boolean{From internal}

Export arithseq(int, int, int) seq.int{From seq1.int}

Export constantseq(len:int, element:int) seq.int{From seq1.int}

Export findindex(seq.word, word) int{From seq1.word}

Export type:seq.char{From seq.char}

Export isempty(seq.char) boolean{From seq.char}

Export n(seq.char) int{From seq.char}

Export sub(seq.char, int) char{From seq.char}

Export +(seq.char, char) seq.char{From seq.char}

Export +(seq.char, seq.char) seq.char{From seq.char}

Export =(seq.char, seq.char) boolean{From seq.char}

Export empty:seq.char seq.char{From seq.char}

Export subseq(seq.char, int, int) seq.char{From seq.char}

Export type:seq.int{From seq.int}

Export isempty(seq.int) boolean{From seq.int}

Export n(seq.int) int{From seq.int}

Export sub(seq.int, int) int{From seq.int}

Export +(seq.int, int) seq.int{From seq.int}

Export +(seq.int, seq.int) seq.int{From seq.int}

Export =(seq.int, seq.int) boolean{From seq.int}

Export empty:seq.int seq.int{From seq.int}

Export subseq(seq.int, int, int) seq.int{From seq.int}

Export ∈(int, seq.int) boolean{From seq.int}

Export type:seq.seq.word{From seq.seq.word}

Export n(seq.seq.word) int{From seq.seq.word}

Export sub(seq.seq.word, int) seq.word{From seq.seq.word}

Export +(seq.seq.word, seq.seq.word) seq.seq.word{From seq.seq.word}

Export +(seq.seq.word, seq.word) seq.seq.word{From seq.seq.word}

Export empty:seq.seq.word seq.seq.word{From seq.seq.word}

Export subseq(seq.seq.word, int, int) seq.seq.word{From seq.seq.word}

Export ∈(seq.word, seq.seq.word) boolean{From seq.seq.word}

Export type:seq.word{From seq.word}

Export isempty(seq.word) boolean{From seq.word}

Export n(seq.word) int{From seq.word}

Export sub(seq.word, int) word{From seq.word}

Export +(a:seq.word, b:seq.word) seq.word{OPTION COMPILETIME}{From seq.word}

Export +(seq.word, word) seq.word{From seq.word}

Export <<(s:seq.word, i:int) seq.word
{* removes i words from beginning of s From seq.word}{From seq.word}

Export =(seq.word, seq.word) boolean{From seq.word}

Export >>(s:seq.word, i:int) seq.word{* removes i words from end of s}{From seq.word}

Export last(seq.word) word

Export empty:seq.word seq.word{From seq.word}

Export subseq(seq.word, int, int) seq.word{From seq.word}

Export ∈(word, seq.word) boolean{From seq.word}

Export encodeword(a:seq.char) word{From word}

Export merge(a:seq.word) word{make multiple word into a single word.}{From word}

Export type:word{From word}

Export decodeword(w:word) seq.char{From word}

Export hash(a:word) int{From word}

Export =(a:word, b:word) boolean{From word}

Export >1(a:word, b:word) ordering{From word}

Export stacktrace seq.word

Function dq seq.word
{doublequote}
[encodeword.[char.34]]

Function dq(s:seq.word) seq.word dq + s + dq

Export >1(char, char) ordering

Export =(char, char) boolean

Export EQ ordering

Export GT ordering

Export LT ordering

Export =(ordering, ordering) boolean

Function ∧(a:ordering, b:ordering) ordering if a = EQ then b else a

Function >1(a:boolean, b:boolean) ordering
if a then if b then {T T}EQ else {T F}GT
else if b then {F T}LT
else {F F}EQ

Export ∧(a:boolean, b:boolean) boolean

Export ∨(a:boolean, b:boolean) boolean

-------------------------------

Export -(i:int) int

Export >1(a:int, b:int) ordering

Export +(a:int, b:int) int

Export -(a:int, b:int) int

Export *(a:int, b:int) int

Export /(a:int, b:int) int

Export =(a:int, b:int) boolean

--------------------

Export abs(x:int) int

Export mod(x:int, y:int) int

Export >(a:int, b:int) boolean

Export <(a:int, b:int) boolean

Export between(i:int, lower:int, upper:int) boolean

Export sup(i:int, n:int) int

Export max(a:int, b:int) int

Export min(a:int, b:int) int

-------------------------------

Export hash(a:seq.int) int

Export hash(a:seq.word) int

Function randomseq(seed:int, length:int) seq.int
{Xorshift* see Wikapedia entry on Xorshift}
for acc = empty:seq.int, state = bits.seed
while n.acc < length
do
 let x1 = state ⊻ state >> 12
 let x2 = x1 ⊻ x1 << 25,
 let nextrandom = x2 ⊻ x2 >> 27,
 next(acc + toint.state * toint.0x2545F4914F6CDD1D, nextrandom)
{???? omitting acc gives strange error message}
acc

Function break(s:seq.word, seperators:seq.word, includeseperator:boolean) seq.seq.word
let nosep = if includeseperator then 0 else 1
for l = empty:seq.int, j = 1, e ∈ s
do next(l + (if e ∈ seperators then [j] else empty:seq.int), j + 1)
for acc = empty:seq.seq.word, i = 1, ele ∈ l + (n.s + 1)
do next(acc + subseq(s, if i = 1 then 1 else l sub (i - 1) + nosep, ele - 1), i + 1),
acc

Function extractValue(s:seq.word, name:seq.word) seq.word
for value = "", invalue = false, last = "?" sub 1, found = false, w ∈ s
while not.found
do
 if invalue then
  if w ∈ ": :" then next(value >> 1, invalue, w, true)
  else next(value + w, invalue, w, false)
 else if w ∈ ": :" ∧ last ∈ name then next(value, true, w, false)
 else next(value, false, w, false),
value

Function extractFlag(s:seq.word, name:seq.word) boolean
for value = "", invalue = false, last = "?" sub 1, found = false, w ∈ s
while not.found
do
 if invalue then
  if w ∈ ": :" then next(value >> 1, invalue, w, true)
  else next(value + w, invalue, w, false)
 else if w ∈ ": :" ∧ last ∈ name then next(value, true, w, false)
 else next(value, false, w, false),
found ∧ value ≠ "false"

function hexdigit(b:bits) char
let k = decodeword."0123456789ABCDEF" sub 1
assert n.k = 16 report "XXX:(n.k)",
k sub (1 + toint(b ∧ 0x0F))

function hexword(b:bits) word
encodeword.[hexdigit(b >> 12), hexdigit(b >> 8), hexdigit(b >> 4), hexdigit.b]

Function %(b:bits) seq.word
[hexword(b >> 48), hexword(b >> 32), hexword(b >> 16), hexword.b]

Function %(b:byte) seq.word [encodeword.[hexdigit(tobits.b >> 4), hexdigit.tobits.b]]

Function %(n:int) seq.word [toword.n]

Function %(w:word) seq.word [w]

Function %(b:boolean) seq.word if b then "true" else "false"

Function %(o:ordering) seq.word ["LT EQ GT" sub (toint.o + 1)]

Function >alpha(a:word, b:word) ordering
if a = b then EQ else decodeword.a >alpha decodeword.b

Export type:word

Function >alpha(a:char, b:char) ordering a >1 b

use seq.int

Function seqseg2(s:seq.int, i:int) pseq.int seqseg(s, i)

Function red(s:seq.word) seq.word "//:(s)/literal" 