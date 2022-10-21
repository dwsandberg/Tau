Module standard

use UTF8

use seq.char

use seq.index

use otherseq.int

use textio

use otherseq.word

use seq.seq.word

use words

use xxhash

Export type:boolean

Export type:char

Export toint(char) int

Export type:index

Export char(int) char

Export index(int) index

Export type:ordering

Export type:UTF8 {From UTF8}

Export toword(n:int) word {Covert integer to a single word. } {From UTF8}

Export toint(w:word) int {Convert an integer represented as a word to an int} {From UTF8}

Export nbspchar char {From UTF8}

Export length(seq.char) int

Export length(seq.int) int

Export length(seq.seq.word) int

Export length(seq.word) int

Export not(a:boolean) boolean {From internal}

Export =(a:boolean, b:boolean) boolean {From internal}

Export false boolean {From internal}

Export true boolean {From internal}

Export _(arithmeticseq.int, int) int {From otherseq.int}

Export arithseq(int, int, int) seq.int {From otherseq.int}

Export constantseq(len:int, element:int) seq.int {From otherseq.int}

Export findindex(seq.word, word) int {From otherseq.word}

Export type:seq.char {From seq.char}

Export isempty(seq.char) boolean {From seq.char}

Export +(seq.char, char) seq.char {From seq.char}

Export +(seq.char, seq.char) seq.char {From seq.char}

Export =(seq.char, seq.char) boolean {From seq.char}

Export _(seq.char, int) char {From seq.char}

Export empty:seq.char seq.char {From seq.char}

Export subseq(seq.char, int, int) seq.char {From seq.char}

Export +(seq.index, index) seq.index {From seq.index}

Export empty:seq.index seq.index {From seq.index}

Export type:seq.int {From seq.int}

Export isempty(seq.int) boolean {From seq.int}

Export last(seq.int) int {From seq.int}

Export +(seq.int, int) seq.int {From seq.int}

Export +(seq.int, seq.int) seq.int {From seq.int}

Export =(seq.int, seq.int) boolean {From seq.int}

Export _(seq.int, int) int {From seq.int}

Export empty:seq.int seq.int {From seq.int}

Export subseq(seq.int, int, int) seq.int {From seq.int}

Export ∈(int, seq.int) boolean {From seq.int}

Export type:seq.seq.word {From seq.seq.word}

Export +(seq.seq.word, seq.seq.word) seq.seq.word {From seq.seq.word}

Export +(seq.seq.word, seq.word) seq.seq.word {From seq.seq.word}

Export _(seq.seq.word, int) seq.word {From seq.seq.word}

Export empty:seq.seq.word seq.seq.word {From seq.seq.word}

Export subseq(seq.seq.word, int, int) seq.seq.word {From seq.seq.word}

Export ∈(seq.word, seq.seq.word) boolean {From seq.seq.word}

Export type:seq.word {From seq.word}

Export first(s:seq.word) word {From seq.word}

Export isempty(seq.word) boolean {From seq.word}

Export last(s:seq.word) word {From seq.word}

Export +(a:seq.word, b:seq.word) seq.word {OPTION COMPILETIME} {From seq.word}

Export +(seq.word, word) seq.word {From seq.word}

Export <<(s:seq.word, i:int) seq.word {* removes i words from beginning of s} {From seq.word}

Export =(seq.word, seq.word) boolean {From seq.word}

Export >>(s:seq.word, i:int) seq.word {* removes i words from end of s} {From seq.word}

Export _(seq.word, int) word {From seq.word}

Export empty:seq.word seq.word {From seq.word}

Export subseq(seq.word, int, int) seq.word {From seq.word}

Export ∈(word, seq.word) boolean {From seq.word}

Export towords(UTF8) seq.word {From textio}

Export encodeword(a:seq.char) word {From words}

Export alphasort(a:seq.seq.word) seq.seq.word {From words}

Export alphasort(a:seq.word) seq.word {From words}

Export merge(a:seq.word) word {make multiple words into a single word. } {From words}

Export type:word {From words}

Export checkinteger(w:word) word
{* returns INTEGER if w can be evaluated as a integer; returns ILLEGAL if w starts out like an integer
 but has illegal characters in it. otherwise returns WORD. }
{From words}

Export decodeword(w:word) seq.char {From words}

Export hash(a:word) int {From words}

Export =(a:word, b:word) boolean {From words}

Export >1(a:word, b:word) ordering {From words}

Builtin stacktrace seq.word

Function dq seq.word {doublequote} [encodeword.[char.34]]

Function dq(s:seq.word) seq.word dq + s + dq

type ordering is toint:int

Function space word encodeword.[char.32]

* EQ GT and LT are the possible results of >1 operator

Function EQ ordering ordering.1

Function GT ordering ordering.2

Function LT ordering ordering.0

Function >1(a:ordering, b:ordering) ordering toint.a >1 toint.b

Function =(a:ordering, b:ordering) boolean toint.a = toint.b

Function toword(o:ordering) word "LT EQ GT"_(toint.o + 1)

Function ∧(a:ordering, b:ordering) ordering if a = EQ then b else a

type boolean is tointx:int

builtin true boolean

builtin false boolean

builtin not(a:boolean) boolean

builtin =(a:boolean, b:boolean) boolean {OPTION COMPILETIME}

Function >1(a:boolean, b:boolean) ordering
if a then if b then {T T} EQ else {T F} GT else if b then {F T} LT else {F F} EQ

Function ∧(a:boolean, b:boolean) boolean if a then b else false

Function ∨(a:boolean, b:boolean) boolean if a then true else b

______________

Function -(i:int) int {OPTION COMPILETIME} 0 - i

Builtin >1(a:int, b:int) ordering

Builtin +(a:int, b:int) int {OPTION COMPILETIME}

Builtin -(a:int, b:int) int {OPTION COMPILETIME}

Builtin *(a:int, b:int) int {OPTION COMPILETIME}

Builtin /(a:int, b:int) int {OPTION COMPILETIME}

Function hash(i:int) int finalmix.hash(hashstart, i)

Builtin =(a:int, b:int) boolean {OPTION COMPILETIME}

--------------------

Function abs(x:int) int if x < 0 then 0 - x else x

Function mod(x:int, y:int) int
if x < 0 then x - x / y * y + y else x - x / y * y

Builtin >(a:int, b:int) boolean {OPTION COMPILETIME}

Function <(a:int, b:int) boolean b > a

Function max(a:int, b:int) int if a > b then a else b

Function min(a:int, b:int) int if a < b then a else b

Function between(i:int, lower:int, upper:int) boolean i ≥ lower ∧ i ≤ upper

Function ^(i:int, n:int) int
{* nth power of i}
for acc = 1, @e ∈ constantseq(n, i) do acc * @e /for (acc)

_______________

Function hash(a:seq.int) int
finalmix.for acc = hashstart, @e ∈ a do hash(acc, @e) /for (acc)

Function hash(a:seq.word) int
finalmix.for acc = hashstart, @e ∈ a do hash(acc, hash.@e) /for (acc)

Function pseudorandom(seed:int) int
let ah = 16807
let mh = 2147483647
let test = ah * (seed mod (mh / ah)) - mh mod ah * (seed / (mh / ah))
if test > 0 then test else test + mh

Function randomseq(seed:int, length:int) seq.int
for acc = [seed], @e ∈ constantseq(length - 1, 1) do acc + pseudorandom.last.acc /for (acc)

Builtin randomint(i:int) seq.int

Function %(n:int) seq.word [toword.n]

Function %(w:word) seq.word [w]

Function break(s:seq.word, seperators:seq.word, includeseperator:boolean) seq.seq.word
let nosep = if includeseperator then 0 else 1
let l = 
 for acc = empty:seq.int, i = 1, e ∈ s do
  next(acc + if e ∈ seperators then [i] else empty:seq.int, i + 1)
 /for (acc)
for acc = empty:seq.seq.word, i = 1, ele ∈ l + (length.s + 1) do
 next(acc + subseq(s, if i = 1 then 1 else l_(i - 1) + nosep, ele - 1)
 , i + 1
 )
/for (acc)

Function extractValue(s:seq.word, name:seq.word) seq.word
for value = ""
, last = "="_1
, p ∈ break(s + "? =", "=", false)
do
 next(if last ∈ name then value + p >> 1 else value
 , if isempty.p then "="_1 else last.p
 )
/for (value)

type char is toint:int

Function =(a:char, b:char) boolean toint.a = toint.b

Function >1(a:char, b:char) ordering toint.a >1 toint.b

Function hash(a:char) int hash.toint.a

type index is rep:int

Function +(i:index, b:int) index index(rep.i + b)

Function toindex(i:int) index
assert i > 0 report "not an index $(stacktrace)"
index(i - 1)

Function toint(i:index) int rep.i + 1 