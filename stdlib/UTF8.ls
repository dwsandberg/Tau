Module UTF8

use bits

use standard

use otherseq.byte

use otherseq.char

use otherseq.int

use seq.seq.char

type UTF8 is toseqbyte:seq.byte

Function length(a:UTF8)int length.toseqbyte.a

Function _(a:UTF8, i:int)byte(toseqbyte.a)_i

Export type:UTF8

Export UTF8(seq.byte)UTF8

Export toseqbyte(UTF8)seq.byte

Function emptyUTF8 UTF8 UTF8.empty:seq.byte

Function +(a:UTF8, b:UTF8)UTF8 UTF8(toseqbyte.a + toseqbyte.b)

Function +(a:UTF8, ch:char)UTF8 a + encodeUTF8.ch

Function +(a:UTF8, s:seq.char)UTF8 for acc = a, @e ∈ s do acc + @e /for(acc)

Function =(a:UTF8, b:UTF8)boolean toseqbyte.a = toseqbyte.b

Function commachar char char.44

Function hyphenchar char char.45

Function periodchar char char.46

Function doublequotechar char char.34

Function nbspchar char{no break space character}char.160

Function toUTF8(n:int)UTF8
UTF8.if n < 0 then[tobyte.toint.hyphenchar] + toUTF8(n, 10)else toUTF8(-n, 10)

function toUTF8(n:int, base:int)seq.byte
{n should always be negative.This is to handle the smallest integer in the twos complement representation of integers}
if base + n > 0 then[tobyte(48 - n)]
else toUTF8(n / base, base) + tobyte(48 + n / base * base - n)

Function encodeUTF8(ch:char)UTF8
{convert to UTF8 byte encoding of unicode character}
let i = toint.ch
UTF8.if i < 128 then[tobyte.i]else subUTF8(2, i / 64) + tobyte(128 + i mod 64)

function subUTF8(n:int, c:int)seq.byte
if c < 2^(7 - n)then[tobyte(256 - 2^(8 - n) + c)]
else subUTF8(n + 1, c / 64) + tobyte(128 + c mod 64)

Function decodeUTF8(b:UTF8)seq.char
{converts UTF8 encoded sequence into a sequence of integers(chars)}decodeUTF8(b, 1, length.b)

Function decodeUTF8(a:UTF8, start:int, finish:int)seq.char
tocharseq.xx(toseqbyte.a, max(1, start), min(finish, length.toseqbyte.a), empty:seq.int)

function xx(b:seq.byte, i:int, finish:int, result:seq.int)seq.int
if i > finish then result
else
 let x = toint.b_i
 if x < 128 then xx(b, i + 1, finish, result + x)
 else if x < 224 then xx(b, i + 2, finish, result + ((x - 194) * 64 + toint.b_(i + 1)))
 else if x < 240 then
  xx(b, i + 3, finish, result + ((x - 224) * 64^2 + (toint.b_(i + 1) - 128) * 64 + toint.b_(i + 2) - 128))
 else if x < 248 then
  xx(b
  , i + 4
  , finish
  , result + ((x - 240) * 64^3 + (toint.b_(i + 1) - 128) * 64^2 + (toint.b_(i + 2) - 128) * 64 + toint.b_(i + 3) - 128)
  )
 else if x < 252 then
  xx(b
  , i + 5
  , finish
  , result
  + ((x - 248) * 64^4 + (toint.b_(i + 1) - 128) * 64^3 + (toint.b_(i + 2) - 128) * 64^2 + (toint.b_(i + 3) - 128) * 64
  + toint.b_(i + 4)
  - 128)
  )
 else
  xx(b
  , i + 6
  , finish
  , result
  + ((x - 252) * 64^5 + (toint.b_(i + 1) - 128) * 64^4 + (toint.b_(i + 2) - 128) * 64^3 + (toint.b_(i + 3) - 128) * 64^2
  + (toint.b_(i + 4) - 128) * 64
  + toint.b_(i + 5)
  - 128)
  )

---------

Function toword(n:int)word
{OPTION NOINLINE COMPILETIME}
{Covert integer to sequence of characters represented as a single word. }encodeword.decodeUTF8.toUTF8.n

Function toint(w:word)int{Convert an integer represented as a word to an int}cvttoint.decodeword.w

Function intlit(s:UTF8)int cvttoint.decodeUTF8.s

Function cvttoint(s:seq.char)int
{Hex values starting with 0x or 0X are allowed. }
if length.s > 2 ∧ s_2 ∈ decodeword.first."Xx"then
 toint.for b = 0x0, c ∈ s do
  let validhex = decodeword.first."0123456789ABCDEFabcdef"
  let i0 = binarysearch(validhex, c)
  let i = if i0 > 16 then i0 - 6 else i0
  if i > 0 then b << 4 ∨ bits(i - 1)
  else
   assert c ∈ [char1."x", char1."X", nbspchar]
   report"invalid hex digit" + encodeword.s
   b
 /for(b)
else
 let validdigits = decodeword.first."0123456789"
 let val = 
  for val = 0, c ∈ s do
   let i = binarysearch(validdigits, c)
   if i > 0 then val * 10 - (i - 1)
   else
    assert c ∈ [char1."-", nbspchar]report"invalid digit" + encodeword.s + stacktrace
    val
  /for(val)
 {Since there are more negative numbers in twos-complement we calculate using negative values. }
 if val = 0 ∨ s_1 = char1."-"then val else-val

-------------

Function tointseq(a:seq.char)seq.int
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.int, @e ∈ a do acc + toint.@e /for(acc)

Function tocharseq(a:seq.int)seq.char
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.char, @e ∈ a do acc + char.@e /for(acc)

_________________

___________

Function toUTF8(a:seq.word)UTF8 toUTF8(a, empty:seq.seq.char, true)

Function toUTF8(s:seq.word, format:seq.seq.char, nospacein:boolean)UTF8
let handle/br = length.format < 126
{nospace means add no space before word}
for result = emptyUTF8, nospace = nospacein, this ∈ s do
 if this = " /br"_1 ∧ handle/br then next(result + char.10, true)
 else if this = ", "_1 then
  {no space before but space after}next(result + char1.", " + char.32, true)
 else
  let chars = decodeword.this
  if length.chars = 1 ∧ first.chars ∈ decodeword.merge.'={}+-()[].:"_^' then
   {no space before or after}next(result + chars, true)
  else if length.chars = 1 ∧ first.chars = char.32 then
   if 32 ≤ length.format ∧ length.format_32 > 1 then
    next(if nospace then result + format_32 else result + char.32 + format_32, false)
   else next(result + chars, true)
  else if chars = [char1.".", char.32]then{no space before or after}next(result + chars, true)
  else
   let d = 
    for acc = emptyUTF8, ch ∈ chars do
     if not.between(toint.ch, 1, length.format)then acc + ch else acc + format_(toint.ch)
    /for(acc)
   next(if nospace then result + d else result + char.32 + d, false)
/for(result) 