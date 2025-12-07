Module UTF8

use bits

use seq.byte

use seq1.char

use seq.int

use standard

use word

Export type:UTF8

Export toseqbyte(UTF8) seq.byte

Export UTF8(seq.byte) UTF8

type UTF8 is toseqbyte:seq.byte

Function length(a:UTF8) int n.toseqbyte.a

Function sub(a:UTF8, i:int) byte (toseqbyte.a) sub i

Function emptyUTF8 UTF8 UTF8.empty:seq.byte

Function +(a:UTF8, b:UTF8) UTF8 UTF8(toseqbyte.a + toseqbyte.b)

Function +(a:UTF8, ch:char) UTF8 a + encodeUTF8.ch

Function +(a:UTF8, s:seq.char) UTF8
for acc = a, @e ∈ s do acc + @e,
acc

Function =(a:UTF8, b:UTF8) boolean toseqbyte.a = toseqbyte.b

Function commachar char char.44

Function hyphenchar char char.45

Function periodchar char char.46

Function hexOrDecimal?(w:word) word
{checks to see if the first 2 chars indicate the word may be integer in hex or decimal format and returns hex, decimal, or other}
let chars = decodeword.w
let len = n.chars,
if len = 0 then "other" sub 1
else
 let i = if len > 1 ∧ chars sub 1 = char1."-" then 2 else 1
 let firstchar = toint.chars sub i,
 if not.between(firstchar, 48, 57) then if len > 1 ∧ char1."'" = chars sub 1 then "word" sub 1 else "other" sub 1
 else if firstchar = 48 ∧ len > 2 ∧ chars sub 2 ∈ decodeword."xX" sub 1 then "hex" sub 1
 else "decimal" sub 1

Function toUTF8(n:int) UTF8
for acc = empty:seq.byte, e ∈ tochars.n do acc + tobyte.toint.e,
UTF8.acc

Function encodeUTF8(ch:char) UTF8
{convert to UTF8 byte encoding of unicode character}
let i = toint.ch,
UTF8(
 if i < 128 then [tobyte.i]
 else
  for acc = [tobyte(128 + i mod 64)], t = 32, c = i / 64
  while c ≥ t
  do next([tobyte(128 + c mod 64)] + acc, t / 2, c / 64),
  [tobyte(256 - 2 * t + c)] + acc
)

Function decodeUTF8(b:UTF8) seq.char
{converts UTF-8 encoded sequence into a sequence of chars}
for state = 0, val = 0, result = empty:seq.int, x0 ∈ toseqbyte.b
do
 let x = toint.x0,
 if state = 0 then
  if x < 128 then next(0, 0, result + x)
  else if x < 224 then next(1, (x - 192) * 64, result)
  else if x < 240 then next(2, (x - 224) * 64, result)
  else if x < 248 then next(3, (x - 240) * 64, result)
  else if x < 252 then next(4, (x - 248) * 64, result)
  else next(5, (x - 252) * 64, result)
 else if state = 1 then next(0, 0, result + (x + val - 128))
 else next(state - 1, (val + (x - 128)) * 64, result),
tocharseq.result

Function intlit(s:UTF8) int cvttoint.decodeUTF8.s

Function tointseq(a:seq.char) seq.int
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.int, @e ∈ a do acc + toint.@e,
acc

Function tocharseq(a:seq.int) seq.char
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.char, @e ∈ a do acc + char.@e,
acc

Function escapeformat word merge."/ escapeformat" 