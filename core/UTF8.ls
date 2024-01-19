Module UTF8

use bits

use seq.byte

use otherseq.char

use standard

Export type:UTF8

Export toseqbyte(UTF8) seq.byte

Export UTF8(seq.byte) UTF8

type UTF8 is toseqbyte:seq.byte

Function length(a:UTF8) int n.toseqbyte.a

Function #(i:int, a:UTF8) byte i#toseqbyte.a

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

Function nbspchar char
{no break space character}
char.160

Function char1(s:seq.word) char
{* First character of first word of s}
1#decodeword.1#s

Function hexOrDecimal?(w:word) word
{checks to see if the first 2 chars indicate the word may be integer in hex or decimal format and returns hex, decimal, or other}
let chars = decodeword.w
let len = n.chars,
if len = 0 then 1#"other"
else
 let i = if len > 1 ∧ 1#chars = char1."-" then 2 else 1
 let firstchar = toint.i#chars,
 if not.between(firstchar, 48, 57) then 1#"other"
 else if firstchar = 48 ∧ len > 2 ∧ 2#chars ∈ decodeword.1#"xX" then 1#"hex"
 else 1#"decimal"

Function toUTF8(n:int) UTF8
UTF8(if n < 0 then [tobyte.toint.hyphenchar] + toUTF8(n, 10) else toUTF8(-n, 10))

function toUTF8(n:int, base:int) seq.byte
{n should always be negative. This is to handle the smallest integer in the twos complement representation of integers}
if base + n > 0 then [tobyte(48 - n)]
else toUTF8(n / base, base) + tobyte(48 + n / base * base - n)

Function encodeUTF8(ch:char) UTF8
{convert to UTF8 byte encoding of unicode character}
let i = toint.ch,
UTF8(if i < 128 then [tobyte.i] else subUTF8(2, i / 64) + tobyte(128 + i mod 64))

function subUTF8(n:int, c:int) seq.byte
if c < 2^(7 - n) then [tobyte(256 - 2^(8 - n) + c)]
else subUTF8(n + 1, c / 64) + tobyte(128 + c mod 64)

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

Function toword(n:int) word
{OPTION NOINLINE COMPILETIME
/br Covert integer to sequence of characters represented as a single word. }
encodeword.decodeUTF8.toUTF8.n

Function toint(w:word) int
{Convert an integer represented as a word to an int}
cvttoint.decodeword.w

Function intlit(s:UTF8) int cvttoint.decodeUTF8.s

Function cvttoint(s:seq.char) int
{Hex values starting with 0x or 0X are allowed. }
if n.s > 2 ∧ 2#s ∈ decodeword.1#"Xx" then
 for b = 0x0, c ∈ s
 do
  let validhex = decodeword.1#"0123456789ABCDEFabcdef"
  let i0 = binarysearch(validhex, c),
  let i = if i0 > 16 then i0 - 6 else i0,
  if i > 0 then b << 4 ∨ bits(i - 1)
  else
   assert c ∈ [char1."x", char1."X", nbspchar] report "invalid hex digit" + encodeword.s,
   b,
 toint.b
else
 let validdigits = decodeword.1#"0123456789"
 for val = 0, c ∈ s
 do
  let i = binarysearch(validdigits, c),
  if i > 0 then val * 10 - (i - 1)
  else
   assert c ∈ [char1."-", nbspchar] report "invalid digit" + encodeword.s + stacktrace,
   val,
 {Since there are more negative numbers in twos-complement we calculate using negative values. }
 if val = 0 ∨ 1#s = char1."-" then val else-val

Function tointseq(a:seq.char) seq.int
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.int, @e ∈ a do acc + toint.@e,
acc

Function tocharseq(a:seq.int) seq.char
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.char, @e ∈ a do acc + char.@e,
acc

Function escapeformat word merge."/ escapeformat" 