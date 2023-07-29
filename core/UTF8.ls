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

Function _(i:int, a:UTF8) byte i_toseqbyte.a

Function emptyUTF8 UTF8 UTF8.empty:seq.byte

Function +(a:UTF8, b:UTF8) UTF8 UTF8(toseqbyte.a + toseqbyte.b)

Function +(a:UTF8, ch:char) UTF8 a + encodeUTF8.ch

Function +(a:UTF8, s:seq.char) UTF8 for acc = a, @e ∈ s do acc + @e, acc

Function =(a:UTF8, b:UTF8) boolean toseqbyte.a = toseqbyte.b

Function commachar char char.44

Function hyphenchar char char.45

Function periodchar char char.46

Function nbspchar char {no break space character} char.160

Function char1(s:seq.word) char {* First character of first word of s} 1_decodeword.1_s

Function toUTF8(n:int) UTF8
UTF8.if n < 0 then [tobyte.toint.hyphenchar] + toUTF8(n, 10) else toUTF8(-n, 10)

function toUTF8(n:int, base:int) seq.byte
{n should always be negative. This is to handle the smallest integer in the twos complement representation of integers}
if base + n > 0 then
[tobyte(48 - n)]
else toUTF8(n / base, base) + tobyte(48 + n / base * base - n)

Function encodeUTF8(ch:char) UTF8
{convert to UTF8 byte encoding of unicode character}
let i = toint.ch,
UTF8.if i < 128 then [tobyte.i] else subUTF8(2, i / 64) + tobyte(128 + i mod 64)

function subUTF8(n:int, c:int) seq.byte
if c < 2^(7 - n) then
[tobyte(256 - 2^(8 - n) + c)]
else subUTF8(n + 1, c / 64) + tobyte(128 + c mod 64)

Function decodeUTF8(b:UTF8) seq.char
{converts UTF-8 encoded sequence into a sequence of chars}
for state = 0, val = 0, result = empty:seq.int, x0 ∈ toseqbyte.b
do
 let x = toint.x0,
  if state = 0 then
   if x < 128 then
   next(0, 0, result + x)
   else if x < 224 then
   next(1, (x - 192) * 64, result)
   else if x < 240 then
   next(2, (x - 224) * 64, result)
   else if x < 248 then
   next(3, (x - 240) * 64, result)
   else if x < 252 then
   next(4, (x - 248) * 64, result)
   else next(5, (x - 252) * 64, result)
  else if state = 1 then
  next(0, 0, result + (x + val - 128))
  else next(state - 1, (val + (x - 128)) * 64, result)
,
tocharseq.result

Function toword(n:int) word
{OPTION NOINLINE COMPILETIME /br Covert integer to sequence of characters represented as a single word. }
encodeword.decodeUTF8.toUTF8.n

Function toint(w:word) int
{Convert an integer represented as a word to an int}
cvttoint.decodeword.w

Function intlit(s:UTF8) int cvttoint.decodeUTF8.s

Function cvttoint(s:seq.char) int
{Hex values starting with 0x or 0X are allowed. }
if n.s > 2 ∧ 2_s ∈ decodeword.1_"Xx" then
 for b = 0x0, c ∈ s
 do
  let validhex = decodeword.1_"0123456789ABCDEFabcdef"
  let i0 = binarysearch(validhex, c)
  let i = if i0 > 16 then i0 - 6 else i0,
   if i > 0 then
   b << 4 ∨ bits(i - 1)
   else
    assert c ∈ [char1."x", char1."X", nbspchar] report "invalid hex digit" + encodeword.s,
    b
 ,
 toint.b
else
 let validdigits = decodeword.1_"0123456789"
 for val = 0, c ∈ s
 do
  let i = binarysearch(validdigits, c),
   if i > 0 then
   val * 10 - (i - 1)
   else
    assert c ∈ [char1."-", nbspchar] report "invalid digit" + encodeword.s + stacktrace,
    val
 {Since there are more negative numbers in twos-complement we calculate using negative values. }
 if val = 0 ∨ 1_s = char1."-" then val else -val

Function tointseq(a:seq.char) seq.int
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.int, @e ∈ a do acc + toint.@e,
acc

Function tocharseq(a:seq.int) seq.char
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.char, @e ∈ a do acc + char.@e,
acc

Function tocharseq2(a:seq.int) seq.char
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.char, @e ∈ a do acc + char.@e,
acc

Function toUTF8(s:seq.word) UTF8 {OPTION INLINE} toUTF83(s, false)

Function escapeformat word merge."/ escapeformat"

Function toUTF83(s:seq.word, escapehtml:boolean) UTF8
{OPTION INLINE /br nospace means add no space before word
 /br if the first character of a multi-character word is char.0 then the character is discarded.
 /br This is to allow format with format meaning to be escaped.}
for cmd = true, result = emptyUTF8, nospace = true, this ∈ s
do
 let chars = decodeword.this,
  if n.chars = 1 then
   let ch = 1_chars,
    if ch ∈ (decodeword.merge."+-.:_^" + char.10 + char.32) then
    {no space before or after} next(cmd, result + chars, true)
    else if ch ∈ decodeword.merge.",]})^(dq)" then
    {no space before but space after} next(cmd, result + chars, false)
    else if ch ∈ decodeword.merge."([{" then
     {space before but nospace after}
     next(cmd, if nospace then result + chars else result + char.32 + chars, true)
    else
     let d =
      if not.escapehtml then
      [ch]
      else if ch = char1."<" then
      decodeword.1_"&lt"
      else if ch = char1."&" then
      decodeword.1_"&amp"
      else [ch]
     ,
     next(cmd, if nospace then result + d else result + char.32 + d, false)
  else if this ∈ ". : " then
  {no space before or after} next(cmd, result + chars, true)
  else if this = escapeformat then
  next(not.cmd, result, nospace)
  else if chars = [char1."/", char1."<"] ∧ cmd then
  next(cmd, result + 2_chars, true)
  else if cmd ∧ this ∈ "/ldq /nosp /sp" then
   if this ∈ "/ldq" then
   next(cmd, result + if nospace then [char1.dq] else [char.32, char1.dq], true)
   else if this ∈ "/nosp" then
   next(cmd, result, true)
   else if not.isempty.toseqbyte.result ∧ 1^toseqbyte.result = tobyte.32 then
   next(cmd, result, true)
   else next(cmd, result + char.32, true)
  else
   let chars2 =
    if subseq(chars, 1, 1) = [char.0] then
    if nospace then result + chars << 1 else result + char.32 + chars << 1
    else if not.escapehtml ∨ not.cmd then
    if nospace then result + chars else result + char.32 + chars
    else
     for acc = if nospace then result else result + char.32, c ∈ chars
     do
      acc
      + 
       if c = char1."<" then
       decodeword.1_"&lt"
       else if c = char1."&" then
       decodeword.1_"&amp"
       else [c]
     ,
     acc
   ,
   next(cmd, chars2, false)
,
result 