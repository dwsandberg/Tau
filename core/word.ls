Module word

use bits

use seq.char

use encoding.seq.char

use seq.int

use kernal

use seq.word

use xxhash

function tointseq(a:seq.char) seq.int
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.int, @e ∈ a do acc + toint.@e,
acc

Function word(a:encoding.seq.char) word word.valueofencoding.a

Function asencoding(w:word) encoding.seq.char to:encoding.seq.char(rawvalue.w)

Function >1(a:char, b:char) ordering toint.a >1 toint.b

Function hash(a:seq.char) int
for acc = hashstart32.0, @e ∈ tointseq.a do hash32(acc, @e),
finalmix32.acc

Function wordencodingtoword(i:int) word word.to:encoding.seq.char(i)

Function encodeword(a:seq.char) word
{OPTION NOINLINE COMPILETIME}
word.encode.a

Function decodeword(w:word) seq.char
{OPTION NOINLINE COMPILETIME}
decode.asencoding.w

Function hash(a:word) int hash.asencoding.a

Function hash(a:seq.word) int
for acc = hashstart, @e ∈ a do hash(acc, hash.@e),
finalmix.acc

Function hash(a:seq.int) int
for acc = hashstart, @e ∈ a do hash(acc, @e),
finalmix.acc

Function >1(a:word, b:word) ordering asencoding.a >1 asencoding.b

Function merge(a:seq.word) word
{OPTION COMPILETIME /br
make multiple words into a single word. }
for acc = empty:seq.char, @e ∈ a do acc + decodeword.@e,
encodeword.acc

Function toword(n:int) word
{OPTION NOINLINE COMPILETIME /br
Covert integer to sequence of characters represented as a single word. }
encodeword.tochars.n

Function tochars(n:int) seq.char
if n < 0 then [{hyphenchar}char.45] + tochars(n, 10) else tochars(-n, 10)

function tochars(n:int, base:int) seq.char
{n should always be negative. This is to handle the smallest integer in the twos complement representation of integers}
if base + n > 0 then [char(48 - n)]
else tochars(n / base, base) + char(48 + n / base * base - n)

Function toint(w:word) int
{Convert an integer represented as a word to an int}
cvttoint.decodeword.w

Function cvttoint(s:seq.char) int
{Hex values starting with 0x or 0X are allowed. }
if n.s > 2 ∧ s sub 2 ∈ decodeword."Xx" sub 1 then
 for b = 0x0, c ∈ s
 do
  let i = toint.c - toint.char1."0",
  if between(i, 0, 9) then b << 4 ∨ bits.i
  else
   let i2 = toint.c - toint.char1."a",
   if between(i2, 0, 5) then b << 4 ∨ bits(i2 + 10)
   else
    let i3 = toint.c - toint.char1."A",
    if between(i3, 0, 5) then b << 4 ∨ bits(i3 + 10)
    else
     assert c ∈ [char1."x", char1."X", {no breack space}char.160] report "invalid hex digit" + encodeword.s,
     b,
 toint.b
else
 for val = 0, c ∈ s
 do
  let i = toint.c - toint.char1."0",
  if between(i, 0, 9) then val * 10 - i
  else
   assert c ∈ [char1."-", {no breack space}char.160] report "invalid digit" + encodeword.s + stacktrace,
   val
 {Since there are more negative numbers in twos-complement we calculate using negative values. }
 if val = 0 ∨ s sub 1 = char1."-" then val else -val

Function char1(s:seq.word) char
{* First character of first word of s}
(decodeword.s sub 1) sub 1 