Module bitstream

use bits

use standard

use otherseq.bits

use seq.byte

use seq.char

Export type:bitstream

type bitstream is length:int, endpart:bits, fullwords:seq.bits

Function tobitstream(s:seq.bits)bitstream bitstream(length.s * 64, 0x0, s)

Export length(bitstream)int

Function bits(a:bitstream)seq.bits fullwords.a + endpart.a

/ function singlebit(a:bitstream, i:int)int // does format checking and gets bit i // assert between(i, 1, length.a)report 
"out bound singlebit"assert(length.a+63)/ 64=length.fullwords.a+1 report"rep problem"let j=((i-1)/ 64+1)let b 
=if j > length.fullwords.a then let partbits=(length.a mod 64)assert partbits=0 ∨ bits.0=endpart.a >>(partbits)report 
"stray bits"endpart.a else(fullwords.a)_j toint(b >>((i-1)mod 64)∧ 0x1)

Function empty:bitstream bitstream bitstream(0, 0x0, empty:seq.bits)

function =(a:bitstream, b:bitstream)boolean length.a = length.b ∧ endpart.a = endpart.b ∧ fullwords.a = fullwords.b

Function patch(a:bitstream, i:int, val:int)bitstream
subseq(a, 1, i - 1) + bitstream(32, bits.val) + subseq(a, i + 32, length.a)

function print(x:bitstream)seq.word
if length.x = 0 then"empty"
else
 let i = (length.x - 1) mod 64
 let j = i / 16
 let start = print.endpart.x << (3 - j)
 let k = i mod 16 + 1
 let part = if k = 16 then start else[toword.k] + "bits of" + start
 part
 + for acc = "", @e ∈ reverse.fullwords.x do acc + print.@e /for(acc)

function firstword(x:bitstream)bits if isempty.fullwords.x then endpart.x else first.fullwords.x

function ithword(x:bitstream, i:int)bits
if i > length.fullwords.x then endpart.x else(fullwords.x)_i

Function bitstream(length:int, val:bits)bitstream bitstream(length, bits(2^length - 1) ∧ val, empty:seq.bits)

Function index(s:bitstream, i:int, sizebits:int)bits endpart.subseq(s, (i - 1) * sizebits + 1, i * sizebits)

Function _(s:bitstream, i:int)byte tobyte.toint.index(s, i, 8)

Function subseq(s:bitstream, start:int, finish:int)bitstream
let len = finish - start + 1
let partbits = toint(bits(len - 1) ∧ bits.63)
let startword = toint(bits(start - 1) >> 6) + 1
let finishword = toint(bits(finish - 1) >> 6) + 1
let startshift = toint(bits(start - 1) ∧ bits.63)
let finishshift = toint(bits(finish - 1) ∧ bits.63)
let startpart = ithword(s, startword) >> startshift
let finishpartmask = bits.-1 >> (63 - partbits)
if len ≤ 64 then
 if len ≤ 0 then empty:bitstream
 else if startword = finishword then bitstream(len, startpart ∧ finishpartmask, empty:seq.bits)
 else
  let endpart = ithword(s, finishword) << (64 - startshift) ∧ finishpartmask
  bitstream(len, startpart ∨ endpart, empty:seq.bits)
else if startshift = 0 then
 let endpart = ithword(s, finishword) ∧ finishpartmask
 bitstream(len, endpart, subseq(fullwords.s, startword, finishword - 1))
else
 let endpart = 
  if finishshift ≥ startshift then
   {all bits in endpart come from finishword}ithword(s, finishword) >> (64 - startshift)
   ∧ finishpartmask
  else
   ithword(s, finishword) << (64 - startshift) ∧ finishpartmask
   ∨ ithword(s, finishword - 1) >> (64 - startshift)
 let firstpart = 
  subseq(fullwords.s + endpart.s
  , startword
  , if finishshift = 63 then finishword else finishword - 1
  )
 bitstream(len, endpart, shiftleft(2, startpart, firstpart, startshift, empty:seq.bits))

/function cmp(a:bitstream, b:bitstream, i:int, offseta:int)boolean if i > length.b then true else if singlebit(a, i 
+offseta)=singlebit(b, i)then cmp(a, b, i+1, offseta)else false

Function +(a:bitstream, b:bitstream)bitstream
{steal bits from b to make full words in a}
let partbitsa = toint(bits.length.a ∧ bits(64 - 1))
if partbitsa = 0 ∧ length.a > 0 then
 {no need to steal bits}
 bitstream(length.a + length.b, endpart.b, fullwords.a + endpart.a + fullwords.b)
else if length.b ≤ 64 then add(a, endpart.b, length.b)
else
 let partbitsb = toint(bits.length.b ∧ bits(64 - 1))
 let steal = 64 - partbitsa
 let overlap = firstword.b << partbitsa ∨ endpart.a
 let firstpart = fullwords.a + overlap
 if length.fullwords.b = 0 then
  if partbitsb + partbitsa > 64 then bitstream(length.a + length.b, firstword.b >> steal, firstpart)
  else bitstream(length.a + length.b, overlap, fullwords.a)
 else
  let allwords = shiftleft(2, firstword.b >> steal, fullwords.b + endpart.b, partbitsa, firstpart)
  if partbitsb > steal ∨ partbitsb = 0 then bitstream(length.a + length.b, endpart.b >> steal, allwords)
  else bitstream(length.a + length.b, last.allwords, allwords >> 1)

Function add(a:bitstream, b:bits, nobits:int)bitstream
let partbitsa = toint(bits.length.a ∧ bits(64 - 1))
let firstwordb = b ∧ bits.-1 >> (64 - nobits)
if partbitsa = 0 ∧ length.a > 1 then bitstream(length.a + nobits, firstwordb, fullwords.a + endpart.a)
else
 let overlap = firstwordb << partbitsa ∨ endpart.a
 let steal = 64 - partbitsa
 if partbitsa + nobits > 64 then
  let firstpart = fullwords.a + overlap
  bitstream(length.a + nobits, firstwordb >> steal, firstpart)
 else bitstream(length.a + nobits, overlap, fullwords.a)

Function +(a:bitstream, b:byte)bitstream add(a, tobits.b, 8)

Function +(a:bitstream, b:seq.byte)bitstream for acc = a, @e ∈ b do acc + @e /for(acc)

function shiftleft(i:int, leftover:bits, allwords:seq.bits, shiftleft:int, result:seq.bits)seq.bits
if i > length.allwords then result
else
 let next = allwords_i
 shiftleft(i + 1, next >> (64 - shiftleft), allwords, shiftleft, result + (leftover ∨ next << shiftleft)) 