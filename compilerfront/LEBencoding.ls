Module LEBencoding

use bits

use seq.boolean

use seq.byte

use otherseq.int

use standard

Export type:decoderesult

Export next(decoderesult) int

Export value(decoderesult) int

Function testLEB seq.word
let r = [
 tobyte.127
 , tobyte.128
 , tobyte.1
 , tobyte.128
 , tobyte.128
 , tobyte.4
 , tobyte.229
 , tobyte.142
 , tobyte.38
 , tobyte.255
 , tobyte.0
 , tobyte.192
 , tobyte.187
 , tobyte.120
]
let d1 = decodeLEBu(r, 1)
let d2 = decodeLEBu(r, next.d1)
let d3 = decodeLEBu(r, next.d2)
let d4 = decodeLEBu(r, next.d3)
let d5 = decodeLEBs(r, next.d4)
let d6 = decodeLEBs(r, next.d5)
for sample = [0], k ∈ [0x2, 0x4, 0x6, 0x8, 0xA, 0xC, 0xE] do sample + toint(k << 60)
let val1 =-4618090677529464034
let xxx =
 for acc = empty:seq.byte, i ∈ sample do acc + LEBs.i + LEBu.i
 for ok = empty:seq.boolean, next = 1, j ∈ sample
 do
  let t = decodeLEBs(acc, next)
  let tu = decodeLEBu(acc, next.t),
  next(ok + [value.t = j, value.tu = j], next.tu),
  [
   value.d1 = 127
   , value.d2 = 128
   , value.d3 = 65536
   , value.d4 = 624485
   , value.d5 = 127
   , value.d6 = -123456
   , val1 = value.decodeLEBs(LEBs.val1, 1)
   , decodeLEBu:seq.int(LEBu.sample) = sample
   , decodeLEBs:seq.int(LEBs.sample) = sample
   , LEBu.127 + LEBu.128 + LEBu.2^16 + LEBu.624485 + LEBs.127 + LEBs.-123456 = r
  ]
   + ok
for acc = empty:seq.int, i = 1, e ∈ xxx do next(if e then acc else acc + i, i + 1),
if isempty.acc then "PASS testLEB" else "FAIL testLEB numbers:^(acc)"

Function LEBu(i:int) seq.byte LEB(bits.0, bits.i, empty:seq.byte)

Function LEBs(i:int) seq.byte LEB(bits.64, bits.i, empty:seq.byte)

function LEB(signbit:bits, value:bits, result:seq.byte) seq.byte
let byte = value ∧ bits.127
let value1 =
 if toint.value < 0 ∧ toint.signbit ≠ 0 then
 bits.-1 << (64 - 7) ∨ value >> 7
 else value >> 7,
if toint.value1 = 0 ∧ toint(byte ∧ signbit) = 0 then
result + tobyte.byte
else if toint.value1 = -1 ∧ toint.byte ≥ toint.signbit then
result + tobyte.byte
else LEB(signbit, value1, result + tobyte(byte ∨ bits.128))

Function decodeLEBu(a:seq.byte, i:int) decoderesult decodeLEB2(a, i, 0x0)

Function decodeLEBs(a:seq.byte, i:int) decoderesult decodeLEB2(a, i, tobits.64)

function decodeLEB2(a:seq.byte, i:int, signbit:bits) decoderesult
{outside}
for acc = 0x0, lastbyte = 0x80, j = 0, jj ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
while (lastbyte ∧ 0x80) ≠ 0x0
do let byte = tobits.(i + j)#a, next(acc ∨ (byte ∧ 0x7F) << (j * 7), byte, j + 1)
let value = if (lastbyte ∧ signbit) = 0x0 ∨ j = 10 then acc else acc ∨ tobits.-1 << (j * 7),
decoderesult(toint.value, i + j)

type decoderesult is value:int, next:int

Function decodeLEBu:seq.int(a:seq.byte) seq.int
for acc = empty:seq.int, result = 0x0, shift = 0, b ∈ a
do
 let byte = tobits.b
 let c = byte ∧ 0x7F
 let newresult = result ∨ c << shift,
  if c = byte then
  next(acc + toint.newresult, 0x0, 0)
  else next(acc, newresult, shift + 7),
acc

Function decodeLEBs:seq.int(a:seq.byte) seq.int
for acc = empty:seq.int, result = 0x0, shift = 0, b ∈ a
do
 let byte = tobits.b
 let c = byte ∧ 0x7F
 let newresult = result ∨ c << shift,
  if c = byte then
   let val =
    if (byte ∧ 0x40) = 0x0 ∨ toint.newresult < 0 then
    newresult
    else newresult ∨ tobits.-1 << (shift + 7),
   next(acc + toint.val, 0x0, 0)
  else next(acc, newresult, shift + 7),
acc

Function LEBs(s:seq.int) seq.byte for acc = empty:seq.byte, e ∈ s do acc + LEBs.e, acc

Function LEBu(s:seq.int) seq.byte for acc = empty:seq.byte, e ∈ s do acc + LEBu.e, acc

Function tobyte(b:bits) byte tobyte.toint.b 