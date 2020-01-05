Module bits

use UTF8

use bitpackedseq.bit

use blockseq.bits

use blockseq.int


use packedseq.bits

use seq.bit

use seq.int

use stdlib

use seq.byte

type bits is record toint:int

Function toint(bits)int export

Function bits(int)bits export

Function ∨(a:bits, bits)bits builtin.usemangle

Function ∧(a:bits, bits)bits builtin.usemangle

Function >>(a:bits, i:int)bits builtin.usemangle

Function <<(a:bits, i:int)bits builtin.usemangle

Function xor(a:bits, b:bits)bits builtin.usemangle

__________________

type bit is record toint:int

Function =(a:bit, b:bit)boolean toint.a = toint.b

Function toint(bit)int export

Function bit(int)bit export

Function sizeinbits(a:bit)int 1

Function tobits(a:bit)bits bits.toint.a


Function frombits:bit(a:bits)bit bit.toint.a



_________________

type byte is record toint:int


Function sizeinbits(a:byte)int 8

Function tobits(a:byte)bits bits.toint.a


Function frombits:byte(a:bits )byte byte.toint.a


Function blockit(seq.int)seq.int export

Function byte(int) byte export

Function  toint(byte) int export

_______________

Function addvbr(b:bitpackedseq.bit, newbits:int, bitcount:int)bitpackedseq.bit 
 let limit = toint(bits.1 << bitcount - 1)
  if newbits < limit 
  then add(b, bits.newbits, bitcount)
  else let firstchunk = bits(limit - 1)∧ bits.newbits ∨ bits.limit 
  let secondchunk = bits.newbits >> bitcount - 1 
  assert toint.secondchunk < limit report"vbr encoding for value is not handled"+ toword.newbits + toword.limit 
  add(b, secondchunk << bitcount ∨ firstchunk, bitcount * 2)

function addvbr6(b:bits, bitstoadd:int, leftover:bits, s:seq.int, r:bitpackedseq.bit, i:int)bitpackedseq.bit 
 if bitstoadd > 58 
  then addvbr6(bits.0, 0, leftover, s, add(r, b, bitstoadd), i)
  else if toint.leftover > 0 
  then if toint.leftover < 32 
   then addvbr6(b ∨ leftover << bitstoadd, bitstoadd + 6, bits.0, s, r, i)
   else addvbr6(b ∨(leftover ∧ bits.31 ∨ bits.32)<< bitstoadd, bitstoadd + 6, leftover >> 5, s, r, i)
  else if i > length.s 
  then if bitstoadd = 0 then r else add(r, b, bitstoadd)
  else let v = s_i 
  if v < 32 
  then addvbr6(b ∨ bits.v << bitstoadd, bitstoadd + 6, bits.0, s, r, i + 1)
  else addvbr6(b ∨(bits.v ∧ bits.31 ∨ bits.32)<< bitstoadd, bitstoadd + 6, bits.v >> 5, s, r, i + 1)

Function addvbr6(b:bitpackedseq.bit, s:seq.int)bitpackedseq.bit addvbr6(bits.0, 0, bits.0, s, b, 1)

Function addvbr6(b:bitpackedseq.bit, v:int)bitpackedseq.bit addvbr6(bits.0, 0, bits.0, [ v], b, 1)

Function addvbrsigned6(b:bitpackedseq.bit, val:int)bitpackedseq.bit 
 if val < 0 
  then if val >-16 
   then addvbr6(b, 2 *-val + 1)
   else let chunk = bits(32 +-val mod 16 * 2 + 1)
   addvbr6(chunk, 6, bits(-val)>> 4, empty:seq.int, b, 1)
  else if val < 16 
  then addvbr6(b, 2 * val)
  else let chunk = bits(32 + val mod 16 * 2)
  addvbr6(chunk, 6, bits.val >> 4, empty:seq.int, b, 1)

Function align32(a:bitpackedseq.bit)bitpackedseq.bit 
 let k = length.a mod 32 
  if k = 0 then a else add(a, bits.0, 32 - k)
  
