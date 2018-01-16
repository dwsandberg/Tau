Module byteseq.T

use bits

use seq.T

use seq.bits

use stdlib

type bitpackedseq is sequence length:int, data:seq.T, part:bits

function frombits(a:bits)T unbound

function tobits(T)bits unbound

function sizeinbits(T)int unbound

Function bitpackedseq(int, seq.T, bits)bitpackedseq.T export

Function toseq(a:bitpackedseq.T)seq.T export

Function length(bitpackedseq.T)int export

Function empty bitpackedseq.T bitpackedseq(0, empty:seq.T, bits.0)

Function bitpackedseq2(len:int, d:seq.T, part:bits)seq.T toseq.bitpackedseq(len, d, part)

Function data2(a:bitpackedseq.T)seq.bits @(+, tobits, empty:seq.bits, data.align.a)

Function_(a:bitpackedseq.T, idx:int)T 
 let nobits = sizeinbits.frombits.bits.0 
  let slotsperword = 64 / nobits 
  let dataidx =(idx - 1)/ slotsperword + 1 
  let d = if dataidx > length.data.a then part.a else tobits(data(a)_dataidx)
  let slot =(idx - 1)mod slotsperword * nobits 
  frombits(d >> slot ∧ bits.-1 >> 64 - nobits)

Function add(a:bitpackedseq.T, b:T)bitpackedseq.T 
 let nobits = sizeinbits.b 
  let slotsperword = 64 / nobits 
  let slot = length.a mod slotsperword 
  let newpart =(tobits.b ∧ bits.-1 >> 64 - nobits)<< slot * nobits ∨ part.a 
  if slot = slotsperword - 1 
  then bitpackedseq(length.a + 1, data.a + frombits.newpart, bits.0)
  else bitpackedseq(length.a + 1, data.a, newpart)

Function align(a:bitpackedseq.T)bitpackedseq.T 
 let nobits = sizeinbits.frombits.bits.0 
  let slotsperword = 64 / nobits 
  let slot = length.a mod slotsperword 
  if slot = 0 then a else align.add(a, frombits.bits.0)

Function patch(a:bitpackedseq.T, j:int, val:int)bitpackedseq.T 
 assert(j - 1)mod 32 = 0 report"incorrect parameter to replace"
  let i = j / 64 + 1 
  let b = if i > length.data.a then part.a else tobits(data(a)_i)
  let x = if(j - 1)mod 64 = 0 
   then b ∧ bits(toint(bits.1 << 32) - 1)<< 32 ∨ bits.val 
   else b ∧ bits(toint(bits.1 << 32) - 1)∨ bits.val << 32 
  // assert false report"PP"+ toword.toint.x // 
  if i > length.data.a 
  then bitpackedseq(length.a, data.a, x)
  else bitpackedseq(length.a, subseq(data.a, 1, i - 1)+ frombits.x + subseq(data.a, i + 1, length.data.a), part.a)

Function add(a:bitpackedseq.T, b:bits, count:int)bitpackedseq.T 
 let nobits = sizeinbits.frombits.bits.0 
  let slotsperword = 64 / nobits 
  let slot = length.a mod slotsperword 
  let slotstoadd = min(slotsperword - slot, count)
  let newpart =(b ∧ bits.-1 >> 64 - slotstoadd * nobits)<< slot * nobits ∨ part.a 
  let d = if slot + slotstoadd = slotsperword 
   then bitpackedseq(length.a + slotstoadd, data.a + frombits.newpart, bits.0)
   else bitpackedseq(length.a + slotstoadd, data.a, newpart)
  if slotstoadd = count then d else add(d, b >> slotstoadd * nobits, count - slotstoadd)

