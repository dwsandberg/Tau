Module inputoutput

use UTF8

use seq.bit

use process.seq.bit

use bits

use seq.bits

use bitstream

use seq.byte

use process.seq.byte

use seq.seq.byte

use file

use seq.file

use format

use standard

use tausupport

Export type:cstr

function tocstr(s:seq.word)cstr
let t = for acc = emptyUTF8, w ∈ s do acc + decodeword.w /for(toseqbyte.acc)
cstr.packed.bits.for acc = empty:bitstream, @e ∈ t + tobyte.0 do add(acc, bits.toint.@e, 8)/for(acc)

type cstr is dummy:seq.bits

Builtin getbytefile2(cstr)process.seq.byte{OPTION STATE}

Builtin getbitfile2(cstr)process.seq.bit{OPTION STATE}

function getfile:byte(name:seq.word)seq.byte
let a = getbytefile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.byte)

function getfile:bit(name:seq.word)seq.bit
let a = getbitfile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.bit)

Function getfiles(args:seq.word)seq.file
for acc = empty:seq.file, fn ∈ getfilenames(".", args << 1)do
 acc
 + if ext.fn ∈ "bc"then file(fn, getfile:bit([fullname.fn]))
 else file(fn, getfile:byte([fullname.fn]))
/for(acc)

Builtin createfile3(a:seq.seq.byte, name:cstr)int

___________

Function finishentry(result:seq.file)UTF8
for acc = "files created:", f ∈ result do
 let discard2 = 
  createfile3(packed.toseqseqbyte.if length.bs.f = 0 then
   for acc2 = empty:bitstream, @e ∈ data.f do add(acc2, bits.toint.@e, 8)/for(acc2)
  else bs.f
  , tocstr.[fullname.fn.f]
  )
 acc + fullname.fn.f
/for(HTMLformat.acc) 