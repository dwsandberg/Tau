Module inputoutput

use UTF8

use bits

use bitstream

use mangle

use standard

use fileT.bit

use seq.bit

use seq.bits

use fileT.byte

use seq.byte

use fileT.int

use seq.int

use encoding.seq.char

Export type:cstr

Function tocstr(s:seq.word)cstr
cstr.packed.bits.for acc = empty:bitstream, @e ∈ toseqbyte.toUTF8.s + tobyte.0 do add(acc, bits.toint.@e, 8)/for(acc)

type cstr is dummy:seq.bits

Builtin getfile2(cstr)fileresult.int

Builtin getbytefile2(cstr)fileresult.byte

Builtin getbitfile2(cstr)fileresult.bit

Function getfileint(name:seq.word)seq.int result.getfile2.tocstr.name

Function getfilebyte(name:seq.word)seq.byte result.getbytefile2.tocstr.name

Function getfilebit(name:seq.word)seq.bit result.getbitfile2.tocstr.name

Builtin createfile2(byteLength:int, data:seq.bits, cstr)int

Function createfile(name:seq.word, a:seq.byte)int
createfile2(length.a
, packed.bits.for acc = empty:bitstream, @e ∈ a do add(acc, bits.toint.@e, 8)/for(acc)
, tocstr.name
)

Function createfile(name:seq.word, a:seq.int)int
createfile2(length.a * 8
, for acc = empty:seq.bits, @e ∈ packed.a do acc + bits.@e /for(acc)
, tocstr.name
)

Builtin initialdict seq.encodingpair.seq.char

Builtin randomint(i:int)seq.int

Function stacktrace seq.word internalstacktrace

Module fileT.T

use standard

use seq.T

Export type:fileresult.T

type fileresult is size:int, start:seq.T, data:seq.T

Function result(a:fileresult.T)seq.T start.a + data.a 