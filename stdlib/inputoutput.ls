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
let t = for acc = emptyUTF8, w ∈ s do acc + decodeword.w /for(toseqbyte.acc)
cstr.packed.bits.for acc = empty:bitstream, @e ∈ t + tobyte.0 do add(acc, bits.toint.@e, 8)/for(acc)

type cstr is dummy:seq.bits

Builtin getfile2(cstr)fileresult.int

Builtin getbytefile2(cstr)fileresult.byte

Builtin getbitfile2(cstr)fileresult.bit

/Export getfileX:byte(seq.word, int)seq.byte

/Export getfileX:int(seq.word, int)seq.int

/Export getfileX:bit(seq.word, int)seq.bit

Function getfile:byte(name:seq.word)seq.byte { getfileX:byte(name,-8)} result.getbytefile2.tocstr.name

Function getfile:bit(name:seq.word)seq.bit result.getbitfile2.tocstr.name

Function getfile:int(name:seq.word)seq.int result.getfile2.tocstr.name

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

use inputoutput

use standard

use seq.T

Export type:fileresult.T

type fileresult is size:int, start:seq.T, data:seq.T

Function result(a:fileresult.T)seq.T start.a + data.a

/Builtin subgetfile:T(cstr, typ:int)fileresult.T

/Function getfileX:T(name:seq.word, typ:int)seq.T result.subgetfile:T(tocstr.name, typ) 