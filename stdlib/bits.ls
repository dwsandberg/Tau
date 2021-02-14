Module bits

use standard

Export type:byte

Export type:bits

Export type:bit

type bits is toint:int

Export toint(bits)int

Function tobits(a:int)bits bits.a

Export bits(int)bits

Builtin ∨(a:bits, bits)bits

Builtin ∧(a:bits, bits)bits

Builtin >>(a:bits, i:int)bits

Builtin <<(a:bits, i:int)bits

Builtin xor(a:bits, b:bits)bits

Function =(a:bits, b:bits)boolean toint.a = toint.b

function hexdigit(b:bits)char(decodeword."0123456789ABCDEF"_1)_(1 + toint(b ∧ 0x0F))

function hexword(b:bits)word
 encodeword.[ hexdigit(b >> 12), hexdigit(b >> 8), hexdigit(b >> 4), hexdigit.b]

Function print(b:bits)seq.word [ hexword(b >> 48), hexword(b >> 32), hexword(b >> 16), hexword.b]

Function print(b:byte)seq.word [ encodeword.[ hexdigit(tobits.b >> 4), hexdigit.tobits.b]]

Function floorlog2(a:int)int
 let d64 = tobits.a
 let b32 = d64 >> 32
 let t32 = if b32 = 0x0 then 0 else 32
 let d32 = if b32 = 0x0 then 0xFFFFFFFF ∧ d64 else b32
 let b16 = d32 >> 16
 let t16 = if b16 = 0x0 then 0 else 16
 let d16 = if b16 = 0x0 then 0xFFFF ∧ d32 else b16
 let b8 = d16 >> 8
 let t8 = if b8 = 0x0 then 0 else 8
 let d8 = if b8 = 0x0 then 0xFF ∧ d16 else b8
 let b4 = d8 >> 4
 let t4 = if b4 = 0x0 then 0 else 4
 let d4 = if b4 = 0x0 then 0xF ∧ d8 else b4
  t32 + t16 + t8 + t4
  + [ 0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4]_(toint.d4 + 1)

__________________

type bit is rep:int

Function =(a:bit, b:bit)boolean toint.a = toint.b

Builtin toint(b:bit)int

Function tobit(a:int)bit bit.a

Function tobits(a:bit)bits tobits.toint.a

_________________

type byte is rep:int

Function =(a:byte, b:byte)boolean toint.a = toint.b

Function tobits(a:byte)bits tobits.toint.a

Builtin toint(b:byte)int \\ use builtin rather than rep.b so abyteseq @ +(empty:seq.int, toint.@e)does not become an noop since a bytseq may contain packed sequences of bytes \\

Function tobyte(a:int)byte byte.a

_______________