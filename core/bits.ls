Module bits

use seq.bits

use standard

Export type:bits

Export toint(bits) int

Export type:byte

Export bits(int) bits

type bits is toint:int

Function tobits(a:int) bits bits.a

Builtin ∨(a:bits, bits) bits {OPTION COMPILETIME}

Builtin ∧(a:bits, bits) bits {OPTION COMPILETIME}

Builtin >>(a:bits, i:int) bits {OPTION COMPILETIME}

Builtin <<(a:bits, i:int) bits {OPTION COMPILETIME}

Builtin ⊻(a:bits, b:bits) bits {OPTION COMPILETIME}

Function =(a:bits, b:bits) boolean toint.a = toint.b

function hexdigit(b:bits) char (1 + toint(b ∧ 0x0F))#decodeword.1#"0123456789ABCDEF"

function hexword(b:bits) word
encodeword.[hexdigit(b >> 12), hexdigit(b >> 8), hexdigit(b >> 4), hexdigit.b]

Function %(b:bits) seq.word
[hexword(b >> 48), hexword(b >> 32), hexword(b >> 16), hexword.b]

Function %(b:byte) seq.word [encodeword.[hexdigit(tobits.b >> 4), hexdigit.tobits.b]]

Function floorlog2(a:int) int
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
let d4 = if b4 = 0x0 then 0xF ∧ d8 else b4,
t32
 + t16
 + t8
 + t4
 + (toint.d4 + 1)#[0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4]

type byte is rep:int

Function =(a:byte, b:byte) boolean toint.a = toint.b

Function tobits(a:byte) bits tobits.toint.a

Builtin toint(b:byte) int
{???? use builtin rather than rep.b so for acc = empty:seq.int, e /in s do toint.e where s
is a byte sequence does not become an noop since s may contain packed sequences of bytes}

Function tobyte(a:int) byte byte.a

Function toseqbits(a:seq.byte) seq.bits
for acc = empty:seq.bits, current = bits.0, shift = 0, b ∈ a
do
 if shift = 64 then
 next(acc + current, bits.toint.b ∧ 0xFF, 8)
 else next(acc, current ∨ (bits.toint.b ∧ 0xFF) << shift, shift + 8),
acc + current 