Module bits

use standard

Export type:byte

Export type:bits

Export type:bit

type bits is record toint:int

Export toint(bits)int

Export bits(int)bits

Builtin ∨(a:bits, bits)bits

Builtin ∧(a:bits, bits)bits

Builtin >>(a:bits, i:int)bits

Builtin <<(a:bits, i:int)bits

Builtin xor(a:bits, b:bits)bits

Function =(a:bits, b:bits)boolean toint.a = toint.b

/Builtin ∨(a:bits, b:int)bits   a ∨ bits.b

/Builtin ∧(a:bits, b:int )bits a ∧ bits.b

__________________

type bit is record toint:int

Function =(a:bit, b:bit)boolean toint.a = toint.b

Export toint(bit)int

Export bit(int)bit

Function sizeinbits(a:bit)int 1

Function tobits(a:bit)bits bits.toint.a

Function frombits:bit(a:bits)bit bit.toint.a

_________________

type byte is record toint:int

Function sizeinbits(a:byte)int 8

Function tobits(a:byte)bits bits.toint.a

Function frombits:byte(a:bits)byte byte.toint.a

Export byte(int)byte

Export toint(byte)int

_______________