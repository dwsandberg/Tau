Module bits

use stdlib

Function type:byte internaltype export

Function type:bits internaltype export

Function type:bit internaltype export

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

Function frombits:byte(a:bits)byte byte.toint.a

Function byte(int)byte export

Function toint(byte)int export

_______________