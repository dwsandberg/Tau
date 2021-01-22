Module bits

use standard

Export type:byte

Export type:bits

Export type:bit

type bits is record toint:int

Export toint(bits)int

Function tobits(a:int) bits bits.a

Export bits(int)bits

Builtin ∨(a:bits, bits)bits

Builtin ∧(a:bits, bits)bits

Builtin >>(a:bits, i:int)bits

Builtin <<(a:bits, i:int)bits

Builtin xor(a:bits, b:bits)bits

Function =(a:bits, b:bits)boolean toint.a = toint.b


function  hexdigit(b:bits)  char (decodeword."0123456789ABCDEF"_1)_(1 + toint(b ∧  0x0F))

function hexword(b:bits) word 
      encodeword.[hexdigit(b >> 12), hexdigit(b >> 8),      hexdigit(b >> 4),  hexdigit.b]
    
Function print(b:bits) seq.word
    [ hexword(b >> 48)  ,  hexword(b >> 32) , hexword(b >> 16),  hexword(b )]
    
Function print(b:byte) seq.word 
      [encodeword.[      hexdigit(tobits.b >> 4),  hexdigit.tobits.b]]


__________________

type bit is record rep:int

Function =(a:bit, b:bit)boolean toint.a = toint.b

Builtin    toint(b:bit) int  

Function  tobit(a:int)bit bit.a

Function tobits(a:bit)bits   tobits.toint.a

_________________

type byte is record rep:int

Function =(a:byte, b:byte)boolean toint.a = toint.b

Function tobits(a:byte)bits tobits.toint.a

Builtin  toint(b:byte)int  // use builtin rather than rep.b so  abyteseq @ +(empty:seq.int,toint.@e) does 
not become an noop since a bytseq may contain packed sequences of bytes // 


Function  tobyte(a:int) byte byte.a


_______________