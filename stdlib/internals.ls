module internals(T)

use seq.T

use stacktrace

use stdlib

Function seqtype(a:seq.T)int Ttoint.valueat(address.a, 0)

Function allocatespace(i:int)seq.T builtin.usemangle

type address is record toseq:seq.T

Function +(a:address.T, i:int)address.T builtin.usemangle

Function toT(a:address.T)T builtin

Function toseq(a:address.T)seq.T export

Function address(seq.T)address.T export

Function valueat(address.T, offset:int)T builtin.IDXUC

function Ttoint(T)int builtin

Function setfld3(a:address.T, x:int, i:int)int builtin.SETFLD3

Function setfld3T(a:address.T, x:T, i:int)int setfld3(a, Ttoint.x, i)

This pstruct function is tacked on here for printing structure of seq.

/Function pstruct(a:seq.T)seq.word iftype x:pseq.T = a then"["+ toword.length.x + pstruct.a.x +"/"+ pstruct.b.x +"]"else"^"+ toword.length.a + decodeaddress.seqtype.a

---------------------------

