Module objectio.T

use seq.T

use bitcast.seq.T

use bits

use object01

use symbol2

use ptr

Builtin typestructure:T seq.seq.mytype

Function outbytes:T(try:seq.T) seq.byte
result.process.outp.try

Function outp(try:seq.T) seq.byte
let pat = formatTypeDef.typestructure:T
encode2.outrec(toptr.try, pat)

use process.seq.T 

use process.ptr

use process.seq.byte

Function inbytes:T(in:seq.byte) seq.T result.process.inp.in  

Function inbytes2:T(in:seq.byte) seq.T bitcast:seq.T(result.process.inrec.in)  

function inp(in:seq.byte) seq.T bitcast:seq.T(inrec.in)