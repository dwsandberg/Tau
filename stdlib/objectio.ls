module objectio.T

use bits

use object01

use standard

use symbol2

use bitcast.T

use seq.byte

use seq.mytype

use bitcast.seq.T

use seq.seq.int

Builtin typestructure:T seq.seq.mytype

Function outbytes:T(try:seq.T)seq.byte
let pat = formatTypeDef.typestructure:T
encode2.outrec(toptr.try, pat)

Function inbytes:T(in:seq.byte)seq.T bitcast:seq.T(inrec.decode2.in) 