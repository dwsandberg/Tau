Module objectio.T

use seq.T

use bitcast.seq.T

use process.seq.T

use bits

use process.seq.byte

use object01

use symbol2

Builtin typestructure:T seq.seq.mytype

Function outbytes:T(try:seq.T) seq.byte result.process.outp.try

Function outp(try:seq.T) seq.byte
let pat = formatTypeDef.typestructure:T,
encode2.outrec(toptr.try, pat)

Function inbytes:T(in:seq.byte) seq.T
{Note: " bitcast:seq.T (result.process.inrec.in)" will not work because a deepcopy is
 done when the process returns a value. The deepcopy will be of a type ptr which will not work. 
 The bitcast must be done before the deepcody is done, which inprocess does.}
result.process.inp:T(in)

function inp:T(in:seq.byte) seq.T bitcast:seq.T(inrec.in) 