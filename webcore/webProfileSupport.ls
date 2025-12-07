Module webProfileSupport

use profile

use symbol1

use seq.byte

use bits

use standard

/use objectio.addrsym

use object01

use bitcast.seq.addrsym

Function decodeaddrsym(b:seq.byte) seq.seq.addrsym
{???? should work but doesn't:[inbytes:addrsym (b)]}
[bitcast:seq.addrsym(inrec.b)] 