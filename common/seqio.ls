module seqio.T

use seqiohelp

use standard

use symbol2

use seq.mytype

use bitcast.seq.T

use seq.seq.mytype

use bits

use UTF8

use IO2

Builtin typestructure:T seq.seq.mytype

Function readfile:T(name:seq.word)seq.T
{OPTION INLINE}
let datain = towords.UTF8.getfile:byte(name)
bitcast:seq.T(subread.datain)

Function writefile:T(name:seq.word, data:seq.T)seq.word
let a = fileformat.typestructure:T
subwrite(toptr.data, a, name) 