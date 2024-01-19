Module webIOtypes

use JS.HTTPresult

use UTF8

use bits

use seq.byte

use bitcast.seq.byte

use bitcast.int

use ptr

use real

use standard

use file

Function set2zero(p:ptr, size:int) ptr
{used in wasm2.ls}
if size = 0 then p else set2zero(set(p, 0), size - 1)

Function empty:JS.HTTPresult JS.HTTPresult toJS.HTTPresult(emptyUTF8, empty:seq.byte)

type jsbytes is toreal:real

Export toreal(jsbytes) real

Export jsbytes(real) jsbytes

Export type:jsbytes

Export type:HTTPresult

Export type:jsbytes

type HTTPresult is header:UTF8, result:seq.byte

Export HTTPresult(header:UTF8, result:seq.byte) HTTPresult

Export result(HTTPresult) seq.byte

Export header(HTTPresult) UTF8

Function aborted(h:HTTPresult) boolean
subseq(toseqbyte.header.h, 1, 1) ≠ [tobyte.toint.char1."2"]

Function token(s:seq.word) jsbytes
jsUTF8.toseqbyte(
 for acc = emptyUTF8, w ∈ s do acc + decodeword.w,
 acc
)

Function jsUTF8(t:seq.byte) jsbytes
{OPTION NOINLINE}
jsbytes.toreal.bitcast:int(toptr.packed.t)

Function towords(a:jsbytes) seq.word towords.UTF8.toseqbyte.a

Function toseqbyte(a:jsbytes) seq.byte bitcast:seq.byte(toptr.intpart.toreal.a) 