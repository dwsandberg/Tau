module packedindex

use standard

use tausupport

use seq.packed3

use bitcast:packed3

use bitcast:seq.packed3

Function packedindex(t:ptr, size:int, idx:int)ptr
assert size = 3 report"problem packedindex"
toptr.bitcast:seq.packed3(t)_idx 