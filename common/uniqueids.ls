Module uniqueids

use encoding.idrange

use seq.idrange

use standard

Function ldq(a:seq.word) seq.word "/ldq^(a)^(dq)"

type idrange is next:int

function =(a:idrange, b:idrange) boolean next.a = next.b

function hash(a:idrange) int next.a

Function requestids(no:int) int
let d = encodingdata:idrange
let firstno = if isempty.d then 1 else next.1^d
let discard = encode.idrange(firstno + no),
firstno 