module uniqueids

use standard

use encoding.idrange

Function $(a:seq.word,b:seq.word) seq.word a+b

Function xml(val:seq.word)seq.word dq.val + space

type idrange is next:int

function =(a:idrange, b:idrange)boolean next.a = next.b

function hash(a:idrange)int next.a

function assignencoding(a:idrange)int nextencoding.a

Function requestids(no:int)int
let j = nextencoding.idrange.0
let firstno = if j = 1 then 1 else next.decode.to:encoding.idrange(j - 1)
let discard = encode.idrange(firstno + no)
firstno 