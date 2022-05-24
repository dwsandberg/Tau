module uniqueids

use standard

use encoding.idrange

Function xml(val:seq.word)seq.word dq.val + space

type idrange is next:int

function =(a:idrange, b:idrange)boolean next.a = next.b

function hash(a:idrange)int next.a

use seq.idrange

Function requestids(no:int)int
let d=encodingdata:idrange
let firstno = if isempty.d then 1 else next.last.d
let discard = encode.idrange(firstno + no)
firstno
