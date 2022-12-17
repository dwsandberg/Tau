Module encoding.T

use bitcast.einfo.T

use seq.encodingpair.T

use otherseq.seq.encodingpair.T

use bitcast.encodingstate.T

use seq.T

use bits

use ptr

use standard

Export type:encoding.T

Export valueofencoding(a:encoding.T) int

type encoding is valueofencoding:int

Function to:encoding.T(i:int) encoding.T encoding.i

type encodingstate is all:seq.encodingpair.T
 , length:int
 , encodetable:seq.seq.encodingpair.T
 , lastadd:encoding.T

Export type:encodingstate.T

Export length(encodingstate.T) int

Function startInParent:T boolean
let inst = getinstance3:T
if length.fromindirect.state.inst > 0 then
 false
else
 let discard = finishStart.encodingnumber.inst
 true

builtin finishStart(eno:int) einfo.T

Function empty:encodingstate.T encodingstate.T
let x = constantseq(4, empty:seq.encodingpair.T)
encodingstate(empty:seq.encodingpair.T, 0, x, to:encoding.T(0))

type encodingpair is data:T, code:encoding.T, hash:int

function =(a:encodingpair.T, b:encodingpair.T) boolean
hash.a = hash.b ∧ valueofencoding.code.a = valueofencoding.code.b ∧ data.a = data.b

unbound hash(T) int

unbound =(T, T) boolean

Function lastadded(h:encodingstate.T) encoding.T code.last.all.h

function notsamehash:T(a:int, b:int, mask:bits) boolean
(bits.a ∧ mask) ≠ (bits.b ∧ mask)

builtin deepcopy(T) T

Function addencoding(h:encodingstate.T, data:T) encodingstate.T
{this is the add that is called by primitiveadd}
let datav = deepcopy.data
let hashv = hash.datav
let tablesize = length.encodetable.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
let dataindex = toint(tobits.hashv ∧ mask) + 1
let existingcode = lookuprep(datav, (encodetable.h)_dataindex)
if not.isempty.existingcode then
 {already present}
 let c = code.existingcode_1
 if lastadd.h = c then h else encodingstate(all.h, length.h, encodetable.h, c)
else
 let code = to:encoding.T(length.all.h + 1)
 let p = encodingpair(datav, code, hashv)
 let codeindex = toint(tobits.valueofencoding.code ∧ mask) + 1
 let listencode = 
  for acc = [p], e ∈ (encodetable.h)_dataindex do
   if data.e = data.p ∨ notsamehash:T(hash.p, hash.e, mask) then acc else acc + e
  /for (acc)
 let newencode = replace(encodetable.h, dataindex, listencode)
 if 3 * length.h > 2 * tablesize then
  encodingstate(all.h + p
   , length.h + 1
   , newencode + newencode + newencode + newencode
   , code.p)
 else
  encodingstate(all.h + p, length.h + 1, newencode, code.p)

Function addencodings(l:seq.T) int
let inst = getinstance3:T
for acc = to:encoding.T(0), @e ∈ l do primitiveadd(inst, @e) /for (0)

Function decode(t:encoding.T) T
let h = encodingstate.getinstance3:T
assert between(valueofencoding.t, 1, length.all.h)
report "no such encoding" + toword.valueofencoding.t + stacktrace
data.(all.h)_(valueofencoding.t)

type einfo is state:indirect.encodingstate.T, encodingnumber:int, allocatein:ptr

function encodingstate(e:einfo.T) encodingstate.T fromindirect.state.e

builtin getinstance3:T einfo.T

Function add1encoding(p:ptr, data:T) encoding.T
{???? ptr time is used instead of einfo since einfo is also defined in encodingsupport}
let e = bitcast:einfo.T(p)
let t = addencoding(fromindirect.state.e, data)
let discard = set(toptr.e, toptr.t)
lastadd.t

builtin primitiveadd(e:einfo.T, s:T) encoding.T

type e3 is sequence, data:seq.encodingpair.T

function _(a:e3.T, i:int) T data.(data.a)_i

Function encodingdata:T seq.T
let t = all.encodingstate.getinstance3:T
toseq.e3(length.t, t)

Function encode(t:T) encoding.T
let instance = getinstance3:T
let r = lookuprep(t, encodingstate.instance)
if isempty.r then primitiveadd(instance, t) else code.r_1

Function =(a:encoding.T, b:encoding.T) boolean valueofencoding.a = valueofencoding.b

Function >1(a:encoding.T, b:encoding.T) ordering valueofencoding.a >1 valueofencoding.b

Function hash(a:encoding.T) int valueofencoding.a

function lookuprep(t:T, inst:encodingstate.T) seq.encodingpair.T
lookuprep(t, (encodetable.inst)_(hash.t mod length.encodetable.inst + 1))

function lookuprep(t:T, s:seq.encodingpair.T) seq.encodingpair.T
for acc = empty:seq.encodingpair.T, e ∈ s do
 if t = data.e then acc + e else acc
/for (acc)

Function findencode(t:T) seq.T
let r = lookuprep(t, encodingstate.getinstance3:T)
if isempty.r then empty:seq.T else [data.r_1]

Function addorder(t:T) int valueofencoding.encode.t

function analyze(t:encodingstate.T) seq.word
"numele =" + toword.length.all.t + "encodecounts" + counts(encodetable.t, 1, 0, 0, 0)

function counts(s:seq.seq.encodingpair.T, i:int, one:int, two:int, big:int) seq.word
if i > length.s then
 for acc = "", @e ∈ [length.s, one, two, big] do acc + toword.@e /for (acc)
else
 let t = length.s_i
 if t = 0 then
  counts(s, i + 1, one, two, big)
 else if t = 1 then
  counts(s, i + 1, one + 1, two, big)
 else if t = 2 then
  counts(s, i + 1, one, two + 1, big)
 else
  counts(s, i + 1, one, two, big + 1) 