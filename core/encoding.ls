Module encoding.T

use seq.encodingpair.T

use otherseq.seq.encodingpair.T

use indirect.encodingstate.T

use seq.T

use bits

use ptr

use standard

builtin set2(ptr, encodingstate.T) ptr

Export type:encoding.T

Export valueofencoding(a:encoding.T) int

type encoding is valueofencoding:int

Function to:encoding.T(i:int) encoding.T encoding.i

type encodingstate is
all:seq.encodingpair.T
, length:int
, encodetable:seq.seq.encodingpair.T
, lastadd:encoding.T

Export type:encodingstate.T

Export length(encodingstate.T) int

Function startInParent:T boolean
let inst = getinstance3:T,
if length.fromindirect.state.inst > 0 then
false
else let discard = finishStart:T(encodingnumber.inst), true

builtin finishStart:T(eno:int) einfo.T

Function empty:encodingstate.T encodingstate.T
let x = constantseq(4, empty:seq.encodingpair.T),
encodingstate(empty:seq.encodingpair.T, 0, x, to:encoding.T(0))

type encodingpair is data:T, code:encoding.T, hash:int

function =(a:encodingpair.T, b:encodingpair.T) boolean
hash.a = hash.b ∧ valueofencoding.code.a = valueofencoding.code.b ∧ data.a = data.b

unbound hash(T) int

unbound =(T, T) boolean

Function lastadded(h:encodingstate.T) encoding.T code.1^all.h

function notsamehash:T(a:int, b:int, mask:bits) boolean
(bits.a ∧ mask) ≠ (bits.b ∧ mask)

builtin deepcopy(T) T

Function addencoding(h:encodingstate.T, data:T) encodingstate.T
{this is the add that is called by primitiveadd}
let datav = deepcopy.data
let hashv = hash.datav
let tablesize = n.encodetable.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
let dataindex = toint(tobits.hashv ∧ mask) + 1
let existingcode = lookuprep2(datav, dataindex#encodetable.h),
if not.isempty.existingcode then
 {already presen}
 let c = code.1#existingcode,
 if lastadd.h = c then h else encodingstate(all.h, length.h, encodetable.h, c)
else
 let code = to:encoding.T(n.all.h + 1)
 let p = encodingpair(datav, code, hashv)
 let codeindex = toint(tobits.valueofencoding.code ∧ mask) + 1
 for listencode = [p], e ∈ dataindex#encodetable.h
 do
  if data.e = data.p ∨ notsamehash:T(hash.p, hash.e, mask) then
  listencode
  else listencode + e
 let newencode = replace(encodetable.h, dataindex, listencode),
  if 3 * length.h > 2 * tablesize then
  encodingstate(all.h + p, length.h + 1, newencode + newencode + newencode + newencode, code.p)
  else encodingstate(all.h + p, length.h + 1, newencode, code.p)

Function addencodings(l:seq.T) int
let inst = getinstance3:T
for acc = to:encoding.T(0), @e ∈ l do primitiveadd(inst, @e),
0

Function decode(t:encoding.T) T
let h = encodingstate.getinstance3:T
assert between(valueofencoding.t, 1, n.all.h)
report "no such encoding" + toword.valueofencoding.t + stacktrace,
data.(valueofencoding.t)#all.h

type einfo is state:indirect.encodingstate.T, encodingnumber:int, allocatein:ptr

function encodingstate(e:einfo.T) encodingstate.T fromindirect.state.e

builtin getinstance3:T einfo.T

Function add1encoding(p:ptr, data:T) encoding.T
{???? ptr is used instead of einfo since einfo is also defined in encodingsupport}
let t = addencoding(fromindirect.state.bitcast2:einfo.T(p), data)
let discard = set2(p, t),
lastadd.t

builtin bitcast2:einfo.T(ptr) einfo.T

builtin primitiveadd(e:einfo.T, s:T) encoding.T

type e3 is sequence, data:seq.encodingpair.T

function sequenceIndex(a:e3.T, i:int) T data.i#data.a

Function encodingdata:T seq.T let t = all.encodingstate.getinstance3:T, toseq.e3(n.t, t)

Function encode(t:T) encoding.T
let instance = getinstance3:T
let r = lookuprep(t, encodingstate.instance),
if isempty.r then primitiveadd(instance, t) else code.1#r

Function =(a:encoding.T, b:encoding.T) boolean valueofencoding.a = valueofencoding.b

Function >1(a:encoding.T, b:encoding.T) ordering valueofencoding.a >1 valueofencoding.b

Function hash(a:encoding.T) int valueofencoding.a

function lookuprep(t:T, inst:encodingstate.T) seq.encodingpair.T
let mask = bits.-1 >> (65 - floorlog2.n.encodetable.inst)
let dataindex = toint(tobits.hash.t ∧ mask) + 1,
lookuprep2(t, dataindex#encodetable.inst)

function lookuprep2(t:T, s:seq.encodingpair.T) seq.encodingpair.T
for acc = empty:seq.encodingpair.T, e ∈ s do if t = data.e then acc + e else acc,
acc

Function findencode(t:T) seq.T
let r = lookuprep(t, encodingstate.getinstance3:T),
if isempty.r then empty:seq.T else [data.1#r]

Function addorder(t:T) int valueofencoding.encode.t

function analyze(t:encodingstate.T) seq.word
"numele =" + toword.n.all.t + "encodecounts" + counts(encodetable.t, 1, 0, 0, 0)

function counts(s:seq.seq.encodingpair.T, i:int, one:int, two:int, big:int) seq.word
if i > n.s then
for acc = "", @e ∈ [n.s, one, two, big] do acc + toword.@e, acc
else
 let t = n.i#s,
  if t = 0 then
  counts(s, i + 1, one, two, big)
  else if t = 1 then
  counts(s, i + 1, one + 1, two, big)
  else if t = 2 then
  counts(s, i + 1, one, two + 1, big)
  else counts(s, i + 1, one, two, big + 1)
 