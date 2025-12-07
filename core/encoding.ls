Module encoding.T

use seq.encodingpair.T

use seq1.seq.encodingpair.T

use indirect.encodingstate.T

use seq.T

use bits

use kernal

use ptr

use word

use seq.word

Export type:encoding.T

Export valueofencoding(a:encoding.T) int

Export type:encodingstate.T

Export length(encodingstate.T) int

builtin set(ptr, encodingstate.T) ptr

type encoding is valueofencoding:int

Function to:encoding.T(i:int) encoding.T encoding.i

type encodingstate is
all:seq.encodingpair.T
, length:int
, encodetable:seq.seq.encodingpair.T
, lastadd:encoding.T

Function startInParent:T boolean
let inst = getinstance3:T,
if length.fromindirect.state.inst > 0 then false
else
 let discard = finishStart:T(encodingnumber.inst),
 true

builtin finishStart:T(eno:int) einfo.T

Function empty:encodingstate.T encodingstate.T
let e = empty:seq.encodingpair.T,
encodingstate(e, 0, [e, e, e, e], to:encoding.T(0))

type encodingpair is data:T, code:encoding.T, hash:int

function =(a:encodingpair.T, b:encodingpair.T) boolean
hash.a = hash.b ∧ valueofencoding.code.a = valueofencoding.code.b ∧ data.a = data.b

unbound hash(T) int

unbound =(T, T) boolean

Function lastadded(h:encodingstate.T) encoding.T code.(all.h) sub n.all.h

function notsamehash:T(a:int, b:int, mask:bits) boolean
(bits.a ∧ mask) ≠ (bits.b ∧ mask)

builtin deepcopy(T) T

Function addencoding(h:encodingstate.T, data:T) encodingstate.T
{this is the add that is called by primitiveadd}
let datav = deepcopy.data
let hashv = hash.datav
let tablesize = n.encodetable.h
let mask = bits.-1 >> (64 - floorLog2.tablesize)
let dataindex = toint(tobits.hashv ∧ mask) + 1
let existingcode = lookuprep2(datav, (encodetable.h) sub dataindex),
if not.isempty.existingcode then
 {already present}
 let c = code.existingcode sub 1,
 if lastadd.h = c then h else encodingstate(all.h, length.h, encodetable.h, c)
else
 let code = to:encoding.T(n.all.h + 1)
 let p = encodingpair(datav, code, hashv)
 let codeindex = toint(tobits.valueofencoding.code ∧ mask) + 1
 for listencode = [p], e ∈ (encodetable.h) sub dataindex
 do
  if data.e = data.p ∨ notsamehash:T(hash.p, hash.e, mask) then listencode
  else listencode + e
 let etable = encodetable.h
 let newencode = replace(encodetable.h, dataindex, listencode),
 {subseq(etable, 1, dataindex-1)+listencode+subseq(etable, dataindex+1, n.etable)}
 if 3 * length.h > 2 * tablesize then encodingstate(all.h + p, length.h + 1, newencode + newencode + newencode + newencode, code.p)
 else encodingstate(all.h + p, length.h + 1, newencode, code.p)

Function addencodings(l:seq.T) int
let inst = getinstance3:T
for acc = to:encoding.T(0), @e ∈ l do primitiveadd(inst, @e),
0

Function decode(t:encoding.T) T
let h = encodingstate.getinstance3:T
assert between(valueofencoding.t, 1, n.all.h) report "no such encoding" + toword.valueofencoding.t + stacktrace,
data.(all.h) sub valueofencoding.t

type einfo is state:indirect.encodingstate.T, encodingnumber:int, allocatein:ptr

function encodingstate(e:einfo.T) encodingstate.T fromindirect.state.e

builtin getinstance3:T einfo.T

Function add1encoding(p:ptr, data:T) encoding.T
{ptr is used instead of einfo since einfo is also defined in encodingsupport}
let t = addencoding(fromindirect.state.bitcast2:einfo.T(p), data)
let discard = set(p, t),
lastadd.t

builtin bitcast2:einfo.T(ptr) einfo.T

builtin primitiveadd(e:einfo.T, s:T) encoding.T

type e3 is sequence, data:seq.encodingpair.T

function sequenceIndex(a:e3.T, i:int) T data.(data.a) sub i

Function encodingdata:T seq.T
let t = all.encodingstate.getinstance3:T,
toseq.e3(n.t, t)

Function encode(t:T) encoding.T
let instance = getinstance3:T
let r = lookuprep(t, encodingstate.instance),
if isempty.r then primitiveadd(instance, t) else code.r sub 1

Function =(a:encoding.T, b:encoding.T) boolean valueofencoding.a = valueofencoding.b

Function >1(a:encoding.T, b:encoding.T) ordering valueofencoding.a >1 valueofencoding.b

Function hash(a:encoding.T) int valueofencoding.a

function lookuprep(t:T, inst:encodingstate.T) seq.encodingpair.T
let mask = bits.-1 >> (64 - floorLog2.n.encodetable.inst)
let dataindex = toint(tobits.hash.t ∧ mask) + 1,
lookuprep2(t, (encodetable.inst) sub dataindex)

function lookuprep2(t:T, s:seq.encodingpair.T) seq.encodingpair.T
for acc = empty:seq.encodingpair.T, e ∈ s do if t = data.e then acc + e else acc,
acc

Function findencode(t:T) seq.T
let r = lookuprep(t, encodingstate.getinstance3:T),
if isempty.r then empty:seq.T else [data.r sub 1]

Function addorder(t:T) int valueofencoding.encode.t

function analyze(t:encodingstate.T) seq.word
 "numele =" + toword.n.all.t + "encodecounts" + counts(encodetable.t, 1, 0, 0, 0)

function counts(s:seq.seq.encodingpair.T, i:int, one:int, two:int, big:int) seq.word
if i > n.s then
 for acc = "", @e ∈ [n.s, one, two, big] do acc + toword.@e,
 acc
else
 let t = n.s sub i,
 if t = 0 then counts(s, i + 1, one, two, big)
 else if t = 1 then counts(s, i + 1, one + 1, two, big)
 else if t = 2 then counts(s, i + 1, one, two + 1, big)
 else counts(s, i + 1, one, two, big + 1)
 