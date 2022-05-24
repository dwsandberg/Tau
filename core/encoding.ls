Module encoding.T

use bits

use standard

use seq.T

use seq.encodingpair.T

use seq.encodingstate.T

use otherseq.seq.encodingpair.T

Export type:encodingpair.T

Export type:encoding.T

Export code(a:encodingpair.T)encoding.T

Export data(a:encodingpair.T)T

Export hash(a:encodingpair.T)int

Export valueofencoding(a:encoding.T)int

type encoding is valueofencoding:int

Function to:encoding.T(i:int)encoding.T encoding.i

type encodingstate is encodingno:int
, length:int
, encodetable:seq.seq.encodingpair.T
, decodetable:seq.seq.encodingpair.T
, all:seq.encodingpair.T
, lastadd:int


function encodingstate(encodingno:int
, length:int
, encodetable:seq.seq.encodingpair.T
, all:seq.encodingpair.T
, lastadd:int
)encodingstate.T
encodingstate(0, length, encodetable, encodetable, all, lastadd)

/function_(e:encodingstate.T, i:int)T data.(all.e)_i

type encodingpair is code:encoding.T, data:T, hash:int

Function encodingpair(code:encoding.T, data:T)encodingpair.T encodingpair(code, data, hash.data)

Function =(a:encodingpair.T, b:encodingpair.T)boolean
hash.a = hash.b ∧ valueofencoding.code.a = valueofencoding.code.b ∧ data.a = data.b

unbound hash(T)int

unbound=(T, T)boolean

Export type:seq.encodingpair.T

Export length(seq.encodingpair.T)int

/Function empty:encodingstate.T encodingstate.T let x=constantseq(4, empty:seq.encodingpair.T)encodingstate 
(0, 0, x, x, empty:seq.encodingpair.T, 0)

Function lastadded(h:encodingstate.T)encoding.T code.last.all.h

function notsamehash:T(a:int, b:int, mask:bits)boolean(bits.a ∧ mask) ≠ (bits.b ∧ mask)

/Function add(h:encodingstate.T, datav:T)

Function add(h:encodingstate.T, v:encodingpair.T)encodingstate.T addencoding(h, data.v)

Function addencoding(h:encodingstate.T, datav:T)encodingstate.T
{this is the add that is called by primitiveadd}
let hashv = hash.datav
let tablesize = length.encodetable.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
let dataindex = toint(tobits.hashv ∧ mask) + 1
let existingcode = lookuprep(datav, (encodetable.h)_dataindex)
if not.isempty.existingcode then
 {already present}
 let c = valueofencoding.code.existingcode_1
 if lastadd.h = c then h
 else encodingstate(encodingno.h, length.h, encodetable.h, decodetable.h, all.h, c)
else
 let code = to:encoding.T(length.all.h + 1)
 let p = encodingpair(code, datav, hashv)
 let codeindex = toint(tobits.valueofencoding.code ∧ mask) + 1
 let listencode = 
  for acc = [p], e ∈(encodetable.h)_dataindex do
   if data.e = data.p ∨ notsamehash:T(hash.p, hash.e, mask)then acc else acc + e
  /for(acc)
 let newencode = replace(encodetable.h, dataindex, listencode)
 if 3 * length.h > 2 * tablesize then
  encodingstate(encodingno.h
  , length.h + 1
  , newencode + newencode + newencode + newencode
  , decodetable.h
  , all.h + p
  , valueofencoding.code.p
  )
 else
  encodingstate(encodingno.h, length.h + 1, newencode, decodetable.h, all.h + p, valueofencoding.code.p)

Function addencodingpairs(l:seq.encodingpair.T)int
let inst = getinstance:encodingstate.T
for acc = 0, @e ∈ l do
 acc + primitiveadd(encodingno.inst, encodingpair(to:encoding.T(0), data.@e, hash.data.@e))
/for(acc)

Function lookupencodingpair(t:encoding.T)seq.encodingpair.T
let inst = getinstance:encodingstate.T
decode(inst, t)

/Function encodingnumber:T int encodingno.getinstance:encodingstate.T

Function decode(t:encoding.T)T
let a = lookupencodingpair.t
assert length.a = 1 report"no such encoding" + toword.valueofencoding.t + stacktrace
data.a_1

builtin getinstance:encodingstate.T encodingstate.T

builtin primitiveadd(encodingnumber:int, s:encodingpair.T)int

Function encoding:seq.encodingpair.T seq.encodingpair.T all.getinstance:encodingstate.T

type e3 is sequence, data:seq.encodingpair.T

function _(a:e3.T, i:int)T data.(data.a)_i

Function encodingdata:T seq.T
let t = all.getinstance:encodingstate.T
toseq.e3(length.t, t)

Function encode(t:T)encoding.T
let instance = getinstance:encodingstate.T
let r = lookuprep(t, instance)
if isempty.r then
 to:encoding.T(primitiveadd(encodingno.instance, encodingpair(to:encoding.T(0), t, hash.t)))
else code.r_1

function decode(h:encodingstate.T, t:encoding.T)seq.encodingpair.T
if between(valueofencoding.t, 1, length.all.h)then[(all.h)_(valueofencoding.t)]
else empty:seq.encodingpair.T

Function =(a:encoding.T, b:encoding.T)boolean valueofencoding.a = valueofencoding.b

Function ?(a:encoding.T, b:encoding.T)ordering valueofencoding.a ? valueofencoding.b

Function hash(a:encoding.T)int valueofencoding.a

function lookuprep(t:T, inst:encodingstate.T)seq.encodingpair.T lookuprep(t, (encodetable.inst)_(hash.t mod length.encodetable.inst + 1))

function lookuprep(t:T, s:seq.encodingpair.T)seq.encodingpair.T
for acc = empty:seq.encodingpair.T, e ∈ s do if t = data.e then acc + e else acc /for(acc)

Function findencode(t:T)seq.T
let r = lookuprep(t, getinstance:encodingstate.T)
if isempty.r then empty:seq.T else[data.r_1]

Function addorder(t:T)int valueofencoding.encode.t

function analyze(t:encodingstate.T)seq.word
"numele=" + toword.length.all.t + "encodecounts"
+ counts(encodetable.t, 1, 0, 0, 0)

function counts(s:seq.seq.encodingpair.T, i:int, one:int, two:int, big:int)seq.word
if i > length.s then
 for acc = "", @e ∈[length.s, one, two, big]do acc + toword.@e /for(acc)
else
 let t = length.s_i
 if t = 0 then counts(s, i + 1, one, two, big)
 else if t = 1 then counts(s, i + 1, one + 1, two, big)
 else if t = 2 then counts(s, i + 1, one, two + 1, big)else counts(s, i + 1, one, two, big + 1) 