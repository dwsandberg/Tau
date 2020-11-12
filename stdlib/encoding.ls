Module encoding.T

use otherseq.encodingpair.T

use otherseq.seq.encodingpair.T

use seq.seq.encodingpair.T

use seq.encodingpair.T

use seq.encodingstate.T

use process.T

use seq.T

use stacktrace

use stdlib

Export type:encodingpair.T

Export type:encoding.T

Export type:encodingstate.T

type encodingstate is sequence length:int, encodetable:seq.seq.encodingpair.T, decodetable:seq.seq.encodingpair.T, all:seq.encodingpair.T

Export length(e:encodingstate.T)int

Function_(e:encodingstate.T, i:int)T data.(all.e)_i

type encodingpair is record code:encoding.T, data:T, hash:int

Export code(a:encodingpair.T)encoding.T

Export data(a:encodingpair.T)T

Function encodingpair(code:encoding.T, data:T)encodingpair.T encodingpair(code, data, hash.data)

Export hash(a:encodingpair.T)int

Function =(a:encodingpair.T, b:encodingpair.T)boolean
 hash.a = hash.b ∧ valueofencoding.code.a = valueofencoding.code.b
 ∧ data.a = data.b

Function ?(a:encodingpair.T, b:encodingpair.T)ordering valueofencoding.code.a ? valueofencoding.code.b

unbound hash(T)int

unbound =(T, T)boolean

Function empty:encodingstate.T encodingstate.T
let x = constantseq(4, empty:seq.encodingpair.T)
 encodingstate(0, x, x, empty:seq.encodingpair.T)

function adddata(eletoadd:encodingpair.T, tablesize:int, a:encodingpair.T)seq.encodingpair.T
 if data.a = data.eletoadd ∨ hash.eletoadd mod tablesize ≠ hash.a mod tablesize then
 empty:seq.encodingpair.T
 else [ a]

function addcode(code:encoding.T, hashsize:int, x:seq.encodingpair.T, e:encodingpair.T)seq.encodingpair.T
 if code.e = code ∨ valueofencoding.code mod hashsize ≠ valueofencoding.code.e mod hashsize then
 x
 else x + e

type encoding is record valueofencoding:int

Export valueofencoding(a:encoding.T)int

Function to:encoding.T(i:int)encoding.T encoding.i

Function lastadded(h:encodingstate.T)encoding.T code.last.all.h

Function add(h:encodingstate.T, v:encodingpair.T)encodingstate.T
 // this is the add that is stored in the erecord //
 let tablesize = length.encodetable.h
  if 3 * length.h > 2 * tablesize then
  let t = encodetable.h
   let d = decodetable.h
    add(encodingstate(length.h, t + t + t + t, d + d + d + d, all.h)
    , v)
  else
   let datahash = hash.v
   let dataindex = datahash mod tablesize + 1
    if @(max, ele.data.v, 0,(encodetable.h)_dataindex) > 0 then // already present // h
    else
     let p = subadd(h, v, 1)
     let codeindex = valueofencoding.code.p mod tablesize + 1
     let l1 = @(addcode(code.p, tablesize), identity, [ p],(decodetable.h)_codeindex)
     let l2 = @(+, adddata(p, tablesize), [ p],(encodetable.h)_dataindex)
     let newdecodetable = replace(decodetable.h, codeindex, l1)
     let newencodetable = replace(encodetable.h, dataindex, l2)
      encodingstate(length.h + 1, newencodetable, newdecodetable, all.h + p)

function used(t:encoding.T, a:encodingpair.T)int if t = code.a then 1 else 0

function subadd(h:encodingstate.T, v:encodingpair.T, count:int)encodingpair.T
 // assert count < 10 report"unable to assign encoding"//
 let tablesize = length.encodetable.h
 let code = code.v
 let codeindex = valueofencoding.code mod tablesize + 1
 let found = valueofencoding.code.v ≤ 0 ∨ @(+, used.code.v, 0,(decodetable.h)_codeindex) > 0
  if found then
  subadd(h, encodingpair(to:encoding.T(assignencoding(length.h, data.v)), data.v, hash.v), count + 1)
  else encodingpair(code.v, deepcopy.data.v, hash.v)

unbound assignencoding(length:int, data:T)int //(randomint.1)_1 //

Function assignrandom(length:int, data:T)int(randomint.1)_1

Function addencodingpairs(l:seq.encodingpair.T)encodingstate.T @(add, rehash, getinstance:encodingstate.T, l)

function rehash(a:encodingpair.T)encodingpair.T encodingpair(code.a, data.a)

Function lookupencodingpair(t:encoding.T)seq.encodingpair.T
 let inst = getinstance:encodingstate.T
  decode(inst, t)

Function decode(t:encoding.T)T
 let inst = getinstance:encodingstate.T
 let a = decode(inst, t)
  assert length.a = 1 report"no such encoding" + toword.valueofencoding.t + stacktrace
   data.a_1

Builtin getinstance:encodingstate.T encodingstate.T

Builtin primitiveadd(s:encodingpair.T)int

Function encoding:seq.encodingpair.T seq.encodingpair.T all.getinstance:encodingstate.T

Function encode(t:T)encoding.T
 let r = lookuprep(t, getinstance:encodingstate.T)
  if isempty.r then
  let discard = primitiveadd.encodingpair(to:encoding.T(0), t, hash.t)
    encode.t
  else code.r_1

function decode(h:encodingstate.T, t:encoding.T)seq.encodingpair.T
 @(+, ele4.t, empty:seq.encodingpair.T,(decodetable.h)_(valueofencoding.t mod length.decodetable.h + 1))

function ele4(t:encoding.T, a:encodingpair.T)seq.encodingpair.T
 if t = code.a then [ a]else empty:seq.encodingpair.T

Function =(a:encoding.T, b:encoding.T)boolean valueofencoding.a = valueofencoding.b

Function ?(a:encoding.T, b:encoding.T)ordering valueofencoding.a ? valueofencoding.b

Function hash(a:encoding.T)int valueofencoding.a

function lookuprep(t:T, inst:encodingstate.T)seq.encodingpair.T
 @(+, ele5.t, empty:seq.encodingpair.T,(encodetable.inst)_(hash.t mod length.encodetable.inst + 1))

function ele(v:T, a:encodingpair.T)int if v = data.a then valueofencoding.code.a else 0

Export type:encodingpair.T

function ele5(v:T, a:encodingpair.T)seq.encodingpair.T if v = data.a then [ a]else empty:seq.encodingpair.T

Function findencode(t:T)seq.T
 let r = lookuprep(t, getinstance:encodingstate.T)
  if isempty.r then empty:seq.T else [ data.r_1]

Function analyze(t:encodingstate.T)seq.word
 "numele =" + toword.length.all.t + "encodecounts" + counts(encodetable.t, 1, 0, 0, 0)
 + "decodeconuts"
 + counts(decodetable.t, 1, 0, 0, 0)

function counts(s:seq.seq.encodingpair.T, i:int, one:int, two:int, big:int)seq.word
 if i > length.s then @(+, toword,"", [ length.s, one, two, big])
 else
  let t = length.s_i
   if t = 0 then counts(s, i + 1, one, two, big)
   else if t = 1 then counts(s, i + 1, one + 1, two, big)
   else if t = 2 then counts(s, i + 1, one, two + 1, big)
   else counts(s, i + 1, one, two, big + 1)

module assignencodingnumber

use seq.seq.int

use seq.int

use stdlib

use encoding.typename

type typename is record name:seq.word

function =(a:typename, b:typename)boolean name.a = name.b

function hash(a:typename)int hash.name.a

Function encodingno(name:seq.word)int
 if name = "char seq"then 1
 else if name = "typename"then 2 else valueofencoding.encode.typename.name + 2

function assignencoding(a:int, typename)int a + 1

builtin IDX(seq.int, int)int

builtin setfld(seq.int, int, int)int

builtin allocatespace(i:int)seq.int

Function memcpy(i:int, memsize:int, s:seq.int, idx:int, fromaddress:seq.int)int
 if memsize = 0 then idx
 else memcpy(i + 1, memsize - 1, s, setfld(s, idx, IDX(fromaddress, i)), fromaddress)

Function packed1(s:seq.int)seq.int
 // for use where the element type is represented in 64bits. //
 if length.s > blocksize then
 let r = bitcast
  .packed
  .@(+, subblock(s), empty:seq.seq.int, arithseq((length.s + blocksize - 1) / blocksize, blocksize, 1))
  let k = setfld(r, setfld(r, 0, blockindexfunc), length.s)
   r
 else
  let newseq = allocatespace(length.s + 2)
  let a = setfld(newseq, setfld(newseq, 0, 0), length.s)
  let d = @(setfld.newseq, identity, 2, s)
   newseq

Function packed(s:seq.seq.int, ds:int)seq.int packed(ds, s)

Function packed(ds:int, s:seq.seq.int)seq.int
 // for use where the element type is represented in ds * 64bits where ds > 1. //
 // if the length < = blocksize then the result is represented as <ds> <length> <fld1.s_1><fld2.s_1>... <fld1.s_2><fld2.s_2>.... //
 // if the length > bloocksize then result is represented as <blockindexfunc> <length> <packed.subseq(s, 1, blocksize)> <packed.subseq(s, blocksize + 1, 2*blocksize)>.....//
 if length.s > blocksize then
 let r = bitcast
  .packed
  .@(+, subblock(ds, s), empty:seq.seq.int, arithseq((length.s + blocksize - 1) / blocksize, blocksize, 1))
  let k = setfld(r, setfld(r, 0, blockindexfunc), length.s)
   r
 else
  let newseq = allocatespace(length.s * ds + 2)
  let a = setfld(newseq, setfld(newseq, 0, ds), length.s)
  let d = @(memcpy(0, ds, newseq), identity, 2, s)
   newseq

builtin bitcast(a:seq.seq.int)seq.int

builtin IDX(seq.seq.int, int)seq.int

builtin blockindexfunc int

function blocksize int 10000

Function indexblocks(a:seq.seq.int, i:int)int
 assert between(i, 1, length.a)report"out of bounds"
  IDX(a,(i - 1) / blocksize + 2)_((i - 1) mod blocksize + 1)

function subblock(s:seq.int, i:int)seq.int packed.subseq(s, i, i + blocksize - 1)

function subblock(ds:int, s:seq.seq.int, i:int)seq.int
 packed(ds, subseq(s, i, i + blocksize - 1))