Module encoding.T

use otherseq.seq.encodingpair.T

use seq.seq.encodingpair.T

use seq.encodingpair.T

use seq.encodingstate.T

use seq.T

use stacktrace

use stdlib

Export type:encodingpair.T

Export type:encoding.T

Export type:encodingstate.T

type encodingstate is sequence length:int, encodetable:seq.seq.encodingpair.T, decodetable:seq.seq.encodingpair.T, all:seq.encodingpair.T, lastadd:int

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
 encodingstate(0, x, x, empty:seq.encodingpair.T, 0)

function adddata(eletoadd:encodingpair.T, tablesize:int, a:encodingpair.T)seq.encodingpair.T
 if data.a = data.eletoadd ∨ hash.eletoadd mod tablesize ≠ hash.a mod tablesize then
 empty:seq.encodingpair.T
 else [ a]

function addcode(x:seq.encodingpair.T,code:encoding.T, hashsize:int,  e:encodingpair.T)seq.encodingpair.T
 if code.e = code ∨ valueofencoding.code mod hashsize ≠ valueofencoding.code.e mod hashsize then
 x
 else x + e

type encoding is record valueofencoding:int

Export valueofencoding(a:encoding.T)int

Function to:encoding.T(i:int)encoding.T encoding.i

Function lastadded(h:encodingstate.T)encoding.T code.last.all.h

Function add(h:encodingstate.T, v:encodingpair.T)encodingstate.T
 // this is the add that is called by primitiveadd //
 let tablesize = length.encodetable.h
 let datahash = hash.v
 let dataindex = datahash mod tablesize + 1
 let existingcode =(encodetable.h)_dataindex @@ +(empty:seq.encodingpair.T, ele5(data.v, @e))
  if not.isempty.existingcode then
  // already present //
   let c = valueofencoding.code.existingcode_1
    if lastadd.h = c then h else encodingstate(length.h, encodetable.h, decodetable.h, all.h, c)
  else
   let p = subadd(h, v, 1)
   let codeindex = valueofencoding.code.p mod tablesize + 1
   let l1 = (decodetable.h)_codeindex @@ addcode([p],code.p, tablesize,@e) 
   let l2 =(encodetable.h)_dataindex @@ +([ p], adddata(p, tablesize, @e))
   let newdecode = replaceZ(decodetable.h, codeindex, l1)
   let newencode = replaceZ(encodetable.h, dataindex, l2)
    if 3 * length.h > 2 * tablesize then
    let t = newencode
     let d = newdecode
      encodingstate(length.h + 1, t + t + t + t, d + d + d + d, all.h + p, valueofencoding.code.p)
    else encodingstate(length.h + 1, newencode, newdecode, all.h + p, valueofencoding.code.p)

function used(t:encoding.T, a:encodingpair.T)int if t = code.a then 1 else 0

function subadd(h:encodingstate.T, v:encodingpair.T, count:int)encodingpair.T
 // assert count < 10 report"unable to assign encoding"//
 let tablesize = length.encodetable.h
 let code = code.v
 let codeindex = valueofencoding.code mod tablesize + 1
 let found = valueofencoding.code.v ≤ 0
 ∨ (decodetable.h)_codeindex @@ +(0, used(code.v, @e)) > 0
  if found then
  subadd(h, encodingpair(to:encoding.T(assignencoding(length.h, data.v)), data.v, hash.v), count + 1)
  else encodingpair(code.v, data.v, hash.v)

unbound assignencoding(length:int, data:T)int //(randomint.1)_1 //

Function assignrandom(length:int, data:T)int(randomint.1)_1

Function addencodingpairs(l:seq.encodingpair.T)encodingstate.T l @@ add(getinstance:encodingstate.T, rehash.@e)

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
  if isempty.r then to:encoding.T(primitiveadd.encodingpair(to:encoding.T(0), t, hash.t))
  else code.r_1

function decode(h:encodingstate.T, t:encoding.T)seq.encodingpair.T
 (decodetable.h)_(valueofencoding.t mod length.decodetable.h + 1)
 @@ +(empty:seq.encodingpair.T, ele4(t, @e))

function ele4(t:encoding.T, a:encodingpair.T)seq.encodingpair.T
 if t = code.a then [ a]else empty:seq.encodingpair.T

Function =(a:encoding.T, b:encoding.T)boolean valueofencoding.a = valueofencoding.b

Function ?(a:encoding.T, b:encoding.T)ordering valueofencoding.a ? valueofencoding.b

Function hash(a:encoding.T)int valueofencoding.a

function lookuprep(t:T, inst:encodingstate.T)seq.encodingpair.T
 (encodetable.inst)_(hash.t mod length.encodetable.inst + 1)
 @@ +(empty:seq.encodingpair.T, ele5(t, @e))

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
 if i > length.s then [ length.s, one, two, big] @@ +("", toword.@e)
 else
  let t = length.s_i
   if t = 0 then counts(s, i + 1, one, two, big)
   else if t = 1 then counts(s, i + 1, one + 1, two, big)
   else if t = 2 then counts(s, i + 1, one, two + 1, big)
   else counts(s, i + 1, one, two, big + 1)

module assignencodingnumber

use encoding.seq.char

use seq.seq.int

use seq.int

use stdlib

use encoding.typename

Export decode(encoding.seq.char)seq.char

Export encode(seq.char)encoding.seq.char

Function deepcopy(a:int)int a

Function deepcopy(a:real)real a

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

Function memcpy(idx:int,i:int, memsize:int, s:seq.int,  fromaddress:seq.int)int
 if memsize = 0 then idx
 else memcpy(setfld(s, idx, IDX(fromaddress, i)),i + 1, memsize - 1, s,  fromaddress)

Function packed1(s:seq.int)seq.int
 // for use where the element type is represented in 64bits. //
 if length.s > blocksize then
 let r = bitcast
  .packed(arithseq((length.s + blocksize - 1) / blocksize, blocksize, 1)
  @@ +(empty:seq.seq.int, subblock(s, @e)))
  let k = setfld(r, setfld(r, 0, blockindexfunc), length.s)
   r
 else
  let newseq = allocatespace(length.s + 2)
  let a = setfld(newseq, setfld(newseq, 0, 0), length.s)
  let d = s @@  setfld(2,newseq,@e)  
   newseq

function setfld(i:int,s:seq.int,val:int)  int setfld(s,i,val)

Function packed(s:seq.seq.int, ds:int)seq.int packed(ds, s)

Function packed(ds:int, s:seq.seq.int)seq.int
 // for use where the element type is represented in ds * 64bits where ds > 1. //
 // if the length < = blocksize then the result is represented as <ds> <length> <fld1.s_1><fld2.s_1>... <fld1.s_2><fld2.s_2>.... //
 // if the length > bloocksize then result is represented as <blockindexfunc> <length> <packed.subseq(s, 1, blocksize)> <packed.subseq(s, blocksize + 1, 2*blocksize)>.....//
 if length.s > blocksize then
 let r = bitcast
  .packed(arithseq((length.s + blocksize - 1) / blocksize, blocksize, 1)
  @@ +(empty:seq.seq.int, subblock(ds, s, @e)))
  let k = setfld(r, setfld(r, 0, blockindexfunc), length.s)
   r
 else
  let newseq = allocatespace(length.s * ds + 2)
  let a = setfld(newseq, setfld(newseq, 0, ds), length.s)
  let d = s @@ memcpy( 2,0, ds, newseq,@e) 
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