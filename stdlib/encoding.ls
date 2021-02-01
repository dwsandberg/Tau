Module encoding.T

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

type encoding is record valueofencoding:int

Function to:encoding.T(i:int)encoding.T encoding.i

type encodingstate is record encodingno:int, length:int, encodetable:seq.seq.encodingpair.T, decodetable:seq.seq.encodingpair.T, all:seq.encodingpair.T, lastadd:int

/function encodingstate(length:int, encodetable:seq.seq.encodingpair.T, decodetable:seq.seq.encodingpair.T, all:seq.encodingpair.T, lastadd:int)encodingstate.T encodingstate(0, length, encodetable, decodetable, all, lastadd)

/function_(e:encodingstate.T, i:int)T data.(all.e)_i

type encodingpair is record code:encoding.T, data:T, hash:int

Function encodingpair(code:encoding.T, data:T)encodingpair.T encodingpair(code, data, hash.data)

Function =(a:encodingpair.T, b:encodingpair.T)boolean
 hash.a = hash.b ∧ valueofencoding.code.a = valueofencoding.code.b
 ∧ data.a = data.b

Function ?(a:encodingpair.T, b:encodingpair.T)ordering valueofencoding.code.a ? valueofencoding.code.b

unbound hash(T)int

unbound =(T, T)boolean

unbound assignencoding(length:int, data:T)int

/Function empty:encodingstate.T encodingstate.T let x = constantseq(4, empty:seq.encodingpair.T)encodingstate(0, 0, x, x, empty:seq.encodingpair.T, 0)

function adddata(eletoadd:encodingpair.T, tablesize:int, a:encodingpair.T)seq.encodingpair.T
 if data.a = data.eletoadd ∨ hash.eletoadd mod tablesize ≠ hash.a mod tablesize then
 empty:seq.encodingpair.T
 else [ a]

function addcode(x:seq.encodingpair.T, code:encoding.T, hashsize:int, e:encodingpair.T)seq.encodingpair.T
 if code.e = code ∨ valueofencoding.code mod hashsize ≠ valueofencoding.code.e mod hashsize then
 x
 else x + e

Function lastadded(h:encodingstate.T)encoding.T code.last.all.h

Function add(h:encodingstate.T, v:encodingpair.T)encodingstate.T
 \\ this is the add that is called by primitiveadd \\
 let tablesize = length.encodetable.h
 let datahash = hash.v
 let dataindex = datahash mod tablesize + 1
 let existingcode =((for(@e ∈(encodetable.h)_dataindex, acc = empty:seq.encodingpair.T)acc + ele5(data.v, @e)))
  if not.isempty.existingcode then
  \\ already present \\
   let c = valueofencoding.code.existingcode_1
    if lastadd.h = c then h else encodingstate(encodingno.h, length.h, encodetable.h, decodetable.h, all.h, c)
  else
   let p = subadd(h, v, 1)
   let codeindex = valueofencoding.code.p mod tablesize + 1
   let l1 =(for(@e ∈(decodetable.h)_codeindex, acc = [ p])addcode(acc, code.p, tablesize, @e))
   let l2 =((for(@e ∈(encodetable.h)_dataindex, acc = [ p])acc + adddata(p, tablesize, @e)))
   let newdecode = replace(decodetable.h, codeindex, l1)
   let newencode = replace(encodetable.h, dataindex, l2)
    if 3 * length.h > 2 * tablesize then
    let t = newencode
     let d = newdecode
      encodingstate(encodingno.h, length.h + 1, t + t + t + t, d + d + d + d, all.h + p, valueofencoding.code.p)
    else encodingstate(encodingno.h, length.h + 1, newencode, newdecode, all.h + p, valueofencoding.code.p)

function subadd(h:encodingstate.T, v:encodingpair.T, count:int)encodingpair.T
 \\ assert count < 10 report"unable to assign encoding"\\
 let tablesize = length.encodetable.h
 let code = code.v
 let codeindex = valueofencoding.code mod tablesize + 1
 let found = valueofencoding.code.v ≤ 0
 ∨ ((for(@e ∈(decodetable.h)_codeindex, acc = false)acc ∨ code.v = code.@e))
  if found then
  subadd(h, encodingpair(to:encoding.T(assignencoding(length.h, data.v)), data.v, hash.v), count + 1)
  else encodingpair(code.v, data.v, hash.v)

Function assignrandom(length:int, data:T)int(randomint.1)_1

Function addencodingpairs(l:seq.encodingpair.T)int
 let inst = getinstance:encodingstate.T
  {((for(@e ∈ l, acc = 0)acc + primitiveadd(encodingno.inst, rehash.@e)))}

function rehash(a:encodingpair.T)encodingpair.T encodingpair(code.a, data.a)

Function lookupencodingpair(t:encoding.T)seq.encodingpair.T
 let inst = getinstance:encodingstate.T
  decode(inst, t)

Function decode(t:encoding.T)T
 let inst = getinstance:encodingstate.T
 let a = decode(inst, t)
  assert length.a = 1 report"no such encoding" + toword.valueofencoding.t + stacktrace
   data.a_1

builtin getinstance:encodingstate.T encodingstate.T

Builtin primitiveadd(encodingnumber:int, s:encodingpair.T)int

Function encoding:seq.encodingpair.T seq.encodingpair.T all.getinstance:encodingstate.T

Function encode(t:T)encoding.T
 let instance = getinstance:encodingstate.T
 let r = lookuprep(t, instance)
  if isempty.r then
  to:encoding.T(primitiveadd(encodingno.instance, encodingpair(to:encoding.T(0), t, hash.t)))
  else code.r_1

function decode(h:encodingstate.T, t:encoding.T)seq.encodingpair.T
 ((for(@e ∈(decodetable.h)_(valueofencoding.t mod length.decodetable.h + 1), acc = empty:seq.encodingpair.T)acc + ele4(t, @e)))

function ele4(t:encoding.T, a:encodingpair.T)seq.encodingpair.T
 if t = code.a then [ a]else empty:seq.encodingpair.T

Function =(a:encoding.T, b:encoding.T)boolean valueofencoding.a = valueofencoding.b

Function ?(a:encoding.T, b:encoding.T)ordering valueofencoding.a ? valueofencoding.b

Function hash(a:encoding.T)int valueofencoding.a

function lookuprep(t:T, inst:encodingstate.T)seq.encodingpair.T
 ((for(@e ∈(encodetable.inst)_(hash.t mod length.encodetable.inst + 1), acc = empty:seq.encodingpair.T)acc + ele5(t, @e)))

function ele5(v:T, a:encodingpair.T)seq.encodingpair.T if v = data.a then [ a]else empty:seq.encodingpair.T

Function findencode(t:T)seq.T
 let r = lookuprep(t, getinstance:encodingstate.T)
  if isempty.r then empty:seq.T else [ data.r_1]

function analyze(t:encodingstate.T)seq.word
 "numele =" + toword.length.all.t + "encodecounts" + counts(encodetable.t, 1, 0, 0, 0)
 + "decodeconuts"
 + counts(decodetable.t, 1, 0, 0, 0)

function counts(s:seq.seq.encodingpair.T, i:int, one:int, two:int, big:int)seq.word
 if i > length.s then
 ((for(@e ∈ [ length.s, one, two, big], acc ="")acc + toword.@e))
 else
  let t = length.s_i
   if t = 0 then counts(s, i + 1, one, two, big)
   else if t = 1 then counts(s, i + 1, one + 1, two, big)
   else if t = 2 then counts(s, i + 1, one, two + 1, big)
   else counts(s, i + 1, one, two, big + 1)