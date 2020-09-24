Module encoding.T

use blockseq.T

use seq.T

use seq.encodingrep.T

use seq.seq.encodingrep.T

use stdlib

use otherseq.encodingrep.T

use otherseq.seq.encodingrep.T

use process.T


Function type:encoding.T internaltype export

Function type:encodingstate.T internaltype export

type encodingstate is sequence length:int, encodetable:seq.seq.encodingrep.T, decodetable:seq.seq.encodingrep.T, all:seq.encodingrep.T

Function decodetable(encodingstate.T)seq.seq.encodingrep.T export

Function encodetable(encodingstate.T)seq.seq.encodingrep.T export

Function all(encodingstate.T)seq.encodingrep.T export

Function length(e:encodingstate.T)int export

Function_(e:encodingstate.T, i:int)T data.(all.e)_i

type encodingrep is record code:encoding.T, data:T, hash:int

Function code(encodingrep.T)encoding.T export

Function hash(encodingrep.T)int export

Function data(encodingrep.T)T export

Function encodingrep(code:encoding.T, data:T, hash:int)encodingrep.T export

Function =(a:encodingrep.T, b:encodingrep.T)boolean
 hash.a = hash.b ∧ valueofencoding.code.a = valueofencoding.code.b
 ∧ data.a = data.b
 
 
 Function ?(a:encodingrep.T, b:encodingrep.T)ordering valueofencoding.code.a ? valueofencoding.code.b


Function check(h:encodingstate.T)seq.word [ toword.length.encodetable.h, toword.length.decodetable.h]

Function hash(T)int unbound

Function =(T, T)boolean unbound

Function empty:encodingstate.T encodingstate.T
let x = constantseq(4, empty:seq.encodingrep.T)
 encodingstate(0, x, x, empty:seq.encodingrep.T)

function adddata(eletoadd:encodingrep.T, tablesize:int, a:encodingrep.T)seq.encodingrep.T
 if data.a = data.eletoadd &or hash.eletoadd mod tablesize ≠ hash.a mod tablesize then
 empty:seq.encodingrep.T
 else [ a]

function addcode(code:encoding.T, hashsize:int, x:seq.encodingrep.T, e:encodingrep.T)seq.encodingrep.T
 if code.e = code ∨ valueofencoding.code mod hashsize ≠ valueofencoding.code.e mod hashsize then
 x
 else x + e

type encoding is record valueofencoding:int

Function valueofencoding(a:encoding.T)int export

Function to:encoding.T (i:int)  encoding.T  encoding.i


Function lastadded( h:encodingstate.T) encoding.T
   code.last.all.h

Function add(h:encodingstate.T, v:encodingrep.T)encodingstate.T
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
     let p=subadd(h,v,1)
          let codeindex = valueofencoding.code.p mod tablesize + 1
      let l1=@(addcode(code.p, tablesize), identity, [ p],(decodetable.h)_codeindex)
     let l2= @(+, adddata(p, tablesize), [ p],(encodetable.h)_dataindex)
     let newdecodetable = replace(decodetable.h, codeindex, l1)
     let newencodetable = replace(encodetable.h, dataindex, l2)
      encodingstate(length.h + 1, newencodetable,newdecodetable , all.h + p)



function used(t:encoding.T, a:encodingrep.T) int
 if t = code.a then 1  else 0
 
 function subadd(h:encodingstate.T, v:encodingrep.T,count:int) encodingrep.T
    // assert count < 10 report "unable to assign encoding" //
    let tablesize = length.encodetable.h
    let code = code.v
    let codeindex = valueofencoding.code mod tablesize + 1
    let found=  valueofencoding.code.v ≤ 0 &or @(+, used.code.v,0,(decodetable.h)_(codeindex) ) > 0
    if found then subadd(h, encodingrep(to:encoding.T(assignencoding(length.h,data.v)), data.v, hash.v),count+1)
     else encodingrep(code.v, deepcopy.data.v, hash.v)

Function assignencoding(length:int,data:T) int // (randomint.1)_1 // unbound

Function assignrandom(length:int,data:T) int  (randomint.1)_1

function rehash(a:encodingrep.T) encodingrep.T encodingrep(code.a,data.a,hash.data.a)

Function add(h:encodingstate.T, l:seq.encodingrep.T)encodingstate.T @(add, rehash, h, l)

Function addseq(h:encodingstate.T, l:seq.encodingrep.T)encodingstate.T @(add, identity, h, l)

Function add(erec:erecord.T, s:encodingrep.T)int builtin.usemangle

Function add(erec:erecord.T, s:seq.encodingrep.T)int @(+, add.erec, 0, s)

Function getinstance(erec:erecord.T)encodingstate.T builtin.usemangle

Function orderadded(erec:erecord.T)seq.T toseq.getinstance.erec


function decode(h:encodingstate.T, t:encoding.T)seq.encodingrep.T
 @(+, ele4.t, empty:seq.encodingrep.T,(decodetable.h)_(valueofencoding.t mod length.decodetable.h + 1))

function ele4(t:encoding.T, a:encodingrep.T)seq.encodingrep.T
 if t = code.a then [ a]else empty:seq.encodingrep.T

Function decode(erec:erecord.T, t:encoding.T)T
 let inst = getinstance.erec
 let a = decode(inst, t)
  assert length.a = 1 report"no such encoding" + toword.valueofencoding.t+stacktrace
   data.a_1

use stacktrace 


Function =(a:encoding.T, b:encoding.T)boolean valueofencoding.a = valueofencoding.b

Function ?(a:encoding.T, b:encoding.T)ordering valueofencoding.a ? valueofencoding.b

Function hash(a:encoding.T)int valueofencoding.a

Function encode(erec:erecord.T, t:T)encoding.T
 let r = lookuprep(t, getinstance.erec)
  if isempty.r then
  let discard = add(erec, encodingrep(to:encoding.T(0), t, hash.t))
    encode(erec, t)
  else code.r_1

function lookuprep(t:T, inst:encodingstate.T)seq.encodingrep.T
 @(+, ele5.t, empty:seq.encodingrep.T,(encodetable.inst)_(hash.t mod length.encodetable.inst + 1))

function ele(v:T, a:encodingrep.T)int if v = data.a then valueofencoding.code.a else 0

type erecord is record addfunc:int, number:int, name:word

Function type:erecord.T internaltype export

Function type:encodingrep.T internaltype export

function ele5(v:T, a:encodingrep.T)seq.encodingrep.T if v = data.a then [ a]else empty:seq.encodingrep.T

Function findencode(erec:erecord.T, t:T)seq.T
 let r = lookuprep(t, getinstance.erec)
  if isempty.r then empty:seq.T else [ data.r_1]

Function analyze(t:encodingstate.T)seq.word
 "numele =" + toword.length.all.t + "encodecounts" + counts(encodetable.t, 1, 0, 0, 0)
 + "decodeconuts"
 + counts(decodetable.t, 1, 0, 0, 0)

function counts(s:seq.seq.encodingrep.T, i:int, one:int, two:int, big:int)seq.word
 if i > length.s then @(+, toword,"", [ length.s, one, two, big])
 else
  let t = length.s_i
   if t = 0 then counts(s, i + 1, one, two, big)
   else if t = 1 then counts(s, i + 1, one + 1, two, big)
   else if t = 2 then counts(s, i + 1, one, two + 1, big)
   else counts(s, i + 1, one, two, big + 1)