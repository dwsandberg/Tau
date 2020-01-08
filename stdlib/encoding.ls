Module encoding.T

use deepcopy.seq.encodingrep.T

use seq.T

use seq.encodingrep.T

use seq.seq.encodingrep.T

use stdlib

type encodingstate is sequence length:int, encodetable:seq.seq.encodingrep.T, decodetable:seq.seq.encodingrep.T, all:seq.encodingrep.T

Function decodetable(encodingstate.T)seq.seq.encodingrep.T export

Function encodetable(encodingstate.T)seq.seq.encodingrep.T export

Function all(encodingstate.T)seq.encodingrep.T export

function elecount(e:encodingstate.T)int length.e

Function length(e:encodingstate.T)int export

Function_(e:encodingstate.T, i:int)T data(all(e)_i)

type encodingrep is record code:int, data:T, hash:int

Function code(encodingrep.T)int export

Function hash(encodingrep.T)int export

Function data(encodingrep.T)T export

Function encodingrep(code:int, data:T, hash:int)encodingrep.T export

Function =(a:encodingrep.T, b:encodingrep.T)boolean hash.a = hash.b ∧ code.a = code.b ∧ data.a = data.b

Function check(h:encodingstate.T)seq.word [ toword.length.encodetable.h, toword.length.decodetable.h]

Function hash(T)int unbound

Function =(T, T)boolean unbound

Function index(T)int unbound

Function addindex(T, int)T unbound

Function encodingstate(v:T)encodingstate.T 
 let x = constantseq(4, empty:seq.encodingrep.T)
  encodingstate(0, x, x, empty:seq.encodingrep.T)

function ele(v:T, a:encodingrep.T)int if v = data.a then code.a else 0

function ele2(eletoadd:encodingrep.T, tablesize:int, a:encodingrep.T)seq.encodingrep.T 
 if data.a = data.eletoadd ∨ not(hash.eletoadd mod tablesize = hash.a mod tablesize)
  then empty:seq.encodingrep.T 
  else [ a]

function addcode(code:int, hashsize:int, x:seq.encodingrep.T, e:encodingrep.T)seq.encodingrep.T 
 if code.e = code ∨ not(code mod hashsize = code.e mod hashsize)then x else x + e

Function lookup(data:T, h:encodingstate.T)int 
 @(max, ele.data, 0, encodetable(h)_(hash.data mod length.encodetable.h + 1))


Function add(h:encodingstate.T, l:seq.encodingrep.T)encodingstate.T 
 if 3 *(elecount.h + length.l)> 2 * length.encodetable.h 
  then let t = encodetable.h 
   let d = decodetable.h 
   add(encodingstate(elecount.h, t + t + t + t, d + d + d + d, all.h), l)
  else @(add, identity, h, l)

function ele6(v:encodingrep.T, e:encodingrep.T)int 
 if data.v = data.e then code.e else 0

Function add(h:encodingstate.T, v:encodingrep.T)encodingstate.T 
 let tablesize = length.encodetable.h 
  let datahash = hash.v 
  let dataindex = datahash mod tablesize + 1 
  if @(max, ele6.v, 0, encodetable(h)_dataindex)> 0 
  then // already present // h 
  else let code = code.v 
  let p = v 
  let codeindex = code mod tablesize + 1 
  let l2 = @(addcode(code, tablesize), identity, [ p], decodetable(h)_codeindex)
  let tnew = replace(encodetable.h, dataindex, @(+, ele2(p, tablesize), [ p], encodetable(h)_dataindex))
  encodingstate(elecount.h + 1, tnew, replace(decodetable.h, codeindex, l2), all.h + p)

Function add(h:encodingstate.T, v:T)encodingstate.T 
 if 3 * elecount.h > 2 * length.encodetable.h 
  then let t = encodetable.h 
   let d = decodetable.h 
   add(encodingstate(elecount.h, t + t + t + t, d + d + d + d, all.h), v)
  else let tablesize = length.encodetable.h 
  let datahash = hash.v 
  let dataindex = datahash mod tablesize + 1 
  if @(max, ele.v, 0, encodetable(h)_dataindex)> 0 
  then // already present // h 
  else let code = randomint(1)_1 
  if code < 0 
  then add(h, v)
  else let p = encodingrep(code, v, datahash)
  let codeindex = code mod tablesize + 1 
  let l2 = @(addcode(code, tablesize), identity, [ p], decodetable(h)_codeindex)
  let tnew = replace(encodetable.h, dataindex, @(+, ele2(p, tablesize), [ p], encodetable(h)_dataindex))
  encodingstate(elecount.h + 1, tnew, replace(decodetable.h, codeindex, l2), all.h + p)

Function decode(h:encodingstate.T, code:int)seq.T 
 @(+, ele4.code, empty:seq.T, decodetable(h)_(code mod length.decodetable.h + 1))

function ele4(v:int, a:encodingrep.T)seq.T 
 if v = code.a then [ data.a]else empty:seq.T

Function getinstance(erec:erecord.T)encodingstate.T builtin.STATE.usemangle

Function mapping(erec:erecord.T)seq.T toseq.getinstance.erec

Function orderadded(erec:erecord.T)seq.T toseq.getinstance.erec

Function decode(t:encoding.T, erec:erecord.T)T 
 let inst = getinstance.erec 
  let a = decode(inst, valueofencoding.t)
  assert length.a = 1 report"no such encoding"+ toword.valueofencoding.t + if valueofencoding.t in @(+, code, empty:seq.int, all.inst)
   then"F"
   else"NONE"
  a_1

Function valueofencoding(encoding.T)int builtin.NOOP

Function =(a:encoding.T, b:encoding.T)boolean valueofencoding.a = valueofencoding.b

Function ?(a:encoding.T, b:encoding.T)ordering valueofencoding.a ? valueofencoding.b

Function hash(a:encoding.T)int valueofencoding.a

Function encode(t:T, erec:erecord.T)encoding.T builtin.STATE.usemangle

Function add(  erec:erecord.T,s:seq.encodingrep.T ) int builtin.STATE.usemangle


type erecord is record deepcopy:int, lookupfunc:int, addfunc:int, number:int, name:word, ispersistant:boolean, encodingtype:seq.word

Function ispersistant(erecord.T)boolean export

Function encodingtype(erecord.T)seq.word export

Function name(erecord.T)word export

function ele5(v:T, a:encodingrep.T)seq.T 
 if v = data.a then [ data.a]else empty:seq.T

Function findencode(t:T, erec:erecord.T)seq.T 
 let inst = getinstance.erec 
  @(+, ele5.t, empty:seq.T, encodetable(inst)_(hash.t mod length.encodetable.inst + 1))

Function findindex(t:T, erec:erecord.T)int 
 // works if type T has a integer field named index and a function setindex is defined to set the index value.  
 If t is not in encoding will assign index to one plus current encoding size. If t is in the encoding it will return the index value.
 //
 let inst = getinstance.erec 
  let a = @(+, ele5.t, empty:seq.T, encodetable(inst)_(hash.t mod length.encodetable.inst + 1))
  if length.a = 0 
  then let x = encode(addindex(t, length.inst + 1), erec)
   length.inst + 1 
  else index(a_1)

Function analyze(t:encodingstate.T)seq.word 
 {"numele ="+ toword.length.all.t +"encodecounts"+ counts(encodetable.t, 1, 0, 0, 0)+"decodeconuts"+ counts(decodetable.t, 1, 0, 0, 0)}

function counts(s:seq.seq.encodingrep.T, i:int, one:int, two:int, big:int)seq.word 
 if i > length.s 
  then @(+, toword,"", [ length.s, one, two, big])
  else let t = length(s_i)
  if t = 0 
  then counts(s, i + 1, one, two, big)
  else if t = 1 
  then counts(s, i + 1, one + 1, two, big)
  else if t = 2 then counts(s, i + 1, one, two + 1, big)else counts(s, i + 1, one, two, big + 1)

Function reconstruct(allx:seq.encodingrep.T)encodingstate.T 
 let all = deepcopy.allx 
  let size = 4 * length.all 
  let x = constantseq(size, empty:seq.encodingrep.T)
  let t = encodingstate(length.all, x, x, all)
  @(XX.size, identity, t, all)

function XX(hashsize:int, h:encodingstate.T, a:encodingrep.T)encodingstate.T 
 let codehash = code.a mod hashsize + 1 
  let datahash = hash.a mod hashsize + 1 
  encodingstate(elecount.h, replace(encodetable.h, datahash, encodetable(h)_datahash + a), replace(decodetable.h, codehash, decodetable(h)_codehash + a), all.h)

