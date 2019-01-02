Module invertedseq.T

use ipair.T

use seq.ipair.T

use seq.seq.ipair.T

use stdlib

type invertedseq is record hashtable:seq.seq.ipair.T, elecount:int

Function hashtable(invertedseq.T)seq.seq.ipair.T export

Function hash(T)int unbound

Function =(T, T)boolean unbound

Function =(a:ipair.T, b:ipair.T)boolean index.a = index.b ∧ value.a = value.b

Function lookup(value:T, h:invertedseq.T)int 
 @(max, ele.value, 0, hashtable(h)_(hash.value mod length.hashtable.h + 1))

Function ele(v:T, a:ipair.T)int if v = value.a then index.a else 0

Function invertedseq(v:T)invertedseq.T invertedseq(constantseq(4, empty:seq.ipair.T), 0)

Function add(h:invertedseq.T, i:int, v:T)invertedseq.T add(h, ipair(i, v))

Function replicatefourseq2(a:seq.seq.ipair.T)seq.seq.ipair.T a + a +(a + a)

Function add(h:invertedseq.T, p:ipair.T)invertedseq.T 
 if 3 * elecount.h > 2 * length.hashtable.h 
  then add(invertedseq(replicatefourseq2.hashtable.h, elecount.h), p)
  else subadd(h, p, hash.value.p mod length.hashtable.h + 1)

Function ele2(e:T, len:int, a:ipair.T)seq.ipair.T 
 if value.a = e ∨ not(hash.e mod len = hash.value.a mod len)then empty:seq.ipair.T else [ a]

Function subadd(m:invertedseq.T, p:ipair.T, hashofvalue:int)invertedseq.T 
 invertedseq(replace(hashtable.m, hashofvalue, @(+, ele2(value.p, length.hashtable.m), [ p], hashtable(m)_hashofvalue)), elecount.m + 1)

Function toipair(a:invertedseq.T)seq.ipair.T 
 @(+, data.hashtable.a, empty:seq.ipair.T, arithseq(length.hashtable.a, 1, 1))

function data(len:int, i:int, m:ipair.T)seq.ipair.T 
 if hash.value.m mod len = i then [ m]else empty:seq.ipair.T

function data(s:seq.seq.ipair.T, i:int)seq.ipair.T @(+, data(length.s, i - 1), empty:seq.ipair.T, s_i)

Function find(h:invertedseq.T, value:T)seq.ipair.T 
 // return list of ipairs matching value // 
  @(+, find.value, empty:seq.ipair.T, hashtable(h)_(hash.value mod length.hashtable.h + 1))

function find(v:T, a:ipair.T)seq.ipair.T 
 if v = value.a then [ a]else empty:seq.ipair.T

