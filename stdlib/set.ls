Module set.T

use oseq.T

use seq.T

use stdlib

type set is record toseq:seq.T

Function empty seq.T export

Function +(seq.T, T)seq.T export

Function +(seq.T, seq.T)seq.T export

Function_(pseq.T, int)T export

Function_(seq.T, int)T export

function ?(T, T)ordering unbound

Function asset(s:seq.T)set.T set.@(setinsert, identity, empty:seq.T, s)

Function empty set.T set.empty:seq.T

Function +(s:set.T, val:T)set.T set.setinsert(toseq.s, val)

Function replace(s:set.T, val:T)set.T set.setreplaceorinsert(toseq.s, val)

Function_(s:set.T, i:int)T toseq(s)_i

Function findelement(val:T, s:set.T)set.T 
 let i = binarysearch(toseq.s, val)
  if i > 0 then set.[ toseq(s)_i]else empty:set.T

Function ∩(a:set.T, b:set.T)set.T set.intersect(toseq.a, toseq.b, 1, 1)

function intersect(a:seq.T, b:seq.T, i:int, j:int)seq.T 
 if i > length.a 
  then empty:seq.T 
  else if j > length.b 
  then empty:seq.T 
  else let c = a_i ? b_j 
  if c = EQ 
  then [ a_i]+ intersect(a, b, i + 1, j + 1)
  else if c = GT then intersect(a, b, i, j + 1)else intersect(a, b, i + 1, j)

function union(a:set.T, b:set.T)set.T 
 if cardinality.b = 0 
  then a 
  else if cardinality.b = 1 then a + b_1 else set.union(toseq.a, toseq.b, 1, 1, empty:seq.T)

Function ∪(a:set.T, b:set.T)set.T 
 if cardinality.b = 0 
  then a 
  else if cardinality.b = 1 then a + b_1 else set.union(toseq.a, toseq.b, 1, 1, empty:seq.T)

function union(a:seq.T, b:seq.T, i:int, j:int, result:seq.T)seq.T 
 if i > length.a 
  then result + subseq(b, j, length.b)
  else if j > length.b 
  then result + subseq(a, i, length.a)
  else if a_i ? b_j = GT 
  then union(a, b, i, j + 1, result + b_j)
  else if a_i ? b_j = EQ 
  then union(a, b, i + 1, j + 1, result + b_j)
  else let p = binarysearch(a, i + 1, length.a, b_j)
  if p > 0 
  then union(a, b, p + 1, j + 1, result + subseq(a, i, p))
  else union(a, b,-p, j + 1, result + subseq(a, i,-p - 1)+ [ b_j])

Function-(a:set.T, b:set.T)set.T 
 // elements in a but not in b // set.diff(toseq.a, toseq.b, 1, 1)

Function-(a:set.T, b:T)set.T set.setdelete(toseq.a, b)

function diff(a:seq.T, b:seq.T, i:int, j:int)seq.T 
 if i > length.a 
  then empty:seq.T 
  else if j > length.b 
  then subseq(a, i, length.a)
  else if a_i ? b_j = EQ 
  then diff(a, b, i + 1, j + 1)
  else if a_i ? b_j = LT then [ a_i]+ diff(a, b, i + 1, j)else diff(a, b, i, j + 1)

Function toseq(set.T)seq.T export

Function isempty(a:set.T)boolean length.toseq.a = 0

Function in(val:T, a:set.T)boolean binarysearch(toseq.a, val)> 0

Function ∈(val:T, a:set.T)boolean binarysearch(toseq.a, val)> 0

Function cardinality(a:set.T)int length.toseq.a

Function =(a:set.T, b:set.T)boolean cardinality.a = cardinality.b ∧ toseq.a = toseq.b

_________________

Secondary ordering that allows a secondary search on a partial key.

The following must be true ?2(a, b)≠ EQ implies ?(a, b)= ?2(a, b)

function ?2(T, T)ordering unbound

Function findelement2(a:set.T, n:T)set.T 
 let i = binarysearch2(toseq.a, 1, length.toseq.a, n)
  if i < 0 
  then asset.empty:seq.T 
  else asset.@(+, identity, empty:seq.T, subseq(toseq.a, expandrangedown(toseq.a, n, i), expandrangeup(toseq.a, n, i)))

function expandrangedown(a:seq.T, n:T, l:int)int 
 if l > 1 
  then if ?2(a_(l - 1), n)= EQ then expandrangedown(a, n, l - 1)else l 
  else l

function expandrangeup(a:seq.T, n:T, u:int)int 
 if u < length.a 
  then if ?2(a_(u + 1), n)= EQ then expandrangeup(a, n, u + 1)else u 
  else u

function binarysearch2(s:seq.T, b:int, a:int, val:T)int 
 if a < b 
  then-(a + 1)
  else let p =(a + b)/ 2 
  let c = ?2(s_p, val)
  if c = EQ 
  then p 
  else if c = GT then binarysearch2(s, b, p - 1, val)else binarysearch2(s, p + 1, a, val)

