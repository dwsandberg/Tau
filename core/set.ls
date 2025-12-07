Module set.T

use seq1.T

use standard

use sort.T

Export type:set.T

Export toseq(set.T) seq.T

Export sub(seq.T, int) T

Export +(seq.T, T) seq.T{From seq.T}

Export +(seq.T, seq.T) seq.T{From seq.T}

Export empty:seq.T seq.T{From seq.T}

type set is toseq:seq.T

unbound >1(T, T) ordering

Function asset(s:seq.T) set.T
for acc = empty:seq.T, @e ∈ s do setinsert(acc, @e),
set.acc

Function empty:set.T set.T set.empty:seq.T

Function +(s:set.T, val:T) set.T set.setinsert(toseq.s, val)

Function replace(s:set.T, val:T) set.T set.setreplaceorinsert(toseq.s, val)

Function ∪(val:T, s:set.T) set.T set.setreplaceorinsert(toseq.s, val)

Function sub(s:set.T, i:int) T (toseq.s) sub i

Function lookup(s:set.T, val:T) set.T
let i = binarysearch(toseq.s, val),
if i > 0 then set.[(toseq.s) sub i] else empty:set.T

Function ∩(a:set.T, b:set.T) set.T set.intersect(toseq.a, toseq.b, 1, 1)

function intersect(a:seq.T, b:seq.T, i:int, j:int) seq.T
if i > n.a then empty:seq.T
else if j > n.b then empty:seq.T
else
 let c = a sub i >1 b sub j,
 if c = EQ then [a sub i] + intersect(a, b, i + 1, j + 1)
 else if c = GT then intersect(a, b, i, j + 1)
 else intersect(a, b, i + 1, j)

function union(a:set.T, b:set.T) set.T
if n.b = 0 then a
else if n.b = 1 then a + b sub 1
else set.union(toseq.a, toseq.b, 1, 1, empty:seq.T)

Function ∪(a:set.T, b:set.T) set.T
if n.b = 0 then a
else if n.b = 1 then a + b sub 1
else set.union(toseq.a, toseq.b, 1, 1, empty:seq.T)

function union(a:seq.T, b:seq.T, i:int, j:int, result:seq.T) seq.T
if i > n.a then result + subseq(b, j, n.b)
else if j > n.b then result + subseq(a, i, n.a)
else if a sub i >1 b sub j = GT then union(a, b, i, j + 1, result + b sub j)
else if a sub i >1 b sub j = EQ then union(a, b, i + 1, j + 1, result + a sub i)
else
 let p = binarysearch(a, i + 1, n.a, b sub j),
 if p > 0 then union(a, b, p + 1, j + 1, result + subseq(a, i, p))
 else union(a, b, -p, j + 1, result + subseq(a, i, -p - 1) + [b sub j])

Function \(a:set.T, b:set.T) set.T
{elements in a but not in b}
set.diff(toseq.a, toseq.b, 1, 1)

Function -(a:set.T, b:T) set.T set.setdelete(toseq.a, b)

function diff(a:seq.T, b:seq.T, i:int, j:int) seq.T
if i > n.a then empty:seq.T
else if j > n.b then subseq(a, i, n.a)
else if a sub i >1 b sub j = EQ then diff(a, b, i + 1, j + 1)
else if a sub i >1 b sub j = LT then [a sub i] + diff(a, b, i + 1, j)
else diff(a, b, i, j + 1)

Function replace(a:set.T, b:set.T) set.T
set.replace(toseq.a, toseq.b, 1, 1, empty:seq.T)

function replace(a:seq.T, b:seq.T, i:int, j:int, result:seq.T) seq.T
{if in a and b then b else a}
if i > n.a then result
else if j > n.b then result + subseq(a, i, n.a)
else
 let ai = a sub i
 let c = ai >1 b sub j,
 if c = EQ then replace(a, b, i + 1, j + 1, result + [b sub j])
 else if c = LT then replace(a, b, i + 1, j, result + ai)
 else replace(a, b, i, skipahead(b, j, 1, ai), result)

function skipahead(b:seq.T, j:int, k:int, ai:T) int
if j + k > n.b then j + k / 2 + 1
else if ai >1 b sub (j + k) = GT then skipahead(b, j, k + k, ai)
else j + k / 2 + 1

Function isempty(a:set.T) boolean n.toseq.a = 0

Function ∈(val:T, a:set.T) boolean binarysearch(toseq.a, val) > 0

Function findindex(a:set.T, val:T) int binarysearch(toseq.a, val)

Function cardinality(a:set.T) int n.toseq.a

Function n(a:set.T) int
{set cardinality}
n.toseq.a

Function =(a:set.T, b:set.T) boolean n.a = n.b ∧ toseq.a = toseq.b

Function subseq(a:set.T, from:int, to:int) set.T set.subseq(toseq.a, from, to)

-------------------------------

Secondary ordering that allows a secondary search on a partial key. 

The following must be true(a >2 b)≠ EQ implies >1(a, b)=(a >2 b)

unbound >2(T, T) ordering

Function findelement2(a:set.T, n:T) set.T
let i = binarysearch2(toseq.a, 1, n.toseq.a, n),
asset(
 if i < 0 then empty:seq.T
 else
  for
   acc = empty:seq.T
   , @e ∈ subseq(toseq.a, expandrangedown(toseq.a, n, i), expandrangeup(toseq.a, n, i))
  do acc + @e,
  acc
)

function expandrangedown(a:seq.T, n:T, l:int) int
if l > 1 then if a sub (l - 1) >2 n = EQ then expandrangedown(a, n, l - 1) else l
else l

function expandrangeup(a:seq.T, n:T, u:int) int
if u < n.a then if a sub (u + 1) >2 n = EQ then expandrangeup(a, n, u + 1) else u
else u 