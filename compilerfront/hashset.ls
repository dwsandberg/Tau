Module hashset.T

use seq.hashelement.T

use otherseq.seq.hashelement.T

use seq.T

use bits

use standard

Export type:hashelement.T

Export type:hashset.T

Export cardinality(hashset.T) int

Export type:seq.seq.hashelement.T{From seq.seq.hashelement.T}

type hashelement is data:T, hash:int

type hashset is cardinality:int, table:seq.seq.hashelement.T

Function empty:hashset.T hashset.T
let x = empty:seq.hashelement.T
hashset(0, [x, x, x, x])

unbound =(a:T, b:T) boolean

unbound hash(T) int

Function lookup(s:hashset.T, ele:T) seq.T
let h = hash.ele
for acc = empty:seq.T, e ∈ (table.s)_(h mod length.table.s + 1) do if data.e = ele then acc + data.e else acc /for (acc)

Function toseq(h:hashset.T) seq.T
let tablesize = length.table.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
for acc = empty:seq.T, idx ∈ arithseq(tablesize, 1, 1) do
 for acc2 = acc, e ∈ (table.h)_idx do
  if (bits.hash.e ∧ mask) = bits (idx - 1) then acc2 + data.e else acc2
 /for (acc2)
/for (acc)

function notsamehash2(ele:T, a:int, b:int, mask:bits) boolean (bits.a ∧ mask) ≠ (bits.b ∧ mask)

Function +(h:hashset.T, ele:T) hashset.T
let tablesize = length.table.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
let hash = hash.ele
let dataindex = toint (tobits.hash ∧ mask) + 1
for acc = empty:seq.hashelement.T, found = false, e ∈ (table.h)_dataindex do
 if data.e = ele then next(acc + e, true)
 else if notsamehash2(ele, hash, hash.e, mask) then next(acc, found)
 else next(acc + e, found)
/for (
 let t = 
  replace(table.h, dataindex, if found then acc else [hashelement(ele, hash)] + acc)
 hashset(if found then cardinality.h else cardinality.h + 1
 , if 3 * cardinality.h > 2 * tablesize then t + t + t + t else t
 ))

Function ∪(ele:T, h:hashset.T) hashset.T replace(h, hashelement(ele, hash.ele))

function replace(h:hashset.T, ele:hashelement.T) hashset.T
let tablesize = length.table.h
let mask = bits.-1 >> (65 - floorlog2.tablesize)
let hash = hash.ele
let dataindex = toint (tobits.hash ∧ mask) + 1
for acc = [ele], found = false, e ∈ (table.h)_dataindex do
 if data.e = data.ele then next(acc, true)
 else if notsamehash2(data.ele, hash, hash.e, mask) then next(acc, found)
 else next(acc + e, found)
/for (
 let t = replace(table.h, dataindex, acc)
 hashset(if found then cardinality.h else cardinality.h + 1
 , if 3 * cardinality.h > 2 * tablesize then t + t + t + t else t
 )) 