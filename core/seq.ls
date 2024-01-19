Module seq.T

use standard

Export type:pseq.T

Export a(pseq.T) seq.T

Export b(pseq.T) seq.T

Export start(a:pseq.T) int

Export type:seq.T

Export to:pseq.T(s:seq.T) pseq.T

Export getseqtype(a:seq.T) int

unbound =(T, T) boolean

type seq is sequence, x:T

Builtin packed(s:seq.T) seq.T

Builtin empty:seq.T seq.T {empty seq}

Builtin idxNB(a:seq.T, i:int) T

Function =(a:seq.T, b:seq.T) boolean
for isequal = n.a = n.b, i = 1, e ∈ a
while isequal
do next(e = i#b, i + 1),
isequal

Function ∈(a:T, s:seq.T) boolean
for found = false, e ∈ s while not.found do a = e,
found

Function lookup(s:seq.T, a:T) seq.T
for found = empty:seq.T, e ∈ s
while isempty.found
do if a = e then found + e else found,
found

type pseq is sequence, a:seq.T, b:seq.T, start:int

function sequenceIndex(s:pseq.T, ii:int) T
let i = ii + start.s
let len = n.a.s,
if i > len then
 let x = to:pseq.T(b.s),
 if n.toseq.x = 0 then idxNB(b.s, i - len) else sequenceIndex(x, i - len)
else
 let x = to:pseq.T(a.s),
 if n.toseq.x = 0 then idxNB(a.s, i) else sequenceIndex(x, i)

Function ispseq(s:seq.T) boolean n.toseq.to:pseq.T(s) ≠ 0

Function +(a:seq.T, b:seq.T) seq.T
{OPTION NOINLINE}
let la = n.a,
if n.a = 0 then b
else
 let lb = n.b,
 if lb = 0 then a else catnonzero(a, b)

Function +(l:seq.T, a:T) seq.T l + [a]

function cat3(totallength:int, a:seq.T, b:seq.T, c:seq.T) seq.T
if n.a > n.b then toseq.pseq(totallength, a, catnonzero(b, c), 0)
else if n.b < n.c then toseq.pseq(totallength, catnonzero(a, b), c, 0)
else toseq.pseq(totallength, toseq.pseq(n.a + n.b, a, b, 0), c, 0)

function catnonzero(a:seq.T, b:seq.T) seq.T
let totallength = n.a + n.b,
if totallength = 2 then [idxNB(a, 1), idxNB(b, 1)]
else
 let ta = to:pseq.T(a),
 if n.toseq.ta = 0 then
  let tb = to:pseq.T(b),
  if n.toseq.tb = 0 ∨ n.a.tb + n.b.tb ≠ n.toseq.tb then toseq.pseq(totallength, a, b, 0)
  else cat3(totallength, a, a.tb, b.tb)
 else if n.a.ta + n.b.ta ≠ n.toseq.ta then toseq.pseq(totallength, a, b, 0)
 else cat3(totallength, a.ta, b.ta, b)

Function subseq(s:seq.T, start:int, finish:int) seq.T
if start > finish then empty:seq.T
else if start < 1 then subseq(s, 1, finish)
else if finish > n.s then subseq(s, start, n.s)
else if start = 1 ∧ n.s = finish then s
else if start = finish + 1 then [start#s, finish#s]
else if start + 1 ≥ finish then if start = finish then [start#s] else [start#s, finish#s]
else
 let p = to:pseq.T(s),
 if n.toseq.p = 0 then toseq.pseq(finish - start + 1, s, s, start - 1)
 else
  let adjstart = start + start.p - n.a.p
  let adjfinish = start.p + finish - n.a.p,
  if adjstart > 0 then {all in part b} subseq(b.p, adjstart, adjfinish)
  else if adjfinish > 0 then subseq(a.p, start.p + start, n.a.p) + subseq(b.p, 1, adjfinish)
  else {all in part a} subseq(a.p, start.p + start, start.p + finish)

Function isempty(a:seq.T) boolean n.a = 0

Function <<(s:seq.T, i:int) seq.T
{* removes i elements from beginning of s}
subseq(s, i + 1, n.s)

Function >>(s:seq.T, i:int) seq.T
{* removes i elements from end of s}
subseq(s, 1, n.s - i)

Builtin n(s:seq.T) int {length of string}

Function #(i:int, s:seq.T) T
{Number elements in sequence from 1 to n.s and return the element numbered i}
assert i > 0 ∧ i ≤ n.s ∨ getseqtype.s > 1 report outofbounds:T,
idxNB(s, i)

builtin outofbounds:T seq.word

Function ^(i:int, s:seq.T) T
{Number elements in sequence from n.s to 1 and return the element numbered i}
(n.s - (i - 1))#s 