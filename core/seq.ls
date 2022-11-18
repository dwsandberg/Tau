Module seq.T

use standard

Export type:pseq.T

Export a(pseq.T) seq.T

Export b(pseq.T) seq.T

Export start(a:pseq.T) int

Export type:seq.T

Export to:pseq.T(s:seq.T) pseq.T

Export getseqtype(a:seq.T) int

Export length(a:seq.T) int

unbound =(T, T) boolean

type seq is sequence, x:T

Builtin packed(s:seq.T) seq.T

Builtin empty:seq.T seq.T {empty seq}

Builtin _(a:seq.T, c:int) T

Builtin idxNB(a:seq.T, i:int) T

Function =(a:seq.T, b:seq.T) boolean
for isequal = length.a = length.b, i = 1, e ∈ a
while isequal
do
 next(e = b_i, i + 1)
/for (isequal)

Function ∈(a:T, s:seq.T) boolean
for found = false, e ∈ s while not.found do a = e /for (found)

Function lookup(s:seq.T, a:T) seq.T
for found = empty:seq.T, e ∈ s
while isempty.found
do
 if a = e then found + e else found
/for (found)

type pseq is sequence, a:seq.T, b:seq.T, start:int

Function _(s:pseq.T, ii:int) T
let i = ii + start.s
let len = length.a.s
if i > len then
 let x = to:pseq.T(b.s)
 if length.toseq.x = 0 then idxNB(b.s, i - len) else x_(i - len)
else
 let x = to:pseq.T(a.s)
 if length.toseq.x = 0 then idxNB(a.s, i) else x_i

Function ispseq(s:seq.T) boolean length.toseq.to:pseq.T(s) ≠ 0

Function +(a:seq.T, b:seq.T) seq.T
let la = length.a
if length.a = 0 then
 b
else
 let lb = length.b
 if lb = 0 then a else catnonzero(a, b)

Function +(l:seq.T, a:T) seq.T l + [a]

function cat3(totallength:int, a:seq.T, b:seq.T, c:seq.T) seq.T
if length.a > length.b then
 toseq.pseq(totallength, a, catnonzero(b, c), 0)
else if length.b < length.c then
 toseq.pseq(totallength, catnonzero(a, b), c, 0)
else
 toseq.pseq(totallength, toseq.pseq(length.a + length.b, a, b, 0), c, 0)

function catnonzero(a:seq.T, b:seq.T) seq.T
let totallength = length.a + length.b
if totallength = 2 then
 [idxNB(a, 1), idxNB(b, 1)]
else
 let ta = to:pseq.T(a)
 if length.toseq.ta = 0 then
  let tb = to:pseq.T(b)
  if length.toseq.tb = 0 ∨ length.a.tb + length.b.tb ≠ length.toseq.tb then
   toseq.pseq(totallength, a, b, 0)
  else
   cat3(totallength, a, a.tb, b.tb)
 else if length.a.ta + length.b.ta ≠ length.toseq.ta then
  toseq.pseq(totallength, a, b, 0)
 else
  cat3(totallength, a.ta, b.ta, b)

Function subseq(s:seq.T, start:int, finish:int) seq.T
if start > finish then
 empty:seq.T
else if start < 1 then
 subseq(s, 1, finish)
else if finish > length.s then
 subseq(s, start, length.s)
else if start = 1 ∧ length.s = finish then
 s
else if start = finish + 1 then
 [s_start, s_finish]
else if start + 1 ≥ finish then
 if start = finish then [s_start] else [s_start, s_finish]
else
 let x = to:pseq.T(s)
 if length.toseq.x = 0 then
  toseq.pseq(finish - start + 1, s, s, start - 1)
 else
  subseq(x, start, finish)

function subseq(p:pseq.T, start:int, finish:int) seq.T
let adjstart = start + start.p - length.a.p
let adjfinish = start.p + finish - length.a.p
if adjstart > 0 then
 {all in part b} subseq(b.p, adjstart, adjfinish)
else if adjfinish > 0 then
 subseq(a.p, start.p + start, length.a.p) + subseq(b.p, 1, adjfinish)
else
 {all in part a} subseq(a.p, start.p + start, start.p + finish)

Function last(a:seq.T) T a_(length.a)

Function first(a:seq.T) T a_1

Function isempty(a:seq.T) boolean length.a = 0

Function <<(s:seq.T, i:int) seq.T
{* removes i elements from beginning of s}
subseq(s, i + 1, length.s)

Function >>(s:seq.T, i:int) seq.T
{* removes i elements from end of s}
subseq(s, 1, length.s - i) 