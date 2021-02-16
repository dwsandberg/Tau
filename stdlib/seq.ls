Module seq.T

use standard

unbound =(T, T)boolean

type seq is sequence, x:T

Export type:seq.T

Builtin packed(s:seq.T)seq.T

Export getseqtype(a:seq.T)int

Export length(a:seq.T)int

Builtin empty:seq.T seq.T \\ empty seq \\

builtin packedindex(seq.T, int)T

builtin unpackedindex(seq.T, int)T

builtin callidx(seq.T, int)T

Function_(a:seq.T, c:int)T
 let b = if c < 0 then length.a + c + 1 else c
 let typ = getseqtype.a
  if typ > 1 then callidx(a, b)
  else
   assert b > 0 ∧ b ≤ length.a report"out of bounds" + stacktrace
    if typ = 0 then \\ element per word \\ unpackedindex(a, b)else packedindex(a, b)

Function =(a:seq.T, b:seq.T)boolean
 if length.a = length.b then
 for e ∈ a, acc = true, i, e ≠ b_i , not(e ≠ b_i)
 else false

Function ∈(a:T, s:seq.T)boolean for e ∈ s, acc = false, i, a = e , a = e

Function findelement(w:T, s:seq.T)seq.T
 for e ∈ s, acc = empty:seq.T, i, w = e , if w = e then [ e]else empty:seq.T

-------------------------

Export a(pseq.T)seq.T

Export b(pseq.T)seq.T

Export start(a:pseq.T)int

Export to:pseq.T(s:seq.T)pseq.T

Export type:pseq.T

type pseq is sequence, a:seq.T, b:seq.T, start:int

Function_(s:pseq.T, ii:int)T
 let i = ii + start.s
 let len = length.a.s
  if i > len then
  let x = to:pseq.T(b.s)
    if length.toseq.x = 0 then(b.s)_(i - len)else x_(i - len)
  else
   let x = to:pseq.T(a.s)
    if length.toseq.x = 0 then(a.s)_i else x_i

Function ispseq(s:seq.T)boolean length.toseq.to:pseq.T(s) ≠ 0

Function +(a:seq.T, b:seq.T)seq.T
 let la = length.a
  if length.a = 0 then b
  else
   let lb = length.b
    if lb = 0 then a else catnonzero(a, b)

/Function largeseq(s:seq.T)seq.T let length = length.s if length < 64 then if length > 16 then s else if length > 8 then if length = 16 then [ s_1, s_2, s_3, s_4, s_5, s_6, s_7, s_8, s_9, s_10, s_11, s_12, s_13, s_14, s_15, s_16]else s else if length = 8 then [ s_1, s_2, s_3, s_4, s_5, s_6, s_7, s_8]else if length = 4 then [ s_1, s_2, s_3, s_4]else s else s

Function +(l:seq.T, a:T)seq.T l + [ a]

function cat3(totallength:int, a:seq.T, b:seq.T, c:seq.T)seq.T
 \\ if totallength = 3 then [ a_1, b_1, c_1]else \\
 if length.a > length.b then toseq.pseq(totallength, a, catnonzero(b, c), 0)
 else if length.b < length.c then toseq.pseq(totallength, catnonzero(a, b), c, 0)
 else toseq.pseq(totallength, toseq.pseq(length.a + length.b, a, b, 0), c, 0)

function catnonzero(a:seq.T, b:seq.T)seq.T
 let totallength = length.a + length.b
  if totallength = 2 then [ a_1, b_1]
  else
   let ta = to:pseq.T(a)
    if length.toseq.ta = 0 then
    let tb = to:pseq.T(b)
      if length.toseq.tb = 0 ∨ length.a.tb + length.b.tb ≠ length.toseq.tb then
      toseq.pseq(totallength, a, b, 0)
      else cat3(totallength, a, a.tb, b.tb)
    else if length.a.ta + length.b.ta ≠ length.toseq.ta then
    toseq.pseq(totallength, a, b, 0)
    else cat3(totallength, a.ta, b.ta, b)

Function subseq(s:seq.T, start:int, finish:int)seq.T
 if start > finish then empty:seq.T
 else if start < 1 then subseq(s, 1, finish)
 else if finish > length.s then subseq(s, start, length.s)
 else if start = 1 ∧ length.s = finish then s
 else if start = finish + 1 then [ s_start, s_finish]
 else if start + 1 ≥ finish then
 if start = finish then [ s_start]else [ s_start, s_finish]
 else
  let x = to:pseq.T(s)
   if length.toseq.x = 0 then
   toseq.pseq(finish - start + 1, s, s, start - 1)
   else subseq(x, start, finish)

function subseq(p:pseq.T, start:int, finish:int)seq.T
 let adjstart = start + start.p - length.a.p
 let adjfinish = start.p + finish - length.a.p
  if adjstart > 0 then \\ all in part b \\ subseq(b.p, adjstart, adjfinish)
  else if adjfinish > 0 then
  subseq(a.p, start.p + start, length.a.p) + subseq(b.p, 1, adjfinish)
  else \\ all in part a \\ subseq(a.p, start.p + start, start.p + finish)

Function last(a:seq.T)T a_(length.a)

Function first(a:seq.T)T a_1

Function isempty(a:seq.T)boolean length.a = 0

--------------------------

Function <<(s:seq.T, i:int)seq.T
 assert i ≥ 0 report"FAIL <<" + stacktrace
  subseq(s, if i < 0 then length.s + i + 1 else i + 1, length.s)

Function >>(s:seq.T, i:int)seq.T
 assert i ≥ 0 report"FAIL >>" + stacktrace
  subseq(s, 1, if i < 0 then-i else length.s - i)