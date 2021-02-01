Module sparseseq.T

* lets a sequence have a default value even beyond the length of the seq.

use standard

use seq.T

use otherseq.sparseele.T

use seq.sparseele.T

type sparseele is record start:int, edata:seq.T

type sparse is sequence length:int, sdata:seq.sparseele.T, default:T

function ?(a:sparseele.T, b:sparseele.T)ordering start.a ? start.b

function_(s:sparse.T, i:int)T
 let place = binarysearch(sdata.s, sparseele(i, empty:seq.T))
  if place = -1 then default.s
  else
   let k = if place < 0 then-place - 1 else place
   let before =(sdata.s)_k
   let beforeindex = i - start.before + 1
    if beforeindex > length.edata.before then default.s else(edata.before)_beforeindex

Function sparseseq(a:T)seq.T toseq.sparse(1, empty:seq.sparseele.T, a)

Function replaceS(a:seq.T, i:int, b:seq.T)seq.T
 let d = to:sparse.T(a)
  if length.d = 0 then
  subseq(a, 1, i - 1) + b + subseq(a, i + length.b, length.a)
  else
   let ele = sparseele(i, b)
   let place = binarysearch(sdata.d, ele)
   let t = if place > 0 then
   subseq(sdata.d, 1, place - 1) * ele
    + removeoverlap(i + length.b - 1, subseq(sdata.d, place + 1, length.sdata.d), 1)
   else
    subseq(sdata.d, 1,-place - 1) * ele
    + removeoverlap(i + length.b - 1, subseq(sdata.d,-place, length.sdata.d), 1)
   let last = t_(-1)
    toseq.sparse(start.last + length.edata.last - 1, t, default.d)

function removeoverlap(end:int, s:seq.sparseele.T, i:int)seq.sparseele.T
 if i > length.s then empty:seq.sparseele.T
 else if end < start.s_i then s << (i - 1)
 else
  let this = s_i
  let thisend = start.this + length.edata.this - 1
   if end ≥ thisend then removeoverlap(end, s, i + 1)
   else
    [ sparseele(end + 1, edata.this << (end - start.this))] + s << i

function *(a:seq.sparseele.T, e:sparseele.T)seq.sparseele.T
 if isempty.a then [ e]
 else
  let last = a_(-1)
  let lastend = start.last + length.edata.last - 1
   if lastend < start.e then a + e
   else
    a >> 1
    * sparseele(start.last, subseq(edata.last, 1, start.e - start.last) + edata.e)