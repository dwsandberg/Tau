Module sparseseq.T

* lets a sequence have a default value even beyond the length of the seq. 

use seq.T

use seq1.sparseele.T

use standard

type sparseele is start:int, edata:seq.T

type sparse is sequence, sdata:seq.sparseele.T, default:T

Function >1(a:sparseele.T, b:sparseele.T) ordering start.a >1 start.b

function sequenceIndex(s:sparse.T, i:int) T
let place = binarysearch(sdata.s, sparseele(i, empty:seq.T)),
if place = -1 then default.s
else
 let k = if place < 0 then -place - 1 else place
 let before = (sdata.s) sub k,
 let beforeindex = i - start.before + 1,
 if beforeindex > n.edata.before then default.s else (edata.before) sub beforeindex

Function sparseseq(a:T) seq.T toseq.sparse(1, empty:seq.sparseele.T, a)

Function replaceS(a:seq.T, i:int, b:seq.T) seq.T
let d = to:sparse.T(a),
if n.toseq.d = 0 then subseq(a, 1, i - 1) + b + subseq(a, i + n.b, n.a)
else
 let ele = sparseele(i, b)
 let place = binarysearch(sdata.d, ele)
 let t =
  if place > 0 then
   subseq(sdata.d, 1, place - 1) * ele
   + removeoverlap(i + n.b - 1, subseq(sdata.d, place + 1, n.sdata.d), 1)
  else
   subseq(sdata.d, 1, -place - 1) * ele
   + removeoverlap(i + n.b - 1, subseq(sdata.d, -place, n.sdata.d), 1),
 let last = t sub n.t,
 toseq.sparse(start.last + n.edata.last - 1, t, default.d)

function removeoverlap(finish:int, s:seq.sparseele.T, i:int) seq.sparseele.T
if i > n.s then empty:seq.sparseele.T
else if finish < start.s sub i then s << (i - 1)
else
 let this = s sub i
 let thisfinish = start.this + n.edata.this - 1,
 if finish ≥ thisfinish then removeoverlap(finish, s, i + 1)
 else [sparseele(finish + 1, edata.this << (finish - start.this))] + s << i

function *(a:seq.sparseele.T, e:sparseele.T) seq.sparseele.T
if isempty.a then [e]
else
 let last = a sub n.a
 let lastend = start.last + n.edata.last - 1,
 if lastend < start.e then a + e
 else a >> 1 * sparseele(start.last, subseq(edata.last, 1, start.e - start.last) + edata.e)
 