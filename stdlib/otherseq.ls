Module otherseq.T

use seq.T

use stdlib


Function ≠(a:T, b:T)boolean not(a = b)

Function ≤(a:T, b:T)boolean not(a > b)

Function ≥(a:T, b:T)boolean not(b > a)

Function <(a:T, b:T)boolean b > a

Function =(T, T)boolean unbound

Function >(a:T, b:T)boolean unbound

Function reverse(s:seq.T)seq.T
 @(+,_(s), empty:seq.T, arithseq(length.s, 0 - 1, length.s))

Function removedups(a:seq.T, b:seq.T, c:int)seq.T
 if c = 0 then b
 else if a_c in b then removedups(a, b, c - 1)
 else removedups(a, b + a_c, c - 1)

Function removedups(a:seq.T)seq.T removedups(a, empty:seq.T, length.a)

type cseq is sequence len:int, element:T

Function length(c:cseq.T)int len.c

Function_(s:cseq.T, i:int)T element.s

Function constantseq(len:int, element:T)seq.T toseq.cseq(len, element)

- - - - - - - - - - - - - - - - - - - -

dseq lets a sequence have a default value even beyond the length of the seq.

type dseq is sequence length:int, default:T, data:seq.T

function todseq(s:seq.T)dseq.T builtin.FROMSEQ

/Function to2dseq(s:seq.T)dseq.T export

Function_(d:dseq.T, i:int)T if i > length.data.d then default.d else(data.d)_i

Function replace(a:seq.T, b:int, v:T)seq.T
 let d = todseq.a
  if length.d = 0 then replace2(a, b, v)
  else
   let s = if b > length.a then
   replace2(data.d + constantseq(b - length.a, default.d), b, v)
   else replace2(data.d, b, v)
    toseq.dseq(length.s, default.d, s)

Function dseq(d:T)seq.T toseq.dseq(1, d, [ d])

Function dseq(d:T, s:seq.T)seq.T toseq.dseq(1, d, s)

function replace2(s:seq.T, index:int, value:T)seq.T
 let p = topseq.s
  if length.p = 0 then
  @(+,_.s, @(+,_.s, empty:seq.T, arithseq(index - 1, 1, 1)) + value, arithseq(length.s - index, 1, index + 1))
  else if index > length.a.p then
  a.p + replace2(b.p, index - length.a.p, value)
  else replace2(a.p, index, value) + b.p

______________________________________

type fastsubseq is sequence length:int, data:seq.T, begin:int

Function_(a:fastsubseq.T, i:int)T(data.a)_(i + begin.a)

Function fastsubseq(s:seq.T, from:int, to:int)seq.T
 if to < from then empty:seq.T
 else if to > length.s then fastsubseq(s, from, length.s)
 else if to < 1 then fastsubseq(s, 1, to)
 else toseq.fastsubseq(to - from + 1, s, from - 1)

_____________

type arithmeticseq is sequence length:int, step:T, start:T

Function +(T, T)T unbound

Function *(int, T)T unbound

Function length(s:arithmeticseq.T)int export

Function_(s:arithmeticseq.T, i:int)T start.s + (i - 1) * step.s

Function arithseq(length:int, step:T, start:T)seq.T toseq.arithmeticseq(length, step, start)

Function ?(T, T)ordering unbound

Function ?(a:seq.T, b:seq.T)ordering subcmp(a, b, 1)

function subcmp(a:seq.T, b:seq.T, i:int)ordering
 let lengtha = length.a
 let lengthb = length.b
  if i = lengtha + 1 then lengtha ? lengthb
  else if(i ? lengthb) = GT then GT
  else
   let c = a_i ? b_i
    if c = EQ then subcmp(a, b, i + 1)else c

Function sort(a:seq.T)seq.T
 if length.a < 2 then a
 else
  merge(sort.subseq(a, 1, length.a / 2), sort.subseq(a, length.a / 2 + 1, length.a))

Function merge(a:seq.T, b:seq.T)seq.T
 if length.a = 0 then b
 else if length.b = 0 then a
 else if(b_1 ? a_(length.a)) = GT then a + b
 else if(a_1 ? b_(length.b)) = GT then b + a else submerge(a, b, 1, 1)

function submerge(a:seq.T, b:seq.T, i:int, j:int)seq.T
 if i > length.a then subseq(b, j, length.b)
 else if j > length.b then subseq(a, i, length.a)
 else if(b_j ? a_i) = LT then
 [ b_j] + submerge(a, b, i, j + 1)
 else [ a_i] + submerge(a, b, i + 1, j)

Function binarysearch(s:seq.T, val:T)int
 // binarysearch returns position in seq if found and the negation of the posistion if not found // binarysearch(s, 1, length.s, val)

Function binarysearch(s:seq.T, b:int, a:int, val:T)int
 if a < b then -(a + 1)
 else
  let p =(a + b) / 2
  let c = s_p ? val
   if c = EQ then p
   else if c = GT then binarysearch(s, b, p - 1, val)else binarysearch(s, p + 1, a, val)

Function setinsert(s:seq.T, val:T)seq.T
 let i = binarysearch(s, val)
  if i > 0 then s
  else subseq(s, 1, - i - 1) + [ val] + subseq(s, - i, length.s)

Function setdelete(s:seq.T, val:T)seq.T
 let i = binarysearch(s, val)
  if i > 0 then
  subseq(s, 1, i - 1) + subseq(s, i + 1, length.s)
  else s

Function setreplaceorinsert(s:seq.T, val:T)seq.T
 let i = binarysearch(s, val)
  if i > 0 then
  subseq(s, 1, i - 1) + [ val] + subseq(s, i + 1, length.s)
  else subseq(s, 1, - i - 1) + [ val] + subseq(s, - i, length.s)

Function lpad(n:int, val:T, l:seq.T)seq.T constantseq(n - length.l, val) + l