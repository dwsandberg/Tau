Module seq.T


use stacktrace

use stdlib

type seq is sequence length:int, x:T

Export type:seq.T

type pseq is sequence length:int, a:seq.T, b:seq.T

unbound =(T, T)boolean

Function_(a:seq.T, c:int)T
 let b=if c < 0 then  length.a+c+1 else c
 assert not(getseqtype.a = 0) ∨ b > 0 ∧ b ≤ length.a report"out of bounds" + stacktrace
  callidx(a, b)

builtin callidx(a:seq.T, int)T // treated specially by compiler //

Builtin getseqtype(a:seq.T)int

Export length(a:seq.T)int

Builtin empty:seq.T seq.T // empty seq //

Function =(a:seq.T, b:seq.T)boolean
 if length.a = length.b then subequal(a, b, length.a)else false

Function subequal(a:seq.T, b:seq.T, i:int)boolean
 if i = 0 then true
 else if a_i = b_i then subequal(a, b, i - 1)else false

subin is helper function

Function subin(a:T, s:seq.T, i:int)boolean
 if i = 0 then false else if a = s_i then true else subin(a, s, i - 1)

Function in(a:T, s:seq.T)boolean subin(a, s, length.s)

Function identity(a:T)T a

unbound >(a:T, b:T)boolean

Function findelement(w:T, s:seq.T)seq.T
 let idx = findindex(w, s, 1)
  if idx > length.s then empty:seq.T else [ s_idx]

Function findindex(w:T, s:seq.T)int
 // result > length.s when element is not found.Otherwise results is location in sequence // findindex(w, s, 1)

Function findindex(w:T, s:seq.T, i:int)int
 if i > length.s then i
 else if s_i = w then i else findindex(w, s, i + 1)

-------------------------

Export length(c:pseq.T)int

Export a(pseq.T)seq.T

Export b(pseq.T)seq.T

Function_(s:pseq.T, i:int)T
 let len = length.a.s
  if i > len then
  let x = to:pseq.T(b.s)
    if length.x = 0 then(b.s)_(i - len)else x_(i - len)
  else
   let x = to:pseq.T(a.s)
    if length.x = 0 then(a.s)_i else x_i

Function ispseq(s:seq.T)boolean not(length.to:pseq.T(s) = 0)

Export to:pseq.T(s:seq.T)pseq.T

Function +(a:seq.T, b:seq.T)seq.T
 let la = length.a
  if la = 0 then b
  else
   let lb = length.b
    if lb = 0 then a else catnonzero(a, b)

let totallength = la + lb if totallength = 2 then [ a_1, b_1]else let ta = to:pseq.T(a)if length.ta = 0 then let tb = to:pseq.T(b)if length.tb = 0 then toseq.pseq(totallength, a, b)else cat3(totallength, a, a.tb, b.tb)else cat3(totallength, a.ta, b.ta, b)

Function cat3(totallength:int, a:seq.T, b:seq.T, c:seq.T)seq.T
 // if totallength = 3 then [ a_1, b_1, c_1]else //
 if length.a > length.b then toseq.pseq(totallength, a, catnonzero(b, c))
 else if length.b < length.c then toseq.pseq(totallength, catnonzero(a, b), c)
 else toseq.pseq(totallength, toseq.pseq(length.a + length.b, a, b), c)

Function catnonzero(a:seq.T, b:seq.T)seq.T
 let totallength = length.a + length.b
  if totallength = 2 then [ a_1, b_1]
  else
   let ta = to:pseq.T(a)
    if length.ta = 0 then
    let tb = to:pseq.T(b)
      if length.tb = 0 then toseq.pseq(totallength, a, b)else cat3(totallength, a, a.tb, b.tb)
    else cat3(totallength, a.ta, b.ta, b)

Function largeseq(s:seq.T)seq.T
 let length = length.s
  if length < 64 then
  if length > 16 then s
   else if length > 8 then
   if length = 16 then
    [ s_1, s_2, s_3, s_4, s_5, s_6, s_7, s_8, s_9, s_10
     , s_11, s_12, s_13, s_14, s_15, s_16]
    else s
   else if length = 8 then
   [ s_1, s_2, s_3, s_4, s_5, s_6, s_7, s_8]
   else if length = 4 then [ s_1, s_2, s_3, s_4]else s
  else s

Function +(l:seq.T, a:T)seq.T l + [ a]

Function subseq(s:seq.T, start:int, end:int)seq.T
 if start > end then empty:seq.T
 else if start < 1 then subseq(s, 1, end)
 else if end > length.s then subseq(s, start, length.s)
 else if start = 1 ∧ length.s = end then s
 else
  let x = to:pseq.T(s)
   if length.x = 0 then
   @(+,_.s, empty:seq.T, arithseq(end - start + 1, 1, start))
   else subseq(x, start, end)

Function subseq(p:pseq.T, start:int, end:int)seq.T
 if start > length.a.p then
 subseq(b.p, start - length.a.p, end - length.a.p)
 else if end > length.a.p then
 subseq(a.p, start, length.a.p) + subseq(b.p, 1, end - length.a.p)
 else subseq(a.p, start, end)

Function last(a:seq.T)T a_(length.a)

Function isempty(a:seq.T)boolean length.a = 0

--------------------------

Builtin packed(s:seq.T)seq.T

Function << (s:seq.T, i:int) seq.T   
 // if i < 0 then postfix of s of length -i else postfix of length.s-i //
           subseq(s,if i < 0 then length.s+i+1 else i+1,length.s)
          
    Function >> (s:seq.T , i:int) seq.T   
 // if i < 0 then prefix of s of length.s+i else prefix of length.s-i //
            subseq(s,1, if i < 0 then -i  else length.s-i )
