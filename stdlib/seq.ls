Module seq.T

use deepcopy.T

use seq.T

use deepcopy.boolean

use stacktrace

use stdlib

type seq is sequence length:int, x:T

Function sizeoftype:T int export

Function type:seq.T internaltype export

type pseq is sequence length:int, a:seq.T, b:seq.T

Function =(T, T)boolean unbound

Function_(a:seq.T, b:int)T
// NOINLINE
 . //
 let typ = getseqtype.a
  if typ = 0 then
  assert b > 0 ∧ b ≤ length.a report"out of bounds" + stacktrace
    getval(a, b + 1)
  else callidx(typ, a, b)

function callidx(func:int, a:seq.T, b:int)T builtin.usemangle

function getval(a:seq.T, offset:int)T builtin."LOCAL 1 LOCAL 2 IDXUCZbuiltinZintZint"

Function getseqtype(a:seq.T)int builtin."LOCAL 1 LIT 0 IDXUCZbuiltinZintZint"

Function length(a:seq.T)int export

Function empty:seq.T seq.T // empty seq // builtin."LIT 0 LIT 0 RECORD 2"

Function =(a:seq.T, b:seq.T)boolean
 if length.a = length.b then subequal(a, b, length.a)else false

Function subequal(a:seq.T, b:seq.T, i:int)boolean
 if i = 0 then true
 else if a_i = b_i then subequal(a, b, i - 1)else false

subin is helper function

Function subin(a:T, s:seq.T, i:int)boolean
 if i = 0 then false else if a = s_i then true else subin(a, s, i - 1)

Function in(a:T, s:seq.T)boolean // NOINLINE. // subin(a, s, length.s)

Function identity(a:T)T a

Function >(a:T, b:T)boolean unbound

Function findelement(w:T, s:seq.T)seq.T
 let idx = findindex(w, s, 1)
  if idx > length.s then empty:seq.T else [ s_idx]

Function findindex(w:T, s:seq.T)int
 // result > length.s when element is not found.Otherwise results is location in sequence // findindex(w, s, 1)

Function findindex(w:T, s:seq.T, i:int)int
 if i > length.s then i
 else if s_i = w then i else findindex(w, s, i + 1)

- - - - - - - - - - - - - - - - - - - - - - - - -

Function length(c:pseq.T)int export

Function a(pseq.T)seq.T export

Function b(pseq.T)seq.T export

Function_(s:pseq.T, i:int)T
 let len = length.a.s
  if i > len then
  let x = topseq.b.s
    if length.x = 0 then(b.s)_(i - len)else x_(i - len)
  else
   let x = topseq.a.s
    if length.x = 0 then(a.s)_i else x_i

Function ispseq(s:seq.T)boolean not(length.topseq.s = 0)

Function topseq(s:seq.T)pseq.T  builtin.FROMSEQ

to:pseq.T(s)

 

Function to:pseq.T(s:seq.T)pseq.T export

Function +(a:seq.T, b:seq.T)seq.T
 let la = length.a
  if la = 0 then b
  else
   let lb = length.b
    if lb = 0 then a
    else
     let totallength = la + lb
      if totallength = 2 then [ a_1, b_1]
      else
       let ta = topseq.a
        if length.ta = 0 then
        let tb = topseq.b
          if length.tb = 0 then toseq.pseq(totallength, a, b)else cat3(totallength, a, a.tb, b.tb)
        else cat3(totallength, a.ta, b.ta, b)

Function cat3(totallength:int, a:seq.T, b:seq.T, c:seq.T)seq.T
 if length.a > length.b then toseq.pseq(totallength, a, b + c)
 else if length.b < length.c then toseq.pseq(totallength, a + b, c)
 else toseq.pseq(totallength, toseq.pseq(length.a + length.b, a, b), c)

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
  let x = topseq.s
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

- - - - - - - - - - - - - - - - - - - - - - - - - -