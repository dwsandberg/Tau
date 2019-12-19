Module oseq.T

use seq.T

use stdlib

Function ?(T, T)ordering unbound

Function =(T, T)boolean unbound

Function ?(a:seq.T, b:seq.T)ordering subcmp(a, b, 1)

function subcmp(a:seq.T, b:seq.T, i:int)ordering 
 let lengtha = length.a 
  let lengthb = length.b 
  if i = lengtha + 1 
  then lengtha ? lengthb 
  else if i ? lengthb = GT 
  then GT 
  else let c = a_i ? b_i 
  if c = EQ then subcmp(a, b, i + 1)else c

Function sort(a:seq.T)seq.T 
 if length.a < 2 then a else merge(sort.subseq(a, 1, length.a / 2), sort.subseq(a, length.a / 2 + 1, length.a))

Function merge(a:seq.T, b:seq.T)seq.T 
 if length.a = 0 
  then b 
  else if length.b = 0 
  then a 
  else if b_1 ? a_length.a = GT 
  then a + b 
  else if a_1 ? b_length.b = GT then b + a else submerge(a, b, 1, 1)

function submerge(a:seq.T, b:seq.T, i:int, j:int)seq.T 
 if i > length.a 
  then subseq(b, j, length.b)
  else if j > length.b 
  then subseq(a, i, length.a)
  else if b_j ? a_i = LT then [ b_j]+ submerge(a, b, i, j + 1)else [ a_i]+ submerge(a, b, i + 1, j)

Function binarysearch(s:seq.T, val:T)int 
 // binarysearch returns position in seq if found and the negation of the posistion if not found // 
  binarysearch(s, 1, length.s, val)

Function binarysearch(s:seq.T, b:int, a:int, val:T)int 
 if a < b 
  then-(a + 1)
  else let p =(a + b)/ 2 
  let c = s_p ? val 
  if c = EQ 
  then p 
  else if c = GT then binarysearch(s, b, p - 1, val)else binarysearch(s, p + 1, a, val)

Function setinsert(s:seq.T, val:T)seq.T 
 let i = binarysearch(s, val)
  if i > 0 then s else subseq(s, 1,-i - 1)+ [ val]+ subseq(s,-i, length.s)

Function setdelete(s:seq.T, val:T)seq.T 
 let i = binarysearch(s, val)
  if i > 0 then subseq(s, 1, i - 1)+ subseq(s, i + 1, length.s)else s

Function setreplaceorinsert(s:seq.T, val:T)seq.T 
 let i = binarysearch(s, val)
  if i > 0 
  then subseq(s, 1, i - 1)+ [ val]+ subseq(s, i + 1, length.s)
  else subseq(s, 1,-i - 1)+ [ val]+ subseq(s,-i, length.s)

