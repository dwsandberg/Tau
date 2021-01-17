Module seq.T

use standard

type seq is sequence length:int, x:T

Export type:seq.T


unbound =(T, T)boolean

builtin IDX(seq.T, int)T

builtin GEP(seq.T, int)T


Function_(a:seq.T, c:int)T
 let b = if c < 0 then length.a + c + 1 else c
 let typ = getseqtype.a
   if typ > 1 then  callidx2(a, b)
    else
     assert b > 0 ∧ b ≤ length.a report"out of bounds" + stacktrace 
    if  typ = 0  then  // element per word //
     IDX(a, b + 1)
  else 
    if sizeoftype:T > 1 then // element represented by multiple words //
          GEP(a , (b-1) * sizeoftype:T + 2 )
     else   if sizeoftype:T= -1 then
            extractbit(a,b-1)  
     else   assert    sizeoftype:T=-8 report "type size not handled in index package seq.T"+toword.sizeoftype:T
           extractbyte(a,b-1)
     
builtin sizeoftype:T int

  builtin extractbit(seq.T,int) T

 builtin extractbyte(seq.T,int) T

builtin callidx2(a:seq.T, int)T

Builtin packed(s:seq.T)seq.T

Builtin getseqtype(a:seq.T)int

Export length(a:seq.T)int

Builtin empty:seq.T seq.T // empty seq //

Function =(a:seq.T, b:seq.T)boolean
 if length.a = length.b then subequal(a, b, length.a)else false

function subequal(a:seq.T, b:seq.T, i:int)boolean
 if i = 0 then true
 else if a_i = b_i then subequal(a, b, i - 1)else false

a @ &and(true, @e = b_@i)


Function ∈(a:T, s:seq.T)boolean 
 findindex(a,s) &le length.s 



Function findelement(w:T, s:seq.T)seq.T
 let idx = findindex(w, s)
  if idx > length.s then empty:seq.T else [ s_idx]

Function findindex(w:T, s:seq.T)int
  // result > length.s when element is not found.Otherwise results is location in sequence // 
  let t= s @ +(0,if w=@e then @i else 0)(w=@e)
  if t=0 then length.s+1 else t
 
 findindex2(w, s, 1)

Function findindex2(w:T, s:seq.T, i:int)int
 if i > length.s then i
 else if s_i = w then i else findindex2(w, s, i + 1)

-------------------------

Export length(c:pseq.T)int

Export a(pseq.T)seq.T

Export b(pseq.T)seq.T

Export start(a:pseq.T) int  

Export to:pseq.T(s:seq.T)pseq.T

Export type:pseq.T 

type pseq is sequence length:int, a:seq.T, b:seq.T,start:int

Function_(s:pseq.T, ii:int)T
 let i=ii+start.s
 let len = length.a.s
  if i > len then
  let x = to:pseq.T(b.s)
    if length.x = 0 then(b.s)_(i - len)else x_(i - len)
  else
   let x = to:pseq.T(a.s)
    if length.x = 0 then(a.s)_i else x_i

Function ispseq(s:seq.T)boolean length.to:pseq.T(s) ≠ 0


Function +(a:seq.T, b:seq.T)seq.T
 let la = length.a
  if length.a = 0 then b
  else
   let lb = length.b
    if lb = 0 then a else catnonzero(a, b)

/Function largeseq(s:seq.T)seq.T let length = length.s if length < 64 then if length > 16 then s else if length > 8 then if length = 16 then [ s_1, s_2, s_3, s_4, s_5, s_6, s_7, s_8, s_9, s_10, s_11, s_12, s_13, s_14, s_15, s_16]else s else if length = 8 then [ s_1, s_2, s_3, s_4, s_5, s_6, s_7, s_8]else if length = 4 then [ s_1, s_2, s_3, s_4]else s else s

Function +(l:seq.T, a:T)seq.T l + [ a]

 function cat3(totallength:int, a:seq.T, b:seq.T, c:seq.T)seq.T
 // if totallength = 3 then [ a_1, b_1, c_1]else //
 if length.a > length.b then toseq.pseq(totallength, a, catnonzero(b, c),0)
 else if length.b < length.c then toseq.pseq(totallength, catnonzero(a, b), c,0)
 else toseq.pseq(totallength, toseq.pseq(length.a + length.b, a, b,0), c,0)

function catnonzero(a:seq.T, b:seq.T)seq.T
 let totallength = length.a + length.b
  if totallength = 2 then [ a_1, b_1]
  else
   let ta = to:pseq.T(a)
    if length.ta = 0 then
      let tb = to:pseq.T(b)
      if length.tb = 0 &or  length.a.tb+ length.b.tb  &ne length.tb then toseq.pseq(totallength, a, b,0)
       else 
         cat3(totallength, a, a.tb, b.tb)
    else 
       if  length.a.ta+ length.b.ta  &ne length.ta then 
       toseq.pseq(totallength, a, b,0)
      else 
      cat3(totallength, a.ta, b.ta, b)


Function subseq(s:seq.T, start:int, end:int)seq.T
 if start > end then empty:seq.T
 else if start < 1 then subseq(s, 1, end)
 else if end > length.s then subseq(s, start, length.s)
 else if start = 1 ∧ length.s = end then s
 else if start = end+1 then [ s_start,s_end ] 
 else if start +1 &ge  end  then 
  if  start=end then [s_start]  else  [ s_start,s_end ] 
 else
    let x = to:pseq.T(s)
   if length.x = 0 then
       toseq.pseq(end - start + 1,s,s,start-1)     
    else subseq(x, start, end)
   

function subseq(p:pseq.T, start:int, end:int)seq.T
  let adjstart=start+start.p-length.a.p
  let adjend=start.p+end - length.a.p
 if  adjstart > 0 then  
    // all in part b //  subseq(b.p, adjstart , adjend)
 else if adjend > 0 then 
     subseq(a.p, start.p+start, length.a.p) + subseq(b.p, 1, adjend)
 else // all in part a // 
   subseq(a.p, start.p+start, start.p+end)


Function last(a:seq.T)T a_(length.a)

Function first(a:seq.T)T a_1

Function isempty(a:seq.T)boolean length.a = 0

--------------------------


Function suffix(s:seq.T, len:int)seq.T subseq(s, length.s - len - 1, length.s)

Function <<(s:seq.T, i:int)seq.T
 assert i ≥ 0 report"FAIL <<" + stacktrace
  subseq(s, if i < 0 then length.s + i + 1 else i + 1, length.s)

Function >>(s:seq.T, i:int)seq.T
 assert i ≥ 0 report"FAIL >>" + stacktrace
  subseq(s, 1, if i < 0 then-i else length.s - i)
  
  



