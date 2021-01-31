Module seq.T

use standard

type seq is sequence length:int, x:T

Export type:seq.T


unbound =(T, T)boolean

use abstractBuiltin.T
 
builtin indexseq(seq.T, int)T

Function_(a:seq.T, c:int)T
 let b = if c < 0 then length.a + c + 1 else c
 let typ = getseqtype.a
   if typ > 1 then  callidx2(a, b)
    else
     assert b > 0 ∧ b ≤ length.a report"out of bounds" + stacktrace 
    if  typ = 0  then  // element per word //
     IDX(a, b + 1)
  else indexseq(a,b-1) 
  
    if sizeoftype:T > 1 then // element represented by multiple words //
          indexseq(a,b-1) 
     else   if sizeoftype:T= -1 then
            indexseq(a,b-1)  
     else   assert    sizeoftype:T=-8 report "type size not handled in index package seq.T"+toword.sizeoftype:T
           indexseq(a,b-1)
     
builtin sizeoftype:T int

 

Builtin packed(s:seq.T)seq.T

Builtin getseqtype(a:seq.T)int

Export length(a:seq.T)int

Builtin empty:seq.T seq.T // empty seq //

Function =(a:seq.T, b:seq.T)boolean
 if length.a = length.b then  for ( e &in a ,acc=true,i,e &ne b_i) not(e &ne b_i)
  else false
  
Function ∈(a:T, s:seq.T)boolean 
  for( e &in s ,acc=false,i,a=e) a=e
 
Function findelement(w:T, s:seq.T)seq.T
 for( e &in s ,acc=empty:seq.T,i ,w=e)  if w=e then [e] else empty:seq.T 
 
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



Function <<(s:seq.T, i:int)seq.T
 assert i ≥ 0 report"FAIL <<" + stacktrace
  subseq(s, if i < 0 then length.s + i + 1 else i + 1, length.s)

Function >>(s:seq.T, i:int)seq.T
 assert i ≥ 0 report"FAIL >>" + stacktrace
  subseq(s, 1, if i < 0 then-i else length.s - i)
  
  



