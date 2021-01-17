Module otherseq.T

use seq.seq.T

use seq.T

use standard

Function reverse(s:seq.T)seq.T
 arithseq(length.s, 0 - 1, length.s) @ +(empty:seq.T, s_@e)

Function removedups(a:seq.T, b:seq.T, c:int)seq.T
 if c = 0 then b
 else if a_c ∈ b then removedups(a, b, c - 1)
 else removedups(a, b + a_c, c - 1)

Function removedups(a:seq.T)seq.T removedups(a, empty:seq.T, length.a)

type cseq is sequence len:int, element:T

Function length(c:cseq.T)int len.c

Function_(s:cseq.T, i:int)T element.s

Function constantseq(len:int, element:T)seq.T toseq.cseq(len, element)

--------------------

Function replace(s:seq.T, index:int, value:T)seq.T
 // function replace2(s:seq.T, index:int, value:T)seq.T //
 let p = to:pseq.T(s)
  if length.p = 0 then
  let b = arithseq(index - 1, 1, 1) @ +(empty:seq.T, s_@e)
    arithseq(length.s - index, 1, index + 1) @ +(b + value, s_@e)
  else if index > length.a.p then
  a.p + replace(b.p, index - length.a.p, value)
  else replace(a.p, index, value) + b.p
  
_____________

type arithmeticseq is sequence length:int, step:T, start:T

unbound +(T, T)T

unbound *(int, T)T

unbound =(T,T) boolean

Export length(s:arithmeticseq.T)int

Function_(s:arithmeticseq.T, i:int)T start.s + (i - 1) * step.s

Function arithseq(length:int, step:T, start:T)seq.T toseq.arithmeticseq(length, step, start)

unbound ?(T, T)ordering

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
 if a < b then-(a + 1)
 else
  let p =(a + b) / 2
  let c = s_p ? val
   if c = EQ then p
   else if c = GT then binarysearch(s, b, p - 1, val)else binarysearch(s, p + 1, a, val)

Function setinsert(s:seq.T, val:T)seq.T
 let i = binarysearch(s, val)
  if i > 0 then s
  else subseq(s, 1,-i - 1) + [ val] + subseq(s,-i, length.s)

Function setdelete(s:seq.T, val:T)seq.T
 let i = binarysearch(s, val)
  if i > 0 then
  subseq(s, 1, i - 1) + subseq(s, i + 1, length.s)
  else s

Function setreplaceorinsert(s:seq.T, val:T)seq.T
 let i = binarysearch(s, val)
  if i > 0 then
  subseq(s, 1, i - 1) + [ val] + subseq(s, i + 1, length.s)
  else subseq(s, 1,-i - 1) + [ val] + subseq(s,-i, length.s)

Function lpad(n:int, val:T, l:seq.T)seq.T constantseq(n - length.l, val) + l

Function break(w:T, a:seq.T )seq.seq.T break(w,empty:seq.T,a)

  
Function  break(seperator:T,quotes:seq.T,a:seq.T) seq.seq.T
  let b= a @+(empty:seq.int,if @e &in ([seperator]+quotes)  then [@i] else empty:seq.int)
  if isempty.b then [a] else 
  break(empty:seq.T,seperator,seperator,a,b,1,1,empty:seq.seq.T)
     

function break(str:seq.T, currentquote:T,seperator:T, a:seq.T,b:seq.int, j:int, start:int,result:seq.seq.T) seq.seq.T
   if j > length.b then  result+(str+subseq(a,start,length.a ))
   else
   let i=b_j
      if currentquote &ne seperator  then // in quoted string //
       if a_i= seperator then 
            break(str ,currentquote,seperator,a,b,j+1,start,result)
       else if a_i = currentquote &and i=length.a   then     
           result+(str+subseq(a,start,i-1))
       else      if a_i = currentquote  &and a_(i+1) =currentquote then 
           break(subseq(a,start,i) ,currentquote,seperator,a,b,j+2,i+2,result)
        else  assert  a_i &ne seperator  &and a_(i+1)=seperator report  "format problem"
         break(empty:seq.T,seperator,seperator,a,b,j+2,i+2,result+(str+subseq(a,start,i-1)))
      else  // not in quoted string //
      if a_i = seperator then
         break(empty:seq.T,seperator,seperator,a,b,j+1,i+1,result+(str+subseq(a,start,i-1)))
   else
      assert isempty(str+subseq(a,start,i-1)) report "format problem"
         break(str,a_i,seperator,a,b,j+1,i+1,result)
  




 /function break(str:seq.T, currentquote:T,seperator:T, a:seq.T,b:seq.int, j:int, start:int,result:seq.seq.T) seq.seq.T
   if j > length.b then  result+(str+subseq(a,start,length.a ))
   else
   let i=b_j
      if a_i=seperator &and currentquote=seperator then
          break(empty:seq.T,currentquote,seperator,a,b,j+1,i+1,result+(str+subseq(a,start,i-1)))
    else  if a_i=currentquote &and i < length.a &and a_(i+1)= currentquote then
          break(subseq(a,start,i) ,currentquote,seperator,a,b,j+2,i+2,result)
    else  if  a_i=currentquote &and i=length.a   then     
         result+(str+subseq(a,start,i-1))
    else  if  a_i=currentquote &and    a_(i+1)= seperator then
          break(empty:seq.T,seperator,seperator,a,b,j+2,i+2,result+(str+subseq(a,start,i-1)))
    else 
     if a_i=seperator then
         break(str,seperator,seperator,a,b, j+1,start,result)
    else 
      let yy=if currentquote=seperator then a_(i) else currentquote
      if  i > 1 &and (j = 1 &or  b_(j-1) &ne i-1 &or a_(i-1) &ne seperator)  then   
              let zz =[if isempty.result &or last.last.result &ne seperator then  seperator  else a_i ]
             if  currentquote=seperator then
                   break(str,a_i,seperator,a,b,  j+1 ,i+1,result+(str+subseq(a,start,i-1)+seperator))  
             else if a_i=currentquote then
                    break(str,seperator,seperator,a,b,  j+1 ,i+1,result+(str+subseq(a,start,i-1)+a_i))  
              else 
               break(empty:seq.T,currentquote,seperator,a,b,  j+1 ,start,result )  
         else 
       break(str,yy,seperator,a,b,  j+1 ,i+1,result) 
