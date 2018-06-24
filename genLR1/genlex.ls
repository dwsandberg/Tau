#!/usr/local/bin/tau

Module genlex

/run genlex genhash

run genlex findhash

use oseq.seq.word

use oseq.word

use real

use seq.int

use seq.lexaction1

use seq.seq.word

use seq.triple

use set.int

use set.word

use stdlib

use tree.word



type lexaction1 is record w:word, tokenno:int, label:word

function tokenlist seq.word 
 // tokenlist is from parser generator // 
".-is)]= > {:} comment,([_^∧ ∨ T # if * $wordlist then else let assert report @ A E G F W P N L I K" 


function actionlist seq.lexaction1 
 // most frequently used words in programs // 
  let mostfrequentwords ="// &quot,(). :+_seq = a int if-then else Function let word 0 i T ][ 2 use function mytype @ empty inst "
  let wordstoinclude = mostfrequentwords + tokenlist +"= < > ? ≤ ≠ ≥ >> << in +-∈ ∋ * / mod ∪ ∩_^"
  +prepreplacements("","","le ≤ ge ≥ ne ≠ and ∧ or ∨ cup ∪ cap ∩ in ∈ contains ∋", 1)
  @(+, tolexaction, empty:seq.lexaction1, toseq.asset.wordstoinclude)

function tolexaction(next:word)lexaction1 
 // use supplied procedure to convert a word into a lex action // 
  if next in"&quot //"
  then lexaction1(next, 0, next)
  else let token = if next in". ,():"
   then next 
   else if next in" < > ? ≤ ≠ ≥ >> <<"
   then">"_1 
   else if next in"in +-∈ ∋"
   then"-"_1 
   else if next in"* / mod ∪ ∩"
   then"*"_1 
   else if next in"_^"
   then"_"_1 
   else if next in".)]= {:},([ ∧ ∨ # if then else let assert report @ is"
   then next 
   else if hasdigit.next then"I"_1 else"W"_1 
  lexaction1(next, findindex(token, tokenlist), next)

function hashsemiperfect(w:word)int 
 let x = decode.w 
 1+( if length.x > 2 then 23 * (x_1 + 2 * x_2)+ 4 * x_3 
  else if length.x=1 then 23 * x_1
  else 23 * (x_1 + 2 * x_2) ) mod 209
  
 
function tonohash(l:lexaction1)seq.word 
 let a = totext.l 
  {"&br if next = &quot"+ a_4 +"&quot_1 then"+ a +"else"}

Function totext(l:lexaction1)seq.word 
 let w = if w.l ="&quot"_1 then merge("&"+"quot")else w.l 
  let label = if label.l ="&quot"_1 then merge("&"+"quot")else label.l 
  {"lexaction(&quot"+ w +"&quot_1,"+ toword.tokenno.l +", &quot"+ label +"&quot_1)"}

Function genhash seq.word gen.true


Function gen(hash:boolean)seq.word 
 let alist = actionlist 
  let firstpart ="function consumeinput(b:stepresult, next:word)stepresult &br // generated by genlex module in tools //"
  +"&br let Wtoken ="+ toword.findindex("W"_1, tokenlist)+
  "&br let Itoken ="+ toword.findindex("I"_1, tokenlist)+
  "&br let commenttoken ="+ toword.findindex("comment"_1, tokenlist)+
  "&br let stringtoken ="+ toword.findindex("$wordlist"_1, tokenlist)+"&br if tokenstate.b ≠ 0 then 
  &br if tokenstate.b = stringtoken then &br if next = &quot"+ merge.["&"_1,"quot"_1]+"&quot_1 then 
  &br BB(stringtoken, tree(&quot $wordlist &quot_1, @(+, tree, empty:seq.tree.word, string.b)),  stk.b,place.b,input.b)&br else // add to string // 
  &br stepresult(stk.b, place.b + 1, input.b, tokenstate.b, string.b + if next = merge([ &quot & &quot_1, &quot quot &quot_1])then &quot"+ merge.["&"_1,"quot"_1]+"&quot_1 else next)
  &br else if next = &quot // &quot_1 then 
  &br BB(commenttoken, tree(&quot comment &quot_1, @(+, tree, empty:seq.tree.word, string.b)),  stk.b,place.b,input.b)
  &br else // add to string // stepresult(stk.b, place.b + 1, input.b, tokenstate.b, string.b + next)&br else"
  let lastpart ="&br if w.act ≠ next then BB(if hasdigit.next then Itoken else Wtoken, tree(next),  stk.b,place.b,input.b)
  &br else if tokenno.act = 0 then &br if next = &quot"+ merge("&"+"quot")+"&quot_1 then // start word list // stepresult(stk.b, place.b + 1, input.b, stringtoken, &quot &quot)
  &br else // start comment // stepresult(stk.b, place.b + 1, input.b, commenttoken, &quot &quot)
  &br else BB(tokenno.act, tree.label.act,  stk.b,place.b,input.b)"
  firstpart +(if hash 
   then 
    let tab = @(item, identity, constantseq(209, defaultaction), alist)
    {"let act =  let x = decode(next)&br ["+ @(seperator."&br,", identity,"", tab)+"]_( 1+( if length.x > 2 then 23 * (x_1 + 2 * x_2)+ 4 * x_3 
  else if length.x=1 then 23 * x_1
  else 23 * (x_1 + 2 * x_2) ) mod 209
)"} 
   else"let act ="+ @(+, tonohash,"", actionlist)+ defaultaction)+ lastpart

function find(w:word, s:seq.lexaction1, i:int)int 
 if w(s_i)= w then i else find(w, s, i + 1)

function item(tab:seq.seq.word, l:lexaction1)seq.seq.word 
assert tab_hashsemiperfect.w.l = defaultaction report"unexpected collision between"+ w.l +"and"+ tab_hashsemiperfect.w.l 
  replace(tab, hashsemiperfect.w.l, totext.l)

function xx(w:word)seq.word [ toword.hashsemiperfect.w, w]

function defaultaction seq.word {"lexaction(&quot ` &quot_1, 0, &quot ` &quot_1)"}


Function findhash seq.word 
 // look for a semiperfect hash function // 
  // crashes when search larger range of primes // 
  let b = @(+, w,"", actionlist)
   let t = @(+, astriple, empty:seq.triple, actionlist)
  let y = sort.@(+, xx, empty:seq.seq.word, b)
  { "actual hash values &br"+ @(seperator.", &br", identity,"", y)+  "&br size of table, x, y, z, number of collisions"
  + @(+, searchhash(// subseq(findprimes(3, 400), 60, 4000) // arithseq(50,1,2), t, 0,"")  ,"", arithseq(10, 1, 200))}

type triple is record a:int, b:int, c:int

function astriple(l:lexaction1)triple 
 let x = decode.w.l 
  if length.x = 1 then triple(x_1,0,0)
  else if length.x=2 then triple(x_1,x_2,0)
  else triple(x_1,x_2,x_3)

function try(x:int, y:int, m:int, t:triple)int {( x *  (a.t + 2 * b.t) + y  * c.t) mod m }
  
{( x *  (a.t + 2 * b.t) + y  * c.t) mod m }

209 23 46 4

function check(nocollision:int, b:seq.triple, x:int,y:int,m:int,i:int,j:int) seq.word
      if i &ne j &and  try (x,y,m,b_i) = try (x,y,m,b_j)  then 
           if nocollision >  1 then "fail" else 
              let more= 
            if i < j then check(nocollision+1,b,x,y,m,i+1,j) else
            if j = length.b then "success"
            else check(nocollision+1,b,x,y,m,1,j+1)
            if more="fail" then more
            else    let newcol=[reconstruct.b_i , reconstruct.b_j   ]
              if more="success" then
                 newcol
            else  more+newcol
      else  if i < j then check(nocollision,b,x,y,m,i+1,j) else
            if j = length.b then "success"
            else check(nocollision,b,x,y,m,1,j+1) 
            
   

function prepreplacements(old:seq.word, new:seq.word, pairs:seq.word, i:int)seq.word 
 // the pair elements in pair are one after the other. The first element will be merged with a"&".The result is the first elements sorted followed by the second elements rearranged to match the sort. // 
  if i > length.pairs 
  then old + new 
  else let val = merge("&"+ pairs_i)
  let j = binarysearch(old, val)
  prepreplacements(subseq(old, 1,-j - 1)+ [ val]+ subseq(old,-j, length.old), subseq(new, 1,-j - 1)+ [ pairs_(i + 1)]+ subseq(new,-j, length.new), pairs, i + 2)


function reconstruct(t:triple) word if c.t > 0 then  encodeword([a.t,b.t,c.t]) else 
                                    if b.t > 0 then encodeword([a.t,b.t]) else encodeword([a.t]) 

Function searchhash(p:seq.int, b:seq.triple, i:int, result:seq.word, m:int)seq.word 
 let base = length.p 
  let x = p_(i mod base + 1)
  let tmp =  i / base
   if tmp ≥ base 
  then result 
  else let y = p_(tmp + 1)
  // let l = length.b - length.toseq.@(+, try(x, y,  m), empty:set.int, b)
   if l < 4 
    then searchhash(p, b, i + 1, result +"&br"+ @(+, toword,"", [ m, x, y,  l]), m)
  else searchhash(p, b, i + 1, result, m)
//  
  let l =check(0,b,x,y,m,1,2)
  if not(l="fail")  
  then searchhash(p, b, i + 1, result +"&br"+ @(+, toword,"", [ m, x, y])+l, m)
  else searchhash(p, b, i + 1, result, m)

function findprimes(start:int, end:int)seq.int 
 @(+, isprime3, empty:seq.int, arithseq((end - start + 2)/ 2, 2, start))

function isprime3(i:int)seq.int if isprime.i then [ i]else empty:seq.int

function isprime(i:int)boolean 
 if i mod 2 = 0 
  then i = 2 
  else let a = intpart.sqrt.int2real.i 
  let b =(a + i / a)/ 2 
  subisprime(i, 3, b)

function subisprime(i:int, f:int, b:int)boolean 
 if f > b then true else if i mod f = 0 then false else subisprime(i, f + 2, b)

