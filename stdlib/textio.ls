Module textio

use seq.UTF8

use UTF8

use otherseq.int

use seq.seq.seq.int

use seq.int

use seq.byte

use bits

use standard

use seq.seq.seq.word

Function breaklines(a:UTF8)seq.UTF8 breaklines(toseqbyte.a, 2, 1, empty:seq.UTF8)
 
 function breaklines(a:seq.byte, i:int, last:int, result:seq.UTF8)seq.UTF8
 if i > length.a then result
 else if toint.a_i =  10 then
 breaklines(a, i + 1, i + 1, result + UTF8.subseq(a, last, i - if toint.a_(i - 1) =  13 then 2 else 1))
 else breaklines(a, i + 1, last, result)
 
use otherseq.byte

Function breakcommas(a:UTF8)seq.UTF8 
break(tobyte.toint.char1.",",[tobyte.toint.char1.'"'], toseqbyte.a) @ +(empty:seq.UTF8,UTF8.@e)

--------

handle files of paragraphs


Function breakparagraph(a:UTF8)seq.seq.word  breakparagraph(a, 1, 1, empty:seq.seq.word)

   
function blankline(a:UTF8, i:int)int
 // returns 0 if no new line is found before next non white char otherwise returns index of newline //
 if i > length.a then i
 else
  let t = toint.a_i
   if t = 10 then i
   else if t > length.classifychar ∨ t = 0 then 0
   else if classifychar_t = "SPACE"_1 then blankline(a, i + 1)else 0

 
 Function breakparagraph(u:UTF8, i:int, last:int, result:seq.seq.word)seq.seq.word
 if i ≥ length.u then
 if last < length.u then result + towords.decodeUTF8(u, last, length.u)else result
 else 
   if toint.u_i = 10 then
 let j = blankline(u, i + 1)
   if j > 0 then
      if   i-1 < last then breakparagraph(u,  j + 1, j + 1, result)
     else breakparagraph(u,  j + 1, j + 1, result + towords.decodeUTF8(u, last, i - 1))
   else breakparagraph(u,  i + 1, last, result)
 else breakparagraph(u,  i + 1, last, result)


Function classifychar seq.word ' 0 0 0 0 0 0 0 0 0 SPACE 0 0 SPACE 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 SPACE 0"0 0 0 0 0()0 +,-.0 0 0 0 0 0 0 0 0 0 0:0 0 = 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 [ 0]^_'

Function towords(a:UTF8)seq.word towords.decodeUTF8.a

Function towords(a:seq.char)seq.word towords2(a, 1, 1, empty:seq.word)

function towords2(a:seq.char, i:int, last:int, result:seq.word)seq.word
 let spacechar = char.32
  if i > length.a then
  if last > length.a then result else result + [ encodeword.subseq(a, last, length.a)]
  else
   let t = a_i
    if not.between(toint.t,1, length.classifychar  ) then
    towords2(a, i + 1, last, result)
    else
     let class = classifychar_(toint.t)
      if class = "0"_1 then towords2(a, i + 1, last, result)
      else if class = "SPACE"_1 then
      towords2(a, i + 1, i + 1, if last = i then result else result + encodeword.subseq(a, last, i - 1))
      else
       // if class ="-"_1 ∧ i + 1 ≤ length.a ∧ between(toint.a_(i + 1), 48, 57)then towords2(a, i + 2, i, if last = i then result else result + encodeword.subseq(a, last, i-1))else //
       if t = periodchar ∧ i + 1 ≤ length.a ∧ a_(i + 1) = spacechar then
       towords2(a, i + 2, i + 2, if last = i then result + encodeword.[ periodchar, spacechar]
        else result + encodeword.subseq(a, last, i - 1) + encodeword.[ periodchar, spacechar])
       else
        towords2(a, i + 1, i + 1,(if last = i then result else result + encodeword.subseq(a, last, i - 1)) + class)

