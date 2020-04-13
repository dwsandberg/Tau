Module textio

use seq.UTF8

use UTF8

use otherseq.int

use seq.seq.seq.int

use seq.int

use stdlib

use seq.seq.seq.word

Function breaklines(a:UTF8)seq.UTF8 breaklines(toseqint.a, 2, 1, empty:seq.UTF8)

function breaklines(a:seq.int, i:int, last:int, result:seq.UTF8)seq.UTF8
 if i > length.a then result
 else if a_i = 10 then
 breaklines(a, i + 1, i + 1, result + UTF8.subseq(a, last, i - if a_(i - 1) = 13 then 2 else 1))
 else breaklines(a, i + 1, last, result)

Function breakcommas(a:UTF8)seq.UTF8 breakcommas(toseqint.a, 1, 1, empty:seq.UTF8)

function breakcommas(a:seq.int, i:int, last:int, result:seq.UTF8)seq.UTF8
 if i > length.a then result + UTF8.subseq(a, last, i - 1)
 else if a_i = toint.commachar then
 breakcommas(a, i + 1, i + 1, result + UTF8.subseq(a, last, i - 1))
 else if a_i = toint.doublequotechar then
 let d = findindex(toint.doublequotechar, a, i + 2)
   breakcommas(a, d + 2, d + 2, result + UTF8.subseq(a, i + 1, d - 1))
 else breakcommas(a, i + 1, last, result)

- - - - - - - -

handle files of paragraphs

Function breakparagraph(a:UTF8)seq.UTF8 breakparagraph(toseqint.a, 1, 1, empty:seq.UTF8)

function blankline(a:seq.int, i:int)int
 // returns 0 if no new line is found before next non white char otherwise returns index of newline //
 let t = a_i
  if t = 10 then i
  else if t > length.classifychar ∨ t = 0 then 0
  else if classifychar_t = "SPACE"_1 then blankline(a, i + 1)else 0

if classify(a_i)= 3 then if a_i = 10 then i else blankline(a, i + 1)else 0

Function breakparagraph(a:seq.int, i:int, last:int, result:seq.UTF8)seq.UTF8
 if i ≥ length.a then
 if last < length.a then result + UTF8.fastsubseq(a, last, length.a)else result
 else if a_i = 10 then
 let j = blankline(a, i + 1)
   if j > 0 then
   let paragraph = fastsubseq(a, last, i - 1)
     if length.paragraph = 0 then breakparagraph(a, j + 1, j + 1, result)
     else breakparagraph(a, j + 1, j + 1, result + UTF8.paragraph)
   else breakparagraph(a, i + 1, last, result)
 else breakparagraph(a, i + 1, last, result)

Function classifychar seq.word ' 0 0 0 0 0 0 0 0 0 SPACE 0 0 SPACE 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 SPACE 0"0 0 0 0 0()0 +, -.0 0 0 0 0 0 0 0 0 0 0:0 0 = 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 [ 0]^_'

Function towords(a:UTF8)seq.word towords.decodeUTF8.a

Function towords(a:seq.char)seq.word towords2(a, 1, 1, empty:seq.word)

function towords2(a:seq.char, i:int, last:int, result:seq.word)seq.word
 let spacechar = char.32
  if i > length.a then
  if last > length.a then result else result + [ encodeword.subseq(a, last, length.a)]
  else
   let t = a_i
    if toint.t > length.classifychar ∨ t = char.0 then
    towords2(a, i + 1, last, result)
    else
     let class = classifychar_(toint.t)
      if class = "0"_1 then towords2(a, i + 1, last, result)
      else if class = "SPACE"_1 then
      towords2(a, i + 1, i + 1, if last = i then result else result + encodeword.subseq(a, last, i - 1))
      else // if class = "-"_1 ∧ i + 1 ≤ length.a ∧ between(toint.a_(i + 1), 48, 57)then
       towords2(a, i + 2, i, if last = i then result else result + encodeword.subseq(a, last, i - 1))
      else // if t = periodchar ∧ i + 1 ≤ length.a ∧ a_(i + 1) = spacechar then
      towords2(a, i + 2, i + 2, if last = i then result + encodeword.[ periodchar, spacechar]
       else result + encodeword.subseq(a, last, i - 1) + encodeword.[ periodchar, spacechar])
      else
       towords2(a, i + 1, i + 1,(if last = i then result else result + encodeword.subseq(a, last, i - 1)) + class)

________

- - - - - - - - - - - - - - - - - - -