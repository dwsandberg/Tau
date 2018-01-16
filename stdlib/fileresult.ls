Module fileresult

use UTF8

use fileio

use seq.int

use seq.seq.int

use seq.seq.seq.int

use stdlib

Function breaklines(a:seq.int)seq.seq.int breaklines(a, 2, 1, empty:seq.seq.int)

function breaklines(a:seq.int, i:int, last:int, result:seq.seq.int)seq.seq.int 
 if i > length.a 
  then result 
  else if a_i = 10 
  then breaklines(a, i + 1, i + 1, result + subseq(a, last, i - if a_(i - 1)= 13 then 2 else 1))
  else breaklines(a, i + 1, last, result)

Function breakcommas(a:seq.int)seq.seq.int breakcommas(a, 1, 1, empty:seq.seq.int)

function breakcommas(a:seq.int, i:int, last:int, result:seq.seq.int)seq.seq.int 
 if i > length.a 
  then result + subseq(a, last, i - 1)
  else if a_i = commachar 
  then breakcommas(a, i + 1, i + 1, result + subseq(a, last, i - 1))
  else if a_i = decode("&quot"_1)_1 
  then let d = findindex(decode("&quot"_1)_1, a, i + 2)
   breakcommas(a, d + 2, d + 2, result + subseq(a, i + 1, d - 1))
  else breakcommas(a, i + 1, last, result)

--------

handle files of paragraphs

Function breakparagraph(a:seq.int)seq.seq.int breakparagraph(a, 1, 1, empty:seq.seq.int)

function blankline(a:seq.int, i:int)int 
 // returns 0 if no new line is found before next non white char otherwise returns index of newline // 
  if classify(a_i)= 3 then if a_i = 10 then i else blankline(a, i + 1)else 0

Function breakparagraph(a:seq.int, i:int, last:int, result:seq.seq.int)seq.seq.int 
 if i ≥ length.a 
  then if last < length.a then result + [ fastsubseq(a, last, length.a)]else result 
  else if a_i = 10 
  then let j = blankline(a, i + 1)
   if j > 0 
   then let paragraph = fastsubseq(a, last, i - 1)
    if length.paragraph = 0 
    then breakparagraph(a, j + 1, j + 1, result)
    else breakparagraph(a, j + 1, j + 1, result + paragraph)
   else breakparagraph(a, i + 1, last, result)
  else breakparagraph(a, i + 1, last, result)

Function classify(c:int)int 
 // clasify charactor as standalone(1)whitespace(3)or other(0)// 
  if c > 127 
  then 0 
  else [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
  3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
  0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 
  1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 
  0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
  0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
  0, 0, 0, 0, 0, 0, 0, 0]_(c + 1)

Function towords(a:seq.int)seq.word towords2(a, 1, 1, empty:seq.word)

Function gettext(filename:seq.word)seq.seq.word 
 @(+, towords, empty:seq.seq.word, breakparagraph.getfile.filename)

function spacechar int 32

function periodchar int 46

function openparenchar int 40

function closeparenchar int 41

Function towords2(a:seq.int, i:int, last:int, result:seq.word)seq.word 
 if i > length.a 
  then if last > length.a then result else result + [ encodeword.subseq(a, last, length.a)]
  else let t = a_i 
  if t = spacechar 
  then towords2(a, i + 1, i + 1, if last = i then result else result + encodeword.subseq(a, last, i - 1))
  else if t = commachar 
  then towords2(a, i + 1, i + 1, if last = i then result +","else result + encodeword.subseq(a, last, i - 1)+",")
  else if t = periodchar 
  then if i + 1 ≤ length.a ∧ a_(i + 1)= spacechar 
   then towords2(a, i + 2, i + 2, if last = i 
    then result + encodeword.[ periodchar, spacechar]
    else result + encodeword.subseq(a, last, i - 1)+ encodeword.[ periodchar, spacechar])
   else towords2(a, i + 1, i + 1, if last = i then result +"."else result + encodeword.subseq(a, last, i - 1)+".")
  else if t = openparenchar 
  then towords2(a, i + 1, i + 1, if last = i then result +"("else result + encodeword.subseq(a, last, i - 1)+"(")
  else if t = closeparenchar 
  then towords2(a, i + 1, i + 1, if last = i then result +")"else result + encodeword.subseq(a, last, i - 1)+")")
  else let class = classify.t 
  if class = 0 
  then towords2(a, i + 1, last, result)
  else let newresult = result +(if last = i then""else [ encodeword.subseq(a, last, i - 1)])+ if class = 3 then""else [ encodeword.[ a_i]]
  towords2(a, i + 1, i + 1, newresult)

________

Function createfile(filename:seq.word, s:seq.seq.word)int 
 createbytefile(filename, @(+, toUTF8plus, empty:seq.int, s))

Function toUTF8plus(s:seq.word)seq.int toseqint.toUTF8.s + [ 10, 10]

-------------------

