Module textio

use UTF8

use seq.UTF8

use bits

use otherseq.byte

use standard

Function breaklines(a:UTF8) seq.UTF8 breaklines(toseqbyte.a, 2, 1, empty:seq.UTF8)

Function breaklines(a:seq.byte) seq.UTF8 breaklines(a, 2, 1, empty:seq.UTF8)

function breaklines(a:seq.byte, i:int, last:int, result:seq.UTF8) seq.UTF8
if i > length.a then
 result
else if toint.a_i = 10 then
 breaklines(a
  , i + 1
  , i + 1
  , result + UTF8.subseq(a, last, i - if toint.a_(i - 1) = 13 then 2 else 1))
else
 breaklines(a, i + 1, last, result)

Function breakcommas(a:UTF8) seq.UTF8
for acc = empty:seq.UTF8
 , @e ∈ break(tobyte.toint.char1.",", [tobyte.toint.char1.dq], toseqbyte.a)
do
 acc + UTF8.@e
/for (acc)

Function breakparagraph(a:seq.byte) seq.seq.word
{breaks file into seq of paragraphs}
breakparagraph(UTF8.a, 1, 1, empty:seq.seq.word)

function blankline(a:UTF8, i:int) int
{returns 0 if no new line is found before next non white char otherwise returns index of newline}
if i > length.a then
 i
else
 let t = toint.a_i
 if t = 10 then
  i
 else if t > length.classifychar ∨ t = 0 then
  0
 else if classifychar_t = "SPACE"_1 then blankline(a, i + 1) else 0

Function breakparagraph(u:UTF8, i:int, last:int, result:seq.seq.word) seq.seq.word
if i ≥ length.u then
 if last < length.u then
  result + towords.decodeUTF8.UTF8.subseq(toseqbyte.u, last, length.u)
 else
  result
else if toint.u_i = 10 then
 let j = blankline(u, i + 1)
 if j > 0 then
  if i - 1 < last then
   breakparagraph(u, j + 1, j + 1, result)
  else
   breakparagraph(u
    , j + 1
    , j + 1
    , result + towords.decodeUTF8.UTF8.subseq(toseqbyte.u, last, i - 1))
 else
  breakparagraph(u, i + 1, last, result)
else
 breakparagraph(u, i + 1, last, result)

Function classifychar seq.word
"0 0 0 0 0 0 0 0 0 SPACE 0 0 SPACE 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 SPACE 0 $(dq)
 0 0 0 0 0 () 0+,-.0 0 0 0 0 0 0 0 0 0 0:0 0 = 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
 0 0 0 [0]^_0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 {0} 0 0"

Function towords(a:UTF8) seq.word towords.decodeUTF8.a

Function towords(chars:seq.char) seq.word
let spacechar = char.32
for acc = "", last = 1, i = 1, ch ∈ chars + spacechar do
 if not.between(toint.ch, 1, length.classifychar) then
  next(acc, last, i + 1)
 else
  let class = classifychar_(toint.ch)
  if class = "0"_1 then
   next(acc, last, i + 1)
  else
   let newacc = if last = i then acc else acc + encodeword.subseq(chars, last, i - 1)
   if class ∈ "SPACE" then
    next(newacc, i + 1, i + 1)
   else if (ch = char1."." ∨ ch = char1.":") ∧ i + 1 ≤ length.chars
   ∧ chars_(i + 1) = spacechar then
    next(newacc + encodeword.[ch, spacechar], i + 1, i + 1)
   else
    next(newacc + class, i + 1, i + 1)
/for (acc) 