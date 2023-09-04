Module prettyAttribute

use UTF8

use seq.prettyR

use standard

use otherseq.word

type prettyR is prec:int, width:int, text:seq.word, z:int

type attribute is parts:seq.prettyR

Export type:attribute

Function prettyR(prec:int, width:int, text:seq.word) prettyR
assert
 true
 ∨ min(width, 10000) = width.text
 ∨ escapeformat ∈ text
 ∨ not.isempty.text ∧ 1^text ∈ "/br /p /row"
report "DIFF^(width.text)^(width)^(text)^(showZ.text)^(stacktrace)",
prettyR(prec, width, text, 0)

Export prec(prettyR) int

Export width(prettyR) int

Export text(prettyR) seq.word

Export type:prettyR

Export attribute(parts:seq.prettyR) attribute

Export parts(attribute) seq.prettyR

Function toAttribute(a:attribute, s:seq.word) attribute attribute.[prettyR(0, width.s, s)]

Function toAttribute(s:seq.word) attribute attribute.[prettyR(0, width.s, s)]

Function attribute(p:prettyR) attribute attribute.[p]

Function prettyR(s:seq.word) seq.prettyR [prettyR(0, width.s, s)]

Function attr(s:seq.word, b:attribute) seq.prettyR
[prettyR(0, width.s + width.1_parts.b, s + text.1_parts.b)]

Function width1(a:attribute) int width.1_parts.a

Function text1(a:attribute) seq.word text.1_parts.a

Function maxwidth int 100

Function width(s:seq.word) int
for acc = 0, strcount = 0, last = 1_"?", w ∈ s
while acc < 10000 - 10
do
 if w = escapeformat then
 next(acc, if strcount > 0 then 0 else 1, w)
 else if w ∈ "/br" ∧ (strcount = 0 ∨ strcount > 10) then
 {assert false report %.strcount+s} next(10000, strcount, w)
 else if strcount > 0 then
 next(acc + n.decodeword.w + 1, strcount + 1, w)
 else next(acc + wordwidth(last, w), strcount, w),
acc

function wordwidth(last:word, w:word) int
if w ∈ ("<* *> /keyword: ./nosp" + escapeformat) ∨ last ∈ "<*" then
0
else if w ∈ "(,) /ldq /sp" then
1
else n.decodeword.w + 1

function matchR(txt:seq.word) int
let close = 1^txt
let open = if close ∈ "*>" then 1_"<*" else if close ∈ ")" then 1_"(" else 1_"?",
if open ∈ "?" then
0
else
 for idx = 1, count = 1, inescape = false, w ∈ reverse(txt >> 1)
 while count > 0
 do
  if w = escapeformat then
  next(idx + 1, count, not.inescape)
  else if inescape then
  next(idx + 1, count, inescape)
  else if w = open then
  next(idx + 1, count - 1, inescape)
  else if w = close then
  next(idx + 1, count + 1, inescape)
  else next(idx + 1, count, inescape)
 assert count = 0 report "formatproblem2^(count)^(idx)^(showZ.txt)",
 idx

Function blockIsLast(text:seq.word) boolean
if isempty.text ∨ 1^text ∉ "*>" then
false
else let i = matchR.text, subseq(text, n.text - i + 1, n.text - i + 2) = "<* block"

Function removeblock(a:seq.word) seq.word
if subseq(a, 1, 2) = "<* block" ∧ 1^a ∈ "*>" then
if matchR.a = n.a then subseq(a, 3, n.a - 1) else a
else a

Function addblock(a:seq.word) seq.word
if 1^a ∈ "/br" then addblock(a >> 1) else "<* block^(a) *>"

Function removeparen(ain:seq.word) seq.word
let a = removeblock.ain,
if n.a < n.ain then
addblock.removeparen.a
else if subseq(a, 1, 1) = "(" ∧ 1^a ∈ ")" then
if matchR.a = n.a then subseq(a, 2, n.a - 1) else a
else a

Function removeparen(a:attribute) attribute
let txt = text.1_parts.a
let txt2 = removeparen.txt,
if n.txt2 = n.txt then
a
else attribute.prettyR(prec.1_parts.a, width.txt2 - width."()", txt2)

Function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Function removeclose(a:attribute) attribute
let txt = text.1_parts.a
let txt2 = removeclose.txt,
if n.txt2 = n.txt then
a
else attribute.prettyR(prec.1_parts.a, width1.a + n.txt2 - n.txt, txt2)

Function removeclose(a:seq.word) seq.word
if 1^a ∉ "*>)" then
a
else
 let endings =
  for acc = "", hasparen = false, w ∈ reverse.a
  while w ∈ "*>)"
  do if w ∈ ")" then next([w] + acc, true) else next([w] + acc, hasparen),
  if hasparen then acc else ""
 let paren = 1
 let forif = 2
 let changed = 3
 let skip = 4
 for left = n.a, len = n.endings, result = "", state = 0, e ∈ endings
 do
  let acc = a >> (len - 1)
  let i = matchR.acc,
   if state = skip then
   next(n.acc - i, len - 1, result, changed)
   else if e ∈ "*>" then
    if subseq(a, n.acc - i + 1, n.acc - i + 2) ≠ "<* block" then
    next(n.acc - i, len - 1, a >> len, 0)
    else
     let hasforif = subseq(acc, n.acc - i + 3, n.acc - i + 4) ∈ ["/keyword if", "/keyword for"]
     let newtext =
      if state = 0 then
      if hasforif then subseq(acc, n.acc - i + 1, n.acc) else ""
      else checkbr(
       subseq(acc, n.acc - i + 1, left)
       , "^(if 1^result ∈ "/br" then result >> 1 else result) *>"
      ),
     next(n.acc - i, len - 1, newtext, if hasforif then forif else state)
   else
    {e = (}
    let outerparen =
     if n.acc - i ≤ 2 * (len - 1) then
      for state2 = 0, w ∈ subseq(a, 1, n.acc - i)
      while state2 < 2
      do
       if state2 = 1 then
       if w ∈ "block" then 0 else 2
       else if w ∈ "(" then
       0
       else if w ∈ "<*" then
       1
       else 2,
      state2 = 0
     else false,
     if outerparen then
      if state = 0 then
      next(n.acc - i, len - 1, subseq(acc, n.acc - i + 2, n.acc - 1), paren)
      else next(n.acc - i, len - 1, checkbr(subseq(acc, n.acc - i + 2, left), result), paren)
     else
      let b = removeX(acc >> i)
      let tmp = subseq(b, n.b - 1, n.b)
      let before =
       tmp ∈ ["-/sp", "+/sp", "= /sp", "^(escapeformat) *>"]
       ∨ isempty.tmp
       ∨ 1^tmp ∈ "else"
      let after = subseq(acc, n.acc - i + 2, n.acc - i + 3) ∈ ["/keyword if", "/keyword for"],
       if before ∧ (after ∨ state = forif) then
        if state ∈ [0, paren] then
        next(n.acc - i, len - 1, subseq(acc, n.acc - i + 2, n.acc - 1), changed)
        else
         let c = acc >> i
         let d = checkbr(subseq(a, n.acc - i + 2, left), result),
          if
           subseq(c, n.c - 3, n.c) = "}^(escapeformat) *> /br"
           ∧ subseq(d, 1, 2) = "<* block"
           ∧ isempty.b
           ∧ subseq(c, 1, 6) = "<* block <* comment^(escapeformat) {"
          then
          next(n.acc - i, len - 1, c + d << 2, skip)
          else next(n.acc - i, len - 1, d, changed)
       else next(n.acc - i, len - 1, "", 0),
 if state = 0 then a else checkbr(subseq(a, 1, left), result)

function removeX(a:seq.word) seq.word
if n.a = 0 then
a
else if subseq(a, n.a - 1, n.a) = "<* block" then
removeX(a >> 2)
else if 1^a ∈ "/br" then
removeX(a >> 1)
else if subseq(a, n.a - 2, n.a) = "}^(escapeformat) *>" then
for i = 3, w ∈ reverse(a >> 3) while w ≠ escapeformat do i + 1, removeX(a >> (i + 3))
else a

function checkbr(a:seq.word, b:seq.word) seq.word
if not.isempty.a ∧ 1^a ∈ "/br" ∧ subseq(b, 1, 2) = "<* block" then
a >> 1 + b
else a + b

Function escapeformat(in:seq.word) seq.word
if isempty.in then
in
else
 for
  result = [escapeformat, 1_in]
  , linelength = wordwidth(space, 1_in)
  , last = space
  , w ∈ in << 1
 do
  if linelength > maxwidth ∨ w ∈ "/br /p /row" then
  next(result + escapeformat + "/br" + escapeformat + w, wordwidth(last, w), w)
  else next(result + w, linelength + wordwidth(last, w), w),
 result + escapeformat 