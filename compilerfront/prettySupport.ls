Module prettySupport

use PEG

use UTF8

use standard

use seq1.word

Function maxwidth int 100

Function getheader(s:seq.word) seq.word
let gram =
 maketable."Head Export type:any Type' /action /keyword Export type:$.1 $.2
 /br / any FName:any Type' FPL any Type' /action /keyword $.1 $.2:$.3 $.4 $.5 $.6 $.7
 /br / any FName FPL any Type' /action /keyword $.1 $.2 $.3 $.4 $.5
 /br * Type'.any /action /All
 /br FPL (L) /action /tag ($.1) / /action
 /br * L !) any /action /All
 /br FName !+!-any /action $.1
 /br / any /action /sp $.1",
run(gram, s) << 1

Function formatHeader(p:seq.word) seq.word
if width.p < maxwidth then p
else
 let i = findindex(p, "(" sub 1),
 if i > n.p then p
 else
  for acc = subseq(p, 1, i), e ∈ break(p << i, ",)", true)
  do acc + "/br" + e,
  acc

Function mergecodePrec int 11

Function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Function width(s:seq.word) int
for acc = 0, strcount = 0, skip = false, last = "?" sub 1, w ∈ s
while acc < 10000 - 10
do
 if skip then next(acc, strcount, w ∉ ">", w)
 else if w ∈ "<a" then next(acc, strcount, true, w)
 else if w = escapeformat then next(acc, if strcount > 0 then 0 else 1, skip, w)
 else if w ∈ "/br" ∧ (strcount = 0 ∨ strcount > 10) then next(10000, strcount, skip, w)
 else if strcount > 0 then next(acc + n.decodeword.w + 1, strcount + 1, skip, w)
 else next(acc + wordwidth(last, w), strcount, skip, w),
acc

function wordwidth(last:word, w:word) int
if w ∈ ("<* *> /keyword: ./tag" + escapeformat) ∨ last ∈ "<*" then 0
else if w ∈ "(,) /sp" then 1
else n.decodeword.w + 1

Function addcomma(s:seq.word) seq.word
for i = 0, w ∈ reverse.s while w ∈ "*>" do i + 1,
if subseq(s, n.s - i, n.s - i) = "}" then s
else s >> i + "," + subseq(s, n.s - i + 1, n.s)

Function blockIsLast(text:seq.word) boolean
if isempty.text ∨ last.text ∉ "*>" then false
else
 let i = matchR.text,
 subseq(text, n.text - i + 1, n.text - i + 2) = "<* block"

function matchR(txt:seq.word) int
let close = last.txt
let open = if close ∈ "*>" then "<*" sub 1 else if close ∈ ")" then "(" sub 1 else "?" sub 1,
if open ∈ "?" then 0
else
 for idx = 1, count = 1, inescape = false, w ∈ reverse(txt >> 1)
 while count > 0
 do
  if w = escapeformat then next(idx + 1, count, not.inescape)
  else if inescape then next(idx + 1, count, inescape)
  else if w = open then next(idx + 1, count - 1, inescape)
  else if w = close then next(idx + 1, count + 1, inescape)
  else next(idx + 1, count, inescape)
 assert count = 0 report "formatproblem2 empty comment:(count):(idx):(showZ.txt)",
 idx

function removeblock(a:seq.word) seq.word
if subseq(a, 1, 2) = "<* block" ∧ last.a ∈ "*>" then if matchR.a = n.a then subseq(a, 3, n.a - 1) else a
else a

function addblock(a:seq.word) seq.word
if last.a ∈ "/br" then addblock(a >> 1) else "<* block:(a) *>"

Function removeclose(a:seq.word) seq.word
if last.a ∉ "*>)" then a
else
 for endings0 = "", hasparen = false, w ∈ reverse.a
 while w ∈ "*>)"
 do if w ∈ ")" then next([w] + endings0, true) else next([w] + endings0, hasparen)
 let endings = if hasparen then endings0 else ""
 let paren = 1
 let forif = 2
 let changed = 3
 let skip = 4,
 for left = n.a, len = n.endings, result = "", state = 0, e ∈ endings
 do
  let acc = a >> (len - 1)
  let i = matchR.acc,
  if state = skip then next(n.acc - i, len - 1, result, changed)
  else if e ∈ "*>" then
   if subseq(a, n.acc - i + 1, n.acc - i + 2) ≠ "<* block" then next(n.acc - i, len - 1, a >> len, 0)
   else
    let hasforif = subseq(acc, n.acc - i + 3, n.acc - i + 4) ∈ ["/keyword if", "/keyword for"]
    let newtext =
     if state = 0 then if hasforif then subseq(acc, n.acc - i + 1, n.acc) else ""
     else
      checkbr(
       subseq(acc, n.acc - i + 1, left)
       , ":(if last.result ∈ "/br" then result >> 1 else result) *>"
      ),
    next(n.acc - i, len - 1, newtext, if hasforif then forif else state)
  else
   {e = (}
   let outerparen =
    if n.acc - i ≤ 2 * (len - 1) then
     for state2 = 0, w ∈ subseq(a, 1, n.acc - i)
     while state2 < 2
     do
      if state2 = 1 then if w ∈ "block" then 0 else 2
      else if w ∈ "(" then 0
      else if w ∈ "<*" then 1
      else 2,
     state2 = 0
    else false,
   if outerparen then
    if state = 0 then next(n.acc - i, len - 1, subseq(acc, n.acc - i + 2, n.acc - 1), paren)
    else next(n.acc - i, len - 1, checkbr(subseq(acc, n.acc - i + 2, left), result), paren)
   else
    let b = removeX(acc >> i)
    let tmp = subseq(b, n.b - 1, n.b)
    let before =
     tmp ∈ ["-/sp", "+/sp", "= /sp", ":(escapeformat) *>"]
     ∨ isempty.tmp
     ∨ last.tmp ∈ "else",
    let after = subseq(acc, n.acc - i + 2, n.acc - i + 3) ∈ ["/keyword if", "/keyword for"],
    if before ∧ (after ∨ state = forif) then
     if state ∈ [0, paren] then next(n.acc - i, len - 1, subseq(acc, n.acc - i + 2, n.acc - 1), changed)
     else
      let c = acc >> i
      let d = checkbr(subseq(a, n.acc - i + 2, left), result),
      if subseq(c, n.c - 3, n.c)
      = "}:(escapeformat) *>
      /br"
      ∧ subseq(d, 1, 2) = "<* block"
      ∧ isempty.b
      ∧ subseq(c, 1, 6) = "<* block <* comment:(escapeformat) {" then next(n.acc - i, len - 1, c + d << 2, skip)
      else next(n.acc - i, len - 1, d, changed)
    else next(n.acc - i, len - 1, "", 0),
 if state = 0 then a else checkbr(subseq(a, 1, left), result)

function removeX(a:seq.word) seq.word
if n.a = 0 then a
else if subseq(a, n.a - 1, n.a) = "<* block" then removeX(a >> 2)
else if last.a ∈ "/br" then removeX(a >> 1)
else if subseq(a, n.a - 2, n.a) = "}:(escapeformat) *>" then
 for i = 3, w ∈ reverse(a >> 3) while w ≠ escapeformat do i + 1,
 removeX(a >> (i + 3))
else a

function checkbr(a:seq.word, b:seq.word) seq.word
if not.isempty.a ∧ last.a ∈ "/br" ∧ subseq(b, 1, 2) = "<* block" then a >> 1 + b
else a + b 
