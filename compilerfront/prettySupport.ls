Module prettySupport

use PEG

use UTF8

use standard

use seq1.word

Function maxwidth int 100

Function getheader(s:seq.word) seq.word
let gram =
 maketable."Head Export type:any Type' /action // Export /keyword type:$.1 $.2 /br:($$)
 / any any:any Type' FPL any Type' /action // $.1 /keyword $.2:$.3 $.4 $.5 // $.6 $.7 /spc /br:($$)
 / any any FPL any Type' /action // $.1 /keyword $.2 $.3 // $.4 $.5 /spc /br:($$)
 * Type'.any /action /All /br:($$)
 FPL(L)/action($.1)/br:($$)
 / /action /br:($$)
 * L !)any /action /All",
run(gram, s) << 1

Function formatHeader(p1:seq.word) seq.word
let p = getheader.p1,
if width.p < maxwidth then p
else
 let i = findindex(p, "(" sub 1),
 if i > n.p then p
 else
  for acc = subseq(p, 1, i), e ∈ break(p << i, ",)", true) do acc + "/rmbr" + e,
  acc

Function escape2format(in:seq.word) seq.word
if n.in > 2 ∧ last.in = escapeformat ∧ in sub 1 = escapeformat then escape2format.subseq(in, 2, n.in - 1)
else
 for result = "", width = 0, w ∈ in
 do
  next(
   if w ∈ "/br /p" then result + w + escapeFormat."/rmbr" else result + w
   , if w ∈ ("./nsp //" + escapeformat) then width
   else if w ∈ "(,)/sp:(dq)/spc" then width + 1
   else width + n.decodeword.w + 1
  ),
 escapeFormat(if width.in < maxwidth then in else result)

Function width(s:seq.word) int
for acc = 0, inescape = false, w ∈ s
while acc < 10000 - 10
do
 if w = escapeformat then next(acc, not.inescape)
 else if not.inescape ∧ w ∈ "/br /rmbr" then next(10000, inescape)
 else
  next(
   if w ∈ ("/literal /comment /keyword: ./nsp //" + escapeformat) then acc
   else if w ∈ "(,)/sp:(dq)/spc" then acc + 1
   else acc + n.decodeword.w + 1
   , inescape
  ),
acc

Function addcomma(s:seq.word) seq.word
for i = 0, w ∈ reverse.s while w ∈ "/block" do i + 1,
if subseq(s, n.s - i, n.s - i) = "/comment" then s
else s >> i + "," + subseq(s, n.s - i + 1, n.s)

Function blockIsLast(text:seq.word) boolean subseq(text, n.text, n.text) = "/block"

function matchR(txt:seq.word) int
for idx = 1, count = 1, inescape = false, w ∈ reverse(txt >> 1)
while count > 0
do
 if w = escapeformat then next(idx + 1, count, not.inescape)
 else if inescape then next(idx + 1, count, inescape)
 else if w ∈ {open}"(//" then next(idx + 1, count - 1, inescape)
 else if w ∈ {close}")/keyword /literal /comment /block /spc" then next(idx + 1, count + 1, inescape)
 else next(idx + 1, count, inescape)
assert count = 0 report "formatproblem2 empty comment:(count):(idx):(showZ.txt)",
idx

function checkup(a1:seq.word, i:int, a:seq.word) boolean
let start = n.a1 - i,
if start < 2 then false
else if a1 sub start ∉ "/sp /spc" then false
else
 let ch2 = a1 sub (start - 1)
 let ch3 = if ch2 ∈ "/a" ∧ start > 2 then a1 sub (start - 2) else ch2
 let t = ch3 ∈ "+-/ \ =",
 assert t report
  showZ.[ch3]
  + "ten removeclose"
  + showZ.subseq(a1, n.a1 - i - 10, n.a1 - i)
  + "/p"
  + showZ.a,
 t

Function removeclose(a:seq.word) seq.word
{removes the unwanted parenthesis in expressions like[1, 2+(if 3 = 4 then 5 else 6)]}
for endings0 = "", hasparen = false, w ∈ reverse.a
while w ∈ "]/block /spc"
do if w ∈ ")" then next([w] + endings0, true) else next([w] + endings0, hasparen)
let a1 = subseq(a, n.endings0 + 1, n.a - n.endings0),
if last.a1 ∉ ")" then a
else
 {assert n.a ∈[16, 30, 286, 287, 535, 881, 14, 139]∨"iis"sub 1 ∉ a report"DEBUG:(n.a)"+showZ.a}
 let i = matchR.a1
 let start = subseq(a1, n.a1 - i + 1, n.a1 - i + 4),
 if start ∈ ["(// if /keyword", "(// for /keyword"] ∧ checkup(a1, i, a) ∨ i = n.a1 then
  subseq(a, 1, n.endings0)
  + a1 >> i
  + subseq(a1, n.a1 - i + 2, n.a1 - 1)
  + endings0
 else a
 