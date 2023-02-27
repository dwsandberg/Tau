Module pretty

use UTF8

use parsersupport.attribute2

use stack.stkele.attribute2

use seq.prettyresult

use standard

use otherseq.word

use set.seq.word

Export type:attribute2

Export type:prettyresult

Function pretty(s:seq.word) seq.word pretty(s, false)

Function escapeformat(s:seq.word) seq.word text.pretty2.[breakup("", s, "")]

Function pretty(s:seq.word, headeronly:boolean) seq.word
if subseq(s, 1, 3) = "Export type:" then
 s
else
 let t = parse:attribute2(attribute."", sortedlextable:attribute2, s, headeronly),
 removeclose.text.t

function errormessage(message:seq.word, input:seq.word, place:int, parsestk:stack.stkele.attribute2) seq.word
%.place + message + "/br" + subseq(input, 1, place)

function breakup(pre:seq.word, in:seq.word, post:seq.word) attribute2
if isempty.in then
 attribute2.[prettyresult(0, 0, pre + post)]
else
 for result = empty:seq.prettyresult
  , acc = pre + escapeformat + first.in
  , linelength = wordwidth(space, first.in)
  , last = space
  , w ∈ in << 1
 do
  if linelength > maxwidth ∨ w ∈ "/br /p" then
   next(result + prettyresult(0, width.acc, acc + escapeformat)
    , [escapeformat] + w
    , wordwidth(last, w)
    , w)
  else
   next(result, acc + w, linelength + wordwidth(last, w), w)
 /do attribute2(result + prettyresult(0, width.acc, acc + escapeformat + post))

Function sortuse(b:seq.seq.word, prefix:seq.word) seq.seq.word
let a = for a = empty:seq.seq.word, u ∈ b do a + reverse.u /do a,
for acc = empty:seq.seq.word, @e ∈ alphasort.toseq.asset.a do
 acc + (prefix + reverse.@e)
/do acc

function pretty(b:seq.attribute2) attribute2
let a = for acc = empty:seq.prettyresult, @e ∈ b do acc + toseq.@e /do acc,
for text = "", width = 0, @e ∈ a do
 next(text + text.@e, width + width.@e)
/do attribute(prec.first.a, width, text)

function pretty2(b:seq.attribute2) attribute2
for a = empty:seq.prettyresult, totalwidth = 0, acc = "", p ∈ b do
 next(a + toseq.p, totalwidth + width.p, acc + text.p)
/do
 if totalwidth < maxwidth then
  attribute(prec.first.a, totalwidth, acc)
 else
  for text = "", width = 0, has/br = false, @e ∈ a do
   if length.text.@e > 1 ∧ (text.@e)_2 ∈ "/p /br" then
    next(text + "/br" + text.@e, width.@e, true)
   else if width + width.@e < maxwidth ∨ isempty.text then
    next(text + text.@e, width + width.@e, has/br)
   else
    next(text + "/br" + text.@e, width.@e, true)
  /do attribute(prec.first.a, if has/br then 10000 else width, text)

function isblock(b:seq.word) boolean subseq(b, 1, 2) = "<* block"

function removeclose(a:seq.word) seq.word
for acc = "", end = "", i = length.a, w ∈ reverse.a
while isempty.acc
do
 if w ∈ "/br *>" then
  next(acc, [w] + end, i - 1)
 else if w ∈ "/if /for" then
  next(acc, end, i - 1)
 else
  next(subseq(a, 1, i) + end, end, i)
/do acc

function lastsymbol(a:seq.word, i:int) word
if a_i ∈ "/br *>" then lastsymbol(a, i - 1) else a_i

type prettyresult is prec:int, width:int, text:seq.word

type attribute2 is toseq:seq.prettyresult

function attribute(text:seq.word) attribute2 attribute2.[prettyresult(0, width.text, text)]

function attribute(prec:int, width:int, text:seq.word) attribute2
attribute2.[prettyresult(prec, width, text)]

function attribute:attribute2(text:seq.word) attribute2 attribute(0, width.text, text)

function forward(stk:attribute2, token:attribute2) attribute2 token

function text(a:attribute2) seq.word
for acc = "", p ∈ toseq.a do acc + text.p /do acc

function width(a:attribute2) int for acc = 0, p ∈ toseq.a do acc + width.p /do acc

function +(a:attribute2, b:attribute2) attribute2 attribute2(toseq.a + toseq.b)

function length(a:attribute2) int length.toseq.a

function maxwidth int 100

function blockIsLast(a:seq.word) boolean
if last.a ∉ "*>" then
 false
else
 for state = "continue"_1
  , depth = 0
  , last = "*>"_1
  , i ∈ arithseq(length.a - 1,-1, length.a - 1)
 while state ∈ "continue"
 do
  let this = a_i,
  if last = escapeformat then
   if this = escapeformat then next(state, depth, "?"_1) else next(state, depth, last)
  else if this ∈ "<*" then
   if depth = 0 then
    next(if last ∈ "block" then "true"_1 else "false"_1, depth, this)
   else
    next(state, depth - 1, this)
  else if this ∈ "*>" then next(state, depth + 1, this) else next(state, depth, this)
 /do if state ∈ "true" then true else false

function list(openlist:seq.word, a:attribute2, closelist:seq.word) attribute2
let totwidth = for acc = 0, @e ∈ toseq.a do acc + width.@e + 2 /do acc
let noperline = 
 if totwidth < maxwidth then
  10000
 else
  for itemmaxwidth = 0, @e ∈ toseq.a do
   max(itemmaxwidth, width.@e)
  /do max(1, maxwidth / (itemmaxwidth * 5 + 10) * 5)
,
for first = 0, acc = "", i = 1, e ∈ toseq.a do
 if i = noperline then
  let newacc = acc + removeclose.text.e,
  next(if first = 0 then length.newacc else first
   , if width.e > maxwidth ∧ blockIsLast.newacc then newacc + "," else newacc + "/br,"
   , 1)
 else
  next(first, acc + removeclose.text.e + ",", i + 1)
/do
 {remove last terminator and trailing \if from acc}
 let t0 = acc >> 1
 let t1 = 
  if last.t0 ∈ "/br" then t0 >> 1 else t0
 let t2 = removeclose.t1,
 if totwidth < maxwidth then
  {fits on one line} attribute(openlist + t2 + closelist)
 else
  {leave first element on current line and place others in a block}
  let firstelement = subseq(t2, 1, first)
  let part1 = 
   if width.firstelement > maxwidth then
    "<* block $(t2)"
   else
    {adding block so do not need
     /br between first and second element}
    let shift = 
     if subseq(t2, first + 1, first + 1) = "/br" then first + 1 else first
    ,
    firstelement + "<* block" + t2 << shift
  let part2 = if "do while"_1 ∈ closelist then "*> $(closelist)" else closelist + "*>",
  attribute(0, 10000, openlist + part1 + part2)

function wrap(prec:int, prein:attribute2, binary:seq.word, postin:attribute2) attribute2
let pre = (toseq.prein)_1
let post = (toseq.postin)_1
let x = 
 if width.pre + width.post > maxwidth ∧ binary ≠ "." then
  if blockIsLast.text.pre then "" else "/br" /if
  + "$(if binary ∈ [".", "_", "^"] then binary else binary + space)"
 else if binary ∈ [".", "_", "^"] then binary else [space] + binary + space
let pre1 = if prec.pre > prec then "($(text.pre))" else text.pre,
if prec.post > prec ∨ prec ≠ 3 ∧ prec = prec.post then
 attribute(prec
  , width.pre + width.x + width.post
  , pre1 + if binary = "." then "/nosp (" else x + "(" /if + text.post + ")")
else
 attribute(prec, width.pre + width.x + width.post, pre1 + x + text.post)

function unaryminus(exp:attribute2) attribute2
let prec = 3
let post = (toseq.exp)_1,
if prec.post > prec then
 attribute(prec, 3 + width.post, "-($(text.post))")
else
 attribute(prec, 1 + width.post, "-$(text.post)")

function width(s:seq.word) int
for acc = 0, last = "?"_1, w ∈ s
while acc < 10000
do
 if w = escapeformat then
  next(acc, last)
 else if length.s > 10 ∧ w ∈ "/br" then
  next(10000, w)
 else
  next(acc + wordwidth(last, w), w)
/do acc

function wordwidth(last:word, w:word) int
if w ∈ ("<* *> /keyword: ./nosp" + escapeformat) ∨ last ∈ "<*" then
 0
else if w ∈ "(,) /ldq /sp" then 1 else length.decodeword.w + 1

function ifthenelse(R:seq.prettyresult) attribute2
let x1 = "/keyword if $(removeclose.text.R_1) /keyword then"
let bigexp = width.R_1 + width.R_2 + width.R_3 + 13 > maxwidth,
if not.bigexp then
 attribute(x1 + removeclose.text.R_2 + "/keyword else" + text.R_3 + "/if")
else
 let iselseif = subseq(text.R_3, 1, 2) = "/keyword if",
 attribute(0
  , 10000
  , x1 + addblock.removeclose.text.R_2 + "/keyword else"
  + if iselseif then text.R_3 else addblock.text.R_3 /if
  + "/if")

function addblock(t:seq.word) seq.word
"<* block
 $(if first.t ∈ "/br" then t << 1 else t)
 *>"

function prettyfunc(a:attribute2, name:attribute2, paraList:attribute2, returnType:attribute2) attribute2
let tmp555 = if first.text.name ∈ "+=_-^" then [space] + text.name else text.name,
list("/keyword $(text.a) $(tmp555) /nosp (", paraList, ") $(text.returnType)")

Below is generated from parser generator.

function add4(a:seq.word, b:seq.word) seq.word
if blockIsLast.a then
 if first.b ∈ "/br" then a + b << 1 else a + b
else if first.b ∈ "/br" then a + b else a + "/br" + b

function action(ruleno:int
 , input:seq.word
 , place:int
 , R:reduction.attribute2
 , stk:stack.stkele.attribute2) attribute2
{Alphabet.= ():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while
 /for W do wl wlend /do T X F2 A E FP NM L D F F1 G HH F3 E2 EI
 /br RulePrecedence | HH D0 comment | comment | let | assert | if | for | W | wl | I | [| $wordlist |
 (| E NM | E comment E | E E_E |_| E W.E | E E * E | E-E | * | E E-E |-| E E > E | E E = E |
 = | > | E E ∧ E | ∧ | E E ∨ E | ∨ | E EI else E2 /if | /if | E EI else E2 | E for F3 /do E2 /for | /for
 | E for F3 /do E2 | D comment | E2 A do E | E2 E |}
if ruleno = {F D1 E2} 1 then
 assert length.toseq.R_1 ∈ [1, 2] report %.length.toseq.R_1 + input
 let comment = 
  if length.toseq.R_1 = 1 then "" else text.pretty2.[breakup("<* comment", text.last.toseq.R_1, "*>")]
 ,
 if width.R_1 + width.R_2 < maxwidth ∧ isempty.comment then
  pretty.[R_1, R_2]
 else if isempty.comment then
  attribute.add4(text.R_1, text.R_2)
 else
  attribute.add4(add4(text.first.toseq.R_1, comment), text.R_2)
else if ruleno = {F D1} 2 then
 assert length.toseq.R_1 ∈ [1, 2] report %.length.toseq.R_1 + input,
 if length.toseq.R_1 = 1 then
  R_1
 else
  let comment = text.pretty2.[breakup("<* comment", text.last.toseq.R_1, "*>")],
  if width.comment < maxwidth ∧ "/br"_1 ∉ comment then
   R_1
  else
   attribute.add4(text.first.toseq.R_1, comment)
else if ruleno = {D0 W NM (FP) T} 3 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {D0 W_(FP) T} 4 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {D0 W-(FP) T} 5 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {D0 W = (FP) T} 6 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {D0 W > (FP) T} 7 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {D0 W * (FP) T} 8 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {D0 W ∧ (FP) T} 9 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {D0 W ∨ (FP) T} 10 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {D0 W NM T} 11 then
 pretty.[attribute."/keyword", R_1, R_2, R_3]
else if ruleno = {D0 W NM is FP} 12 then
 list("/keyword type $(text.R_2) is", R_4, "")
else if ruleno = {D1 D0} 13 then
 R_1
else if ruleno = {D1 D0 comment} 14 then
 R_1 + R_2
else if ruleno = {FP T} 15 then
 R_1
else if ruleno = {FP FP, T} 16 then
 R_1 + R_3
else if ruleno = {FP W:T} 17 then
 pretty.[R_1, R_2, R_3]
else if ruleno = {FP FP, W:T} 18 then
 R_1 + pretty.[R_3, R_4, R_5]
else if ruleno = {FP comment W:T} 19 then
 pretty.[R_1, R_2, R_3, R_4]
else if ruleno = {FP FP, comment W:T} 20 then
 R_1 + pretty.[R_3, R_4, R_5, R_6]
else if ruleno = {NM W} 21 then
 R_1
else if ruleno = {NM W:T} 22 then
 pretty.[R_1, R_2, R_3]
else if ruleno = {T W} 23 then
 R_1
else if ruleno = {T W.T} 24 then
 pretty.[R_1, R_2, R_3]
else if ruleno = {E NM} 25 then
 R_1
else if ruleno = {E NM (L)} 26 then
 if length.R_3 = 1 ∧ length.text.R_1 = 1 then
  wrap(3, R_1, ".", R_3)
 else
  list(text.R_1 + "/nosp (", R_3, ")")
else if ruleno = {E (E)} 27 then
 R_2
else if ruleno = {E EI else E2} 28 then
 ifthenelse(toseq.R_1 + toseq.R_3)
else if ruleno = {E EI else E2 /if} 29 then
 ifthenelse(toseq.R_1 + toseq.R_3)
else if ruleno = {E E_E} 30 then
 wrap(1, R_1, text.R_2, R_3)
else if ruleno = {E-E} 31 then
 unaryminus.R_2
else if ruleno = {E W.E} 32 then
 wrap(3, R_1, text.R_2, R_3)
else if ruleno = {E E * E} 33 then
 wrap(4, R_1, text.R_2, R_3)
else if ruleno = {E E-E} 34 then
 wrap(5, R_1, text.R_2, R_3)
else if ruleno = {E E = E} 35 then
 wrap(6, R_1, text.R_2, R_3)
else if ruleno = {E E > E} 36 then
 wrap(7, R_1, text.R_2, R_3)
else if ruleno = {E E ∧ E} 37 then
 wrap(8, R_1, text.R_2, R_3)
else if ruleno = {E E ∨ E} 38 then
 wrap(9, R_1, text.R_2, R_3)
else if ruleno = {L E} 39 then
 R_1
else if ruleno = {L L, E} 40 then
 R_1 + R_3
else if ruleno = {E [L]} 41 then
 list("[", R_2, "]")
else if ruleno = {E3 let W = E} 42 then
 attribute(0
  , 10000
  , "/br /keyword let $(text.R_2) $([space, "="_1, space])
   $(if {width.R_2+} width.R_4 > maxwidth then "<* block $(text.R_4) *>" else text.R_4)")
else if ruleno = {E3 comment} 43 then
 attribute.text.pretty2.[
  breakup("/br <* comment", text.R_1, "*>")]
else if ruleno = {E3 assert E report E2} 44 then
 attribute(0
  , 10000
  , "/br /keyword assert $(text.R_2)
   $(if width.R_2 + width.R_4 > maxwidth ∧ not.blockIsLast.text.R_2 then
   "/br"
  else
   ""
  )
   /keyword report $(if width.R_4 > maxwidth then addblock.text.R_4 else text.R_4)")
else if ruleno = {E I} 45 then
 R_1
else if ruleno = {E I.I} 46 then
 pretty.[R_1, R_2, R_3]
else if ruleno = {E $wordlist} 47 then
 pretty2.[breakup("<* literal /ldq", text.R_1 << 1, "*>")]
else if ruleno = {E comment E} 48 then
 let text = 
  text.pretty2.[breakup("<* comment", text.R_1, "*>")]
  + if width.R_1 + width.R_2 > maxwidth then
   if subseq(text.R_2, 1, 2) = "<* block" then text.R_2 else "/br $(text.R_2)"
  else
   text.R_2
 ,
 attribute(prec.(toseq.R_2)_1, width.text, text)
else if ruleno = {F1 W = E} 49 then
 pretty.[R_1, attribute.[space, "="_1, space], R_3]
else if ruleno = {F1 F1, W = E} 50 then
 R_1 + pretty.[R_3, attribute.[space, "="_1, space], R_5]
else if ruleno = {F0 F1, W-E} 51 then
 R_1 + pretty.[R_3, attribute."∈", R_5]
else if ruleno = {F3 F0 do E2} 52 then
 list("/keyword for", R_1, "") + R_3
else if ruleno = {F3 F0 while E do E2} 53 then
 list("/keyword for", R_1, "") + R_5 + R_3
else if ruleno = {E for F3 /do E2 /for} 54 then
 prettyfor(R_2, R_4)
else if ruleno = {E for F3 /do E2} 55 then
 prettyfor(R_2, R_4)
else if ruleno = {E X wlend} 56 then
 pretty2.[R_1, breakup("", subseq(text.R_2, 2, length.text.R_2 - 1) + dq, "*>")]
else if ruleno = {G F #} 57 then
 R_1
else if ruleno = {E2 E3 E} 58 then
 pretty.[attribute(removeclose.text.R_1 + ", /br"), R_2]
else if ruleno = {E2 E3, E} 59 then
 pretty.[attribute(removeclose.text.R_1 + ", /br"), R_3]
else if ruleno = {E2 E} 60 then
 R_1
else if ruleno = {E3 E3 E3} 61 then
 let R2 = 
  if blockIsLast.text.R_1 ∧ first.text.R_2 ∈ "/br" then
   attribute(text.R_2 << 1)
  else
   R_2
 ,
 pretty.[attribute.removeclose.text.R_1, R2]
else if ruleno = {E3 E3, E3} 62 then
 let R2 = 
  if blockIsLast.text.R_1 ∧ first.text.R_3 ∈ "/br" then
   attribute(text.R_3 << 1)
  else
   R_3
 ,
 pretty.[attribute.removeclose.text.R_1, R2]
else if ruleno = {EI if E then E2} 63 then
 R_2 + R_4
else if ruleno = {X wlstart E} 64 then
 breakup("<* literal /ldq", subseq(text.R_1, 2, length.text.R_1 - 1), "")
 + attribute("$" + "(*> $(removeclose.text.R_2) <* literal)")
else if ruleno = {X X wl E} 65 then
 R_1 + breakup("", subseq(text.R_2, 2, length.text.R_2 - 1), "")
 + attribute("$" + "(*> $(removeclose.text.R_3) <* literal)")
else
 {ruleno}
 assert false report "invalid rule number" + toword.ruleno,
 R_1

function prettyfor(R1:attribute2, R2:attribute2) attribute2
let finalexp = removeclose.if width.R2 > maxwidth then addblock.text.R2 else text.R2
let bod = attribute2.[(toseq.R1)_2]
let total = width.R1 + width.finalexp
let body = removeclose.if total + 8 > maxwidth then addblock.text.bod else text.bod
let accexp = attribute2.[first.toseq.R1],
if length.toseq.R1 = 2 then
 pretty.[accexp, attribute."/keyword do $(body) /keyword /do $(finalexp) /for"]
else
 let text = 
  if total + 11 < maxwidth then
   "/keyword while $(text.last.toseq.R1) /keyword do $(body)"
  else
   "
    $(if width.accexp < maxwidth then "/br" else "")
    while $(text.last.toseq.R1)
    /br /keyword do $(body)"
 ,
 pretty.[accexp, attribute."$(text) /keyword /do $(finalexp) /for"]

function %(p:prettyresult) seq.word %.width.p + text.p 