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

use format

Function pretty(s:seq.word, headeronly:boolean) seq.word
if subseq(s, 1, 3) = "Export type:" then
 s
else
 let t = parse:attribute2(attribute."", sortedlextable:attribute2, s, headeronly)
 removeclose.text.t

function errormessage(message:seq.word, input:seq.word, place:int, parsestk:stack.stkele.attribute2) seq.word
%.place + message

Function breakup(pre:seq.word, in:seq.word, post:seq.word) attribute2
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
 /for (attribute2(result + prettyresult(0, width.acc, acc + escapeformat + post)))

Function sortuse(b:seq.seq.word, prefix:seq.word) seq.seq.word
let a = for a = empty:seq.seq.word, u ∈ b do a + reverse.u /for (a)
for acc = empty:seq.seq.word, @e ∈ alphasort.toseq.asset.a do
 acc + (prefix + reverse.@e)
/for (acc)

function pretty(b:seq.attribute2) attribute2
let a = for acc = empty:seq.prettyresult, @e ∈ b do acc + toseq.@e /for (acc)
for text = "", width = 0, @e ∈ a do
 next(text + text.@e, width + width.@e)
/for (attribute(prec.first.a, width, text))

function pretty2(b:seq.attribute2) attribute2
for a = empty:seq.prettyresult, totalwidth = 0, acc = "", p ∈ b do
 next(a + toseq.p, totalwidth + width.p, acc + text.p)
/for (
 if totalwidth < maxwidth then
  attribute(prec.first.a, totalwidth, acc)
 else
  for text = "", width = 0, has/br = false, @e ∈ a do
   {assert not (" Steps"_1 /in text.@e /and length.a > 4) report for txt =" ????", x /in a do txt
    +"
    /br"+encodeword (decodeword ((text.x)_2) << 1)+" ///"+text.x /for (txt)}
   if length.text.@e > 1 ∧ (text.@e)_2 ∈ "/p /br" then
    next(text + "/br" + text.@e, width.@e, true)
   else if width + width.@e < maxwidth ∨ isempty.text then
    next(text + text.@e, width + width.@e, has/br)
   else
    next(text + "/br" + text.@e, width.@e, true)
  /for (attribute(prec.first.a, if has/br then 10000 else width, text))
)

function addBr(b:seq.word) seq.word if subseq(b, 1, 2) = "<* block" then b else "/br $(b)"

function addBr(bigexp:boolean, a:seq.word, b:seq.word) seq.word
if bigexp ∨ blockIsLast.a ∨ subseq(b, 1, 2) = "<* block" then
 "<* block $(a) *> $(b)"
else
 a + "/br" + b

function protect(A:attribute2, B:attribute2) seq.word
let bigexp = width.A > maxwidth
let a = text.A
let b = text.B
let a1 = lastsymbol(a, length.a)
let b1 = 
 if subseq(b, 1, 3) = "<* block /keyword" then
  b_4
 else if subseq(b, 1, 2) = "<* block" then b_3 else if first.b = "/keyword"_1 then b_2 else b_1
if a1 = "/if"_1 ∧ b1 ∉ "-+(" then
 addBr(bigexp, removeclose.a, b)
else if b1 ∈ "-+" ∧ a1 ∉ "/if" then
 addBr(bigexp, "($(removeclose.a))", "($(removeclose.a))")
else if b1 ∈ "(" ∧ a1 ∉ "/if)] $(dq)" then
 addBr(bigexp, "($(removeclose.a))", b)
else
 addBr(bigexp, a, b)

function removeclose(a:seq.word, i:int) seq.word
if a_i = "*>"_1 then
 removeclose(a, i - 1) + "*>"_1
else if a_i = "/if"_1 then removeclose(a, i - 1) else subseq(a, 1, i)

function removeclose(a:seq.word) seq.word
if isempty.a then a else removeclose(a, length.a)

function lastsymbol(a:seq.word, i:int) word
if a_i = "*>"_1 then lastsymbol(a, i - 1) else a_i

type prettyresult is prec:int, width:int, text:seq.word

type attribute2 is toseq:seq.prettyresult

function attribute(text:seq.word) attribute2 attribute2.[prettyresult(0, width.text, text)]

function attribute(prec:int, width:int, text:seq.word) attribute2
attribute2.[prettyresult(prec, width, text)]

function attribute:attribute2(text:seq.word) attribute2 attribute(0, width.text, text)

function forward(stk:attribute2, token:attribute2) attribute2 token

function text(a:attribute2) seq.word
for acc = "", p ∈ toseq.a do acc + text.p /for (acc)

function width(a:attribute2) int for acc = 0, p ∈ toseq.a do acc + width.p /for (acc)

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
  let this = a_i
  if last = escapeformat then
   if this = escapeformat then next(state, depth, "?"_1) else next(state, depth, last)
  else if this ∈ "<*" then
   if depth = 0 then
    next(if last ∈ "block" then "true"_1 else "false"_1, depth, this)
   else
    next(state, depth - 1, this)
  else if this ∈ "*>" then next(state, depth + 1, this) else next(state, depth, this)
 /for (if state ∈ "true" then true else false)

function list(openlist:seq.word, a:attribute2, closelist:seq.word) attribute2
let totwidth = for acc = 0, @e ∈ toseq.a do acc + width.@e + 2 /for (acc)
let noperline = 
 if totwidth < maxwidth then
  10000
 else
  for itemmaxwidth = 0, @e ∈ toseq.a do
   max(itemmaxwidth, width.@e)
  /for (max(1, maxwidth / (itemmaxwidth * 5 + 10) * 5))
for first = 0, acc = "", i = 1, e ∈ toseq.a do
 if i = noperline then
  let newacc = acc + removeclose.text.e
  next(if first = 0 then length.newacc else first
   , if width.e > maxwidth ∧ blockIsLast.newacc then newacc + "," else newacc + "/br,"
   , 1)
 else
  next(first, acc + removeclose.text.e + ",", i + 1)
/for (
 {remove last terminator and trailing \if from acc}
 let t0 = acc >> 1
 let t1 = if last.t0 ∈ "/br" then t0 >> 1 else t0
 let t2 = removeclose.t1
 if totwidth < maxwidth then
  {fits on one line}
  attribute(openlist + t2 + closelist)
 else
  {leave first element on current line and place others in a block}
  let firstelement = subseq(t2, 1, first)
  let part1 = 
   if width.firstelement > maxwidth then
    "<* block $(t2)"
   else
    {adding block so do not need /br between first and second element}
    let shift = if subseq(t2, first + 1, first + 1) = "/br" then first + 1 else first
    firstelement + "<* block" + t2 << shift
  let part2 = if "do while"_1 ∈ closelist then "*> $(closelist)" else closelist + "*>"
  attribute(0, 10000, openlist + part1 + part2)
)

function wrap(prec:int, prein:attribute2, binary:seq.word, postin:attribute2) attribute2
let pre = (toseq.prein)_1
let post = (toseq.postin)_1
let x = 
 if width.pre + width.post > maxwidth ∧ binary ≠ "." then
  if blockIsLast.text.pre then "" else "/br" /if
  + "$(if binary ∈ [".", "_", "^"] then binary else binary + space)"
 else if binary ∈ [".", "_", "^"] then binary else [space] + binary + space
let pre1 = if prec.pre > prec then "($(text.pre))" else text.pre
if prec.post > prec ∨ prec ≠ 3 ∧ prec = prec.post then
 attribute(prec
  , width.pre + width.x + width.post
  , pre1 + if binary = "." then "/nosp (" else x + "(" /if + text.post + ")")
else
 attribute(prec, width.pre + width.x + width.post, pre1 + x + text.post)

function unaryminus(exp:attribute2) attribute2
let prec = 3
let post = (toseq.exp)_1
if prec.post > prec then
 attribute(prec, 3 + width.post, "-($(text.post))")
else
 attribute(prec, 1 + width.post, "-$(text.post)")

function block2(bigexp:boolean, b:attribute2) seq.word
removeclose.if bigexp then "<* block $(text.b) *>" else text.b

function width(s:seq.word) int
for acc = 0, cmd = true, last = "?"_1, w ∈ s
while acc < 10000
do
 if w = escapeformat then
  next(acc, not.cmd, last)
 else if length.s > 20 ∧ w ∈ "/br" ∧ cmd then
  next(10000, cmd, w)
 else
  next(acc + wordwidth(last, w), cmd, w)
/for (acc)

function wordwidth(last:word, w:word) int
if w ∈ ("<* *> /keyword: ./nosp" + escapeformat) ∨ last ∈ "<*" then
 0
else if w ∈ "(,) /ldq /sp" then 1 else length.decodeword.w + 1

function ifthenelse(R:reduction.attribute2) attribute2
let x1 = "/keyword if $(removeclose.text.R_2) /keyword then"
let bigexp = width.R_2 + width.R_4 + width.R_6 + 13 > maxwidth
if not.bigexp then
 attribute(x1 + removeclose.text.R_4 + "/keyword else" + text.R_6 + "/if")
else
 let iselseif = subseq(text.(toseq.R_6)_1, 1, 2) = "/keyword if"
 attribute(0
  , 10000
  , x1 + block2(true, R_4) + "/keyword else" + if iselseif then text.R_6 else "<* block $(text.R_6) *>" /if
  + "/if")

function prettyfunc(a:attribute2, name:attribute2, paraList:attribute2, returnType:attribute2) attribute2
list(
 "/keyword $(text.a)
  $(if first.text.name ∈ "+=_-^" then [space] + text.name else text.name) /nosp ("
 , paraList
 , ") $(text.returnType)")

Below is generated from parser generator.

function action(ruleno:int
 , input:seq.word
 , place:int
 , R:reduction.attribute2
 , stk:stack.stkele.attribute2) attribute2
{Alphabet.= ():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while
 /for W do wl wlend T X F2 A E FP NM L D F F1 G HH}
{RulePrecedence | HH HH comment | comment | let | assert | if | for | W | wl | I | [| $wordlist | (
 | E NM | E comment E | E E_E |_| E W.E | E E * E | E-E | * | E E-E |-| E E > E | E E = E |
 = | > | E E ∧ E | ∧ | E E ∨ E | ∨ | /for | E if E then E else E /if | /if | E if E then E else E | E
 assert E report D E | A W = E | E let A E | D E |}
if ruleno = {F HH E} 1 then
 if width.R_1 + width.R_2 < maxwidth then
  pretty.[R_1, R_2]
 else
  for acc = "", p ∈ toseq.R_1 do
   acc + text.p + if isempty.acc ∧ last.text.p ∈ "*>" then "" else "/br"
  /for (attribute(acc + text.R_2))
else if ruleno = {F HH} 2 then
 if width.R_1 < maxwidth then
  pretty.[R_1]
 else
  for acc = "", p ∈ toseq.R_1 do
   acc + text.p + if isempty.acc ∧ last.text.p ∈ "*>" then "" else "/br"
  /for (attribute(acc >> 1))
else if ruleno = {HH HH comment} 3 then
 R_1 + breakup("<* comment", text.R_2, "*>")
else if ruleno = {HH W NM (FP) T} 4 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W_(FP) T} 5 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W-(FP) T} 6 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W = (FP) T} 7 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W > (FP) T} 8 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W * (FP) T} 9 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W ∧ (FP) T} 10 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W ∨ (FP) T} 11 then
 prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W NM T} 12 then
 pretty.[attribute."/keyword", R_1, R_2, R_3]
else if ruleno = {HH W NM is FP} 13 then
 list("/keyword type $(text.R_2) is", R_4, "")
else if ruleno = {FP T} 14 then
 R_1
else if ruleno = {FP FP, T} 15 then
 R_1 + R_3
else if ruleno = {FP W:T} 16 then
 pretty.[R_1, R_2, R_3]
else if ruleno = {FP FP, W:T} 17 then
 R_1 + pretty.[R_3, R_4, R_5]
else if ruleno = {FP comment W:T} 18 then
 pretty.[R_1, R_2, R_3, R_4]
else if ruleno = {FP FP, comment W:T} 19 then
 R_1 + pretty.[R_3, R_4, R_5, R_6]
else if ruleno = {NM W} 20 then
 R_1
else if ruleno = {NM W:T} 21 then
 pretty.[R_1, R_2, R_3]
else if ruleno = {T W} 22 then
 R_1
else if ruleno = {T W.T} 23 then
 pretty.[R_1, R_2, R_3]
else if ruleno = {E NM} 24 then
 R_1
else if ruleno = {E NM (L)} 25 then
 if length.R_3 = 1 ∧ length.text.R_1 = 1 then
  wrap(3, R_1, ".", R_3)
 else
  list(text.R_1 + "/nosp (", R_3, ")")
else if ruleno = {E (E)} 26 then
 R_2
else if ruleno = {E if E then E else E} 27 then
 ifthenelse.R
else if ruleno = {E if E then E else E /if} 28 then
 ifthenelse.R
else if ruleno = {E E_E} 29 then
 wrap(1, R_1, text.R_2, R_3)
else if ruleno = {E-E} 30 then
 unaryminus.R_2
else if ruleno = {E W.E} 31 then
 wrap(3, R_1, text.R_2, R_3)
else if ruleno = {E E * E} 32 then
 wrap(4, R_1, text.R_2, R_3)
else if ruleno = {E E-E} 33 then
 wrap(5, R_1, text.R_2, R_3)
else if ruleno = {E E = E} 34 then
 wrap(6, R_1, text.R_2, R_3)
else if ruleno = {E E > E} 35 then
 wrap(7, R_1, text.R_2, R_3)
else if ruleno = {E E ∧ E} 36 then
 wrap(8, R_1, text.R_2, R_3)
else if ruleno = {E E ∨ E} 37 then
 wrap(9, R_1, text.R_2, R_3)
else if ruleno = {L E} 38 then
 R_1
else if ruleno = {L L, E} 39 then
 R_1 + R_3
else if ruleno = {E [L]} 40 then
 list("[", R_2, "]")
else if ruleno = {A W = E} 41 then
 R_1 + R_3
else if ruleno = {E let A E} 42 then
 let letname = text.first.toseq.R_2
 attribute(0
  , 10000
  , "/keyword let $(letname) $([space, "="_1, space])
   $(protect(attribute2.[(toseq.R_2)_2], R_3))")
else if ruleno = {E assert E report D E} 43 then
 attribute(0
  , 10000
  , "/keyword assert $(text.R_2)
   $(if width.R_2 + width.R_4 > maxwidth ∧ not.blockIsLast.text.R_2 then
   "/br"
  else
   ""
  )
   /keyword report $(protect(R_4, R_5))")
else if ruleno = {E I} 44 then
 R_1
else if ruleno = {E I.I} 45 then
 pretty.[R_1, R_2, R_3]
else if ruleno = {E $wordlist} 46 then
 pretty2.[breakup("<* literal /ldq", text.R_1 << 1, "*>")]
else if ruleno = {E comment E} 47 then
 let text = 
  text.pretty2.[breakup("<* comment", text.R_1, "*>")]
  + if width.R_1 + width.R_2 > maxwidth then addBr.text.R_2 else text.R_2
 attribute(prec.(toseq.R_2)_1, width.text, text)
else if ruleno = {F1 W = E} 48 then
 pretty.[R_1, attribute.[space, "="_1, space], R_3]
else if ruleno = {F1 F1, W = E} 49 then
 R_1 + pretty.[R_3, attribute.[space, "="_1, space], R_5]
else if ruleno = {F2 F1, W-E} 50 then
 R_1 + pretty.[R_3, attribute."∈", R_5]
else if ruleno = {E for F2 do E /for (E)} 51 then
 let width7 = width.R_7
 let accexp = list("/keyword for", R_2, "/keyword do")
 let finalexp = block2(width7 > maxwidth, R_7)
 let body = block2(width.accexp + width.R_4 + width7 > maxwidth, R_4)
 pretty.[accexp, attribute."$(body) /keyword /for ($(finalexp))"]
else if ruleno = {E for F2 while E do E /for (E)} 52 then
 let width9 = width.R_9
 let finalexp = block2(width9 > maxwidth, R_9)
 let accexp = list("/keyword for", R_2, "")
 let text = 
  if width.accexp + width.R_4 + width.R_6 + width9 + 8 < maxwidth then
   "/keyword while $(text.R_4) /keyword do $(text.R_6)"
  else
   "$(if width.accexp < maxwidth then "/br" else "") /keyword while $(text.R_4)
    /br /keyword do $(block2(true, R_6))"
 pretty.[accexp, attribute."$(text) /keyword /for ($(finalexp))"]
else if ruleno = {D E} 53 then
 R_1
else if ruleno = {X wl E} 54 then
 breakup("<* literal /ldq", subseq(text.R_1, 2, length.text.R_1 - 1), "")
 + attribute("$" + "(*> $(removeclose.text.R_2) <* literal)")
else if ruleno = {X X wl E} 55 then
 R_1 + breakup("", subseq(text.R_2, 2, length.text.R_2 - 1), "")
 + attribute("$" + "(*> $(removeclose.text.R_3) <* literal)")
else if ruleno = {E X wlend} 56 then
 {assert not (subseq (text.first.toseq.R_1, 8, 9) =" 0 0") report" Found"+%n (toseq (R_1+
  breakup ("", subseq (text.R_2, 2, length.text.R_2-1)+dq," *>")))}
 pretty2.[R_1, breakup("", subseq(text.R_2, 2, length.text.R_2 - 1) + dq, "*>")]
else if ruleno = {G F #} 57 then
 R_1
else
 {ruleno}
 assert false report "invalid rule number" + toword.ruleno
 R_1

use otherseq.prettyresult

function %(p:prettyresult) seq.word %.width.p + text.p 