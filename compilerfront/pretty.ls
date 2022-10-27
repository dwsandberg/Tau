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

Function addcomments(header:seq.word, org:seq.word) seq.word
header >> 1 + parsecomment(org << (length.header - 1)) + last.header

function parsecomment(txt:seq.word) seq.word
for idx = 1, nest = 0, w ∈ txt + "X"
while nest ≥ 0
do
 if w ∈ "{" then next(idx + 1, nest + 1)
 else if w ∈ "}" then next(idx + 1, nest - 1)
 else next(idx + 1, if nest = 0 then-2 else nest)
/for (if nest = -2 then subseq(txt, 1, idx - 1) else "")

Function pretty(s:seq.word) seq.word pretty(s, false)

Function pretty(s:seq.word, headeronly:boolean) seq.word
if subseq(s, 1, 3) = "Export type:" then s
else
 let tmp0 = text.(toseq.parse:attribute2(attribute."", sortedlextable:attribute2, s, headeronly))_1
 removeclose(tmp0, length.tmp0)

function escape(w:word) word encodeword([char.0] + decodeword.w)

Function escape2format(s:seq.word) seq.word
for acc = "", w ∈ s do
 acc
 + if w ∈ "<* /br /p /row /keyword *> /em /strong /cell /so /sc /sw /sn" then escape.w
 else w
/for (acc)

Function breakup(a:attribute2) attribute2
if width.a < maxwidth ∨ width.a > 10000 then a
else
 for acc = ""
 , linelength = 0
 , last = space
 , incode = 0
 , lenincode = 0
 , w ∈ text.a
 do
  if last ∈ "<*" then next(acc + w, linelength - 2, w, incode, lenincode)
  else if w ∈ "*>" then next(acc + w, linelength, w, length.acc, linelength)
  else if w ∈ "/br" then next(acc + w, 0, w, 0, 0)
  else if w ∈ [escape."/br"_1, escape."/p"_1, escape."/row"_1]
  ∧ last.acc ∉ dq
  ∨ incode = 0 ∧ linelength > maxwidth then
   next(acc + "/br" + w, wordwidth(last, w), w, 0, 0)
  else if incode > 0 ∧ linelength > maxwidth then
   next(subseq(acc, 1, incode - 2) + "/br" + acc << (incode - 2) + w
   , linelength - lenincode - wordwidth(last, w)
   , w
   , 0
   , 0
   )
  else next(acc + w, linelength + wordwidth(last, w), w, incode, lenincode)
 /for (attribute.acc)

Function escapeformat(s:seq.word) seq.word text.breakup.attribute.escape2format.s

Function sortuse(b:seq.seq.word, prefix:seq.word) seq.seq.word
let a = for a = empty:seq.seq.word, u ∈ b do a + reverse.u /for (a)
for acc = empty:seq.seq.word, @e ∈ alphasort.toseq.asset.a do acc + (prefix + reverse.@e) /for (acc)

function pretty(b:seq.attribute2) attribute2
let a = for acc = empty:seq.prettyresult, @e ∈ b do acc + toseq.@e /for (acc)
for text = "", width = 0, @e ∈ a do
 next(text + text.@e, width + width.@e)
/for (attribute2.[prettyresult(prec.first.a, width, text)])

function protect(a:seq.word, b:seq.word) seq.word
let a1 = lastsymbol(a, length.a)
let b1 = 
 if subseq(b, 1, 3) = "<* block /keyword" then b_4
 else if subseq(b, 1, 2) = "<* block" then b_3
 else if first.b = "/keyword"_1 then b_2 else b_1
if a1 = "/if"_1 ∧ b1 ∉ "-+(" then
 removeclose(a, length.a) + "/br" + b
else if b1 ∈ "-+" ∧ a1 ∉ "/if" then "($(a)) /br ($(b))"
else if b1 ∈ "(" ∧ a1 ∉ "/if)] ' $(dq)" then "($(a)) /br $(b)"
else a + "/br" + b

function removeclose(a:seq.word, i:int) seq.word
if a_i = "*>"_1 then removeclose(a, i - 1) + "*>"_1
else if a_i = "/if"_1 then removeclose(a, i - 1) else subseq(a, 1, i)

function removeclose(a:seq.word) seq.word if isempty.a then a else removeclose(a, length.a)

function lastsymbol(a:seq.word, i:int) word
if a_i = "*>"_1 then lastsymbol(a, i - 1) else a_i

type prettyresult is prec:int, width:int, text:seq.word

type attribute2 is toseq:seq.prettyresult

function attribute(text:seq.word) attribute2
attribute2.[prettyresult(0, width.text, text)]

function precAttribute(p:int, text:seq.word) attribute2
attribute2.[prettyresult(p, width.text, text)]

function attribute:attribute2(text:seq.word) attribute2
attribute2.[prettyresult(0, width.text, text)]

function forward(stk:attribute2, token:attribute2) attribute2 token

function text(a:attribute2) seq.word text.(toseq.a)_1

function width(a:attribute2) int width.(toseq.a)_1

function +(a:attribute2, b:attribute2) attribute2 attribute2(toseq.a + toseq.b)

function length(a:attribute2) int length.toseq.a

function maxwidth int 100

function list(a:attribute2) attribute2
let totwidth = for acc = 0, @e ∈ toseq.a do acc + width.@e + 2 /for (acc)
let noperline = 
 if totwidth < maxwidth then 10000
 else
  for itemmaxwidth = 0, @e ∈ toseq.a do
   max(itemmaxwidth, width.@e)
  /for (max(1, maxwidth / (itemmaxwidth * 5 + 10) * 5))
attribute2.[prettyresult(0
, if totwidth ≥ maxwidth then 10000 else totwidth
, for acc = "", i = 1, e ∈ toseq.a do
 next(acc + removeclose.text.e + if i = noperline then "/br," else ","
 , if i = noperline then 1 else i + 1
 )
/for (removeclose(acc >> 1))
)
]

function wrap(prec:int, prein:attribute2, binary:seq.word, postin:attribute2) attribute2
let pre = (toseq.prein)_1
let post = (toseq.postin)_1
let x = 
 if width.pre + width.post > maxwidth ∧ binary ≠ "." then
  "/br $(if binary ∈ [".", "_", "^"] then binary else binary + space)"
 else if binary ∈ [".", "_", "^"] then binary
 else [space] + binary + space
let pre1 = if prec.pre > prec then "($(text.pre))" else text.pre
let a = 
 if prec.post > prec ∨ prec ≠ 3 ∧ prec = prec.post then
  prettyresult(prec
  , width.pre + width.x + width.post
  , pre1 + if binary = "." then [encodeword.[char.8]] + "(" else x + "(" /if
  + text.post
  + ")"
  )
 else prettyresult(prec, width.pre + width.x + width.post, pre1 + x + text.post)
attribute2.[a]

function unaryminus(exp:attribute2) attribute2
let prec = 3
let post = (toseq.exp)_1
attribute2.[if prec.post > prec then prettyresult(prec, 3 + width.post, "-($(text.post))")
else prettyresult(prec, 1 + width.post, "-$(text.post)")
]

function block(b:attribute2) attribute2
let a = (toseq.b)_1
attribute2.[prettyresult(prec.a, 10000, "<* block $(text.a) *>")]

function block(a:seq.word, b:attribute2) seq.word
removeclose.if isempty.a then text.b else "<* block $(text.b) *>"

function width(s:seq.word) int
for acc = 0, last = "?"_1, w ∈ s
while acc < 10000
do
 if length.s > 20 ∧ w ∈ "/br" then next(10000, w)
 else next(acc + wordwidth(last, w), w)
/for (acc)

function wordwidth(last:word, w:word) int
if w ∈ "<* *> /keyword (,):)." ∨ last ∈ "<*" then 0
else length.decodeword.w + 1

function ifthenelse(R:reduction.attribute2) attribute2
let x1 = "/keyword if $(removeclose.text.R_2) /keyword then"
if width.R_2 + width.R_4 + width.R_6 < maxwidth - 13 then
 attribute(x1 + removeclose.text.R_4 + "/keyword else" + text.R_6 + "/if")
else
 let iselseif = subseq(text.(toseq.R_6)_1, 1, 2) = "/keyword if"
 attribute2.[prettyresult(0
 , 10000
 , x1 + removeclose.text.if width.R_2 + width.R_4 < maxwidth then R_4 else block.R_4 /if
 + "/br /keyword else"
 + if width.R_6 < maxwidth ∨ iselseif then text.R_6
 else "<* block $(text.R_6) *>" /if
 + "/if"
 )
 ]

function prettyfunc(R:reduction.attribute2) attribute2
let t = prettyfunc(R_1, R_2, R_4, R_6)
attribute.if width.t + width.R_7 > maxwidth then "$(text.t) /br $(text.R_7)"
else text.t + text.R_7

function prettyfunc(a:attribute2, name:attribute2, paraList:attribute2, returnType:attribute2) attribute2
pretty.[attribute."/keyword $(text.a) $(if first.text.name ∈ "+=_-
 ^" then [space] + text.name else text.name)"
, attribute([encodeword.[char.8]] + "(")
, list.paraList
, attribute.")"
, returnType
]

Function leftdq seq.word [encodeword.[char.0, char1.dq], encodeword.[char.8]]

Below is generated from parser generator.

function action(ruleno:int, input:seq.word, place:int, R:reduction.attribute2, stk:stack.stkele.attribute2) attribute2
{Alphabet.= ():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while /for
 W do wl T X L E F2 D FP A F F1 G NM HH}
{RulePrecedence | HH HH comment | comment | let | assert | if | for | W | wl | I | [| $wordlist | (| E
 NM | E comment E | E E_E |_| E W.E | E E * E | E-E | * | E E-E |-| E E > E | E E = E | = |
 > | E E ∧ E | ∧ | E E ∨ E | ∨ | /for | E if E then E else E /if | /if | E if E then E else E | E assert
 E report D E | A W = E | E let A E | D E |}
if ruleno = {F HH E} 1 then
 attribute.if width.R_1 + width.R_2 > maxwidth then
  for acc = "", w ∈ text.R_1 do
   if w ∈ "<*" then acc + "/br" + w else acc + w
  /for (acc + "/br $(text.R_2)")
 else text.R_1 + text.R_2
else if ruleno = {F HH} 2 then
 if width.R_1 > maxwidth then
  for acc = "", w ∈ text.R_1 do
   if w ∈ "<*" then acc + "/br" + w else acc + w
  /for (attribute.acc)
 else R_1
else if ruleno = {HH HH comment} 3 then
 let R2 = breakup.attribute."<* comment $(escape2format.text.R_2) *>"
 attribute(text.R_1 + text.R2)
else if ruleno = {HH W NM (FP) T} 4 then prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W_(FP) T} 5 then prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W-(FP) T} 6 then prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W = (FP) T} 7 then prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W > (FP) T} 8 then prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W * (FP) T} 9 then prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W ∧ (FP) T} 10 then prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W ∨ (FP) T} 11 then prettyfunc(R_1, R_2, R_4, R_6)
else if ruleno = {HH W NM T} 12 then pretty.[attribute."/keyword", R_1, R_2, R_3]
else if ruleno = {HH W NM is FP} 13 then
 pretty.[attribute."/keyword", R_1, R_2, R_3, list.R_4]
else if ruleno = {FP T} 14 then R_1
else if ruleno = {FP FP, T} 15 then R_1 + R_3
else if ruleno = {FP W:T} 16 then pretty.[R_1, R_2, R_3]
else if ruleno = {FP FP, W:T} 17 then R_1 + pretty.[R_3, R_4, R_5]
else if ruleno = {FP comment W:T} 18 then pretty.[R_1, R_2, R_3, R_4]
else if ruleno = {FP FP, comment W:T} 19 then R_1 + pretty.[R_3, R_4, R_5, R_6]
else if ruleno = {NM W} 20 then R_1
else if ruleno = {NM W:T} 21 then pretty.[R_1, R_2, R_3]
else if ruleno = {T W} 22 then R_1
else if ruleno = {T W.T} 23 then pretty.[R_1, R_2, R_3]
else if ruleno = {E NM} 24 then R_1
else if ruleno = {E NM (L)} 25 then
 if length.R_3 = 1 ∧ length.text.R_1 = 1 then wrap(3, R_1, ".", R_3)
 else
  pretty.[R_1, attribute([encodeword.[char.8]] + "("), list.R_3, attribute.")"]
else if ruleno = {E (E)} 26 then R_2
else if ruleno = {E if E then E else E} 27 then ifthenelse.R
else if ruleno = {E if E then E else E /if} 28 then ifthenelse.R
else if ruleno = {E E_E} 29 then wrap(1, R_1, text.R_2, R_3)
else if ruleno = {E-E} 30 then unaryminus.R_2
else if ruleno = {E W.E} 31 then wrap(3, R_1, text.R_2, R_3)
else if ruleno = {E E * E} 32 then wrap(4, R_1, text.R_2, R_3)
else if ruleno = {E E-E} 33 then wrap(5, R_1, text.R_2, R_3)
else if ruleno = {E E = E} 34 then wrap(6, R_1, text.R_2, R_3)
else if ruleno = {E E > E} 35 then wrap(7, R_1, text.R_2, R_3)
else if ruleno = {E E ∧ E} 36 then wrap(8, R_1, text.R_2, R_3)
else if ruleno = {E E ∨ E} 37 then wrap(9, R_1, text.R_2, R_3)
else if ruleno = {L E} 38 then R_1
else if ruleno = {L L, E} 39 then R_1 + R_3
else if ruleno = {E [L]} 40 then pretty.[R_1, list.R_2, R_3]
else if ruleno = {A W = E} 41 then
 pretty.[R_1, if width.R_3 > maxwidth then block.R_3 else R_3]
else if ruleno = {E let A E} 42 then
 attribute2.[prettyresult(0
 , 10000
 , "/keyword let" + first.text.R_2 + [space, "="_1, space]
 + protect(text.R_2 << 1, text.R_3)
 )
 ]
else if ruleno = {E assert E report D E} 43 then
 attribute2.[prettyresult(0
 , 10000
 , "/keyword assert $(text.R_2) $(if width.R_2 + width.R_4 > maxwidth then "
  /br" else "") /keyword report $(protect(text.R_4, text.R_5))"
 )
 ]
else if ruleno = {E I} 44 then R_1
else if ruleno = {E I.I} 45 then pretty.[R_1, R_2, R_3]
else if ruleno = {E $wordlist} 46 then
 breakup.attribute."<* literal $(escape2format(leftdq + text.R_1 << 1)) *>"
else if ruleno = {E comment E} 47 then
 precAttribute(prec.(toseq.R_2)_1
 , text.breakup.attribute."<* comment $(escape2format.text.R_1) *>"
 + if width.R_1 + width.R_2 > maxwidth then "/br $(text.R_2)" else text.R_2
 )
else if ruleno = {F1 W = E} 48 then
 pretty.[R_1, attribute.[space, "="_1, space], R_3]
else if ruleno = {F1 F1, W = E} 49 then
 R_1 + pretty.[R_3, attribute.[space, "="_1, space], R_5]
else if ruleno = {F2 F1, W-E} 50 then R_1 + pretty.[R_3, attribute."∈", R_5]
else if ruleno = {E for F2 do E /for (E)} 51 then
 let width7 = width.R_7
 let B = if width.R_2 + width.R_4 + width7 < maxwidth then "" else "/br"
 let finalexp = if width7 > maxwidth then block("/br", R_7) else removeclose.text.R_7
 pretty.[attribute."/keyword for"
 , list.R_2
 , attribute."/keyword do $(block(B, R_4)) $(B) /keyword /for ($(finalexp))"
 ]
else if ruleno = {E for F2 while E do E /for (E)} 52 then
 let width9 = width.R_9
 let B = 
  if width.R_2 + width.R_4 + width.R_6 + width9 < maxwidth then ""
  else "/br"
 let finalexp = if width9 > maxwidth then block("/br", R_9) else removeclose.text.R_9
 let accexp = list.R_2
 pretty.[attribute."/keyword for"
 , accexp
 , attribute."$(if width.accexp > maxwidth then "" else B) /keyword while $(text.R_4) $(B) /keyword do
  $(block(B, R_6)) $(B) /keyword /for ($(finalexp))"
 ]
else if ruleno = {D E} 53 then R_1
else if ruleno = {X wl E} 54 then
 attribute.escape2format.subseq(text.R_1, 2, length.text.R_1 - 1)
 + attribute("$" + "(*> $(removeclose.text.R_2) <* literal)")
else if ruleno = {X X wl E} 55 then
 R_1 + attribute.escape2format.subseq(text.R_2, 2, length.text.R_2 - 1)
 + attribute("$" + "(*> $(removeclose.text.R_3) <* literal)")
else if ruleno = {E X $wordlist} 56 then
 breakup.attribute."<* literal $(leftdq
 + text.pretty.[R_1, attribute.escape2format.subseq(text.R_2, 2, length.text.R_2 - 1)]
 + dq) *>"
else if ruleno = {G F #} 57 then R_1
else
 {ruleno}
 assert false report "invalid rule number" + toword.ruleno
 R_1 