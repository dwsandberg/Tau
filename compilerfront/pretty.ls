Module pretty

use parsersupport.attribute2

use seq.prettyresult

use standard

use otherseq.word

use set.seq.word

Export type:attribute2

Export type:prettyresult

Function addcomments(header:seq.word, org:seq.word) seq.word
{???? does not handle nested comments}
if subseq(org, length.header, length.header) = "{" then
 addcomments(header >> 1
 + subseq(org
 , length.header
 , length.header + findindex(org << length.header, "}"_1)
 )
 + last.header
 , org
 )
else header

Function pretty(s:seq.word) seq.word
if first.s ∈ "Export unbound Builtin builtin" then
 let t = text.(toseq.parse.addcomments(getheader.s, s))_1 >> 1
 if subseq(t, 1, 4) = "/keyword Export type:" then
  {assert false report" here"+subseq (t, 1, findindex (t," ("_1)-1)}
  subseq(t, 1, findindex(t, "("_1) - 1)
  + s << (findindex(s, "{"_1) - 1)
 else t
else
 let tmp0 = text.(toseq.parse.s)_1
 removeclose(tmp0, length.tmp0)

use format

function escape(w:word) word encodeword ([char.0] + decodeword.w)

Function escape2format(s:seq.word) seq.word
for acc = "", w ∈ s do
 acc
 + if w ∈ "/fmt /br /p /row /keyword /end /em /strong /cell" then escape.w
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
  if last ∈ "/fmt" then next(acc + w, linelength - 2, w, incode, lenincode)
  else if w ∈ "/end" then next(acc + w, linelength, w, length.acc, linelength)
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
 if subseq(b, 1, 3) = "/fmt block /keyword" then b_4
 else if subseq(b, 1, 2) = "/fmt block" then b_3
 else if first.b = "/keyword"_1 then b_2 else b_1
if a1 = "/if"_1 ∧ b1 ∉ "-+(" then
 removeclose(a, length.a) + "/br" + b
else if b1 ∈ "-+" ∧ a1 ∉ "/if" then "($(a)) /br ($(b))"
else if b1 ∈ "(" ∧ a1 ∉ "/if)] ' $(dq)" then "($(a)) /br $(b)"
else a + "/br" + b

function removeclose(a:seq.word, i:int) seq.word
if a_i = "/end"_1 then removeclose(a, i - 1) + "/end"_1
else if a_i = "/if"_1 then removeclose(a, i - 1)
else subseq(a, 1, i)

function removeclose(a:seq.word) seq.word if isempty.a then a else removeclose(a, length.a)

function lastsymbol(a:seq.word, i:int) word
if a_i = "/end"_1 then lastsymbol(a, i - 1) else a_i

type prettyresult is prec:int, width:int, text:seq.word

type attribute2 is toseq:seq.prettyresult

function parse(l:seq.word) attribute2 parse:attribute2(l)

function attribute(text:seq.word) attribute2 attribute2.[prettyresult(0, width.text, text)]

function precAttribute(p:int, text:seq.word) attribute2 attribute2.[prettyresult(p, width.text, text)]

function attribute:attribute2(text:seq.word) attribute2 attribute2.[prettyresult(0, width.text, text)]

function forward(stk:attribute2, token:attribute2) attribute2 token

function text(a:attribute2) seq.word text.(toseq.a)_1

function width(a:attribute2) int width.(toseq.a)_1

function +(a:attribute2, b:attribute2) attribute2 attribute2 (toseq.a + toseq.b)

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
/for (removeclose (acc >> 1))
)
]

function wrap(prec:int, prein:attribute2, binary:seq.word, postin:attribute2) attribute2
let pre = (toseq.prein)_1
let post = (toseq.postin)_1
let x = 
 if width.pre + width.post > maxwidth ∧ binary ≠ "." then
  "
   /br $(if binary ∈ [".", "_", "^"] then binary else binary + space)"
 else if binary ∈ [".", "_", "^"] then binary
 else [space] + binary + space
let pre1 = if prec.pre > prec then "($(text.pre))" else text.pre
let a = 
 if prec.post > prec ∨ prec ≠ 3 ∧ prec = prec.post then
  prettyresult(prec
  , width.pre + width.x + width.post
  , pre1 + if binary = "." then "(" else x + "(" /if + text.post
  + ")"
  )
 else
  prettyresult(prec, width.pre + width.x + width.post, pre1 + x + text.post)
attribute2.[a]

function unaryminus(exp:attribute2) attribute2
let prec = 3
let post = (toseq.exp)_1
attribute2.[if prec.post > prec then
 prettyresult(prec, 3 + width.post, "-($(text.post))")
else prettyresult(prec, 1 + width.post, "-$(text.post)")
]

function block(b:attribute2) attribute2
let a = (toseq.b)_1
attribute2.[prettyresult(prec.a, 10000, "/fmt block $(text.a) /end")]

function block(a:seq.word, b:attribute2) seq.word
removeclose.if isempty.a then text.b else "/fmt block $(text.b) /end"

function width(s:seq.word) int
for acc = 0, last = "?"_1, w ∈ s
while acc < 10000
do
 if length.s > 20 ∧ w ∈ "/br" then next(10000, w)
 else next(acc + wordwidth(last, w), w)
/for (acc)

function wordwidth(last:word, w:word) int
if w ∈ "/fmt /end /keyword" ∨ last ∈ "/fmt" then 0
else length.decodeword.w + 1

function ifthenelse(R:reduction.attribute2) attribute2
let x1 = "/keyword if $(removeclose.text.R_2) /keyword then"
if width.R_2 + width.R_4 + width.R_6 < maxwidth - 13 then
 attribute (x1 + removeclose.text.R_4 + "/keyword else" + text.R_6 + "/if")
else
 let iselseif = subseq(text.(toseq.R_6)_1, 1, 2) = "/keyword if"
 attribute2.[prettyresult(0
 , 10000
 , x1
 + removeclose.text.if width.R_2 + width.R_4 < maxwidth then R_4 else block.R_4 /if
 + "/br /keyword else"
 + if width.R_6 < maxwidth ∨ iselseif then text.R_6
 else "/fmt block $(text.R_6) /end" /if
 + "/if"
 )
 ]

function prettyfunc(R:reduction.attribute2) attribute2
pretty.[attribute."/keyword"
, R_1
, if first.text.R_2 ∈ "+=_-^" then attribute ([space] + text.R_2)
else R_2
, attribute ([encodeword.[char.8]] + "(")
, R_4
, R_5
, R_6
, if width.R_4 + width.R_7 > maxwidth then attribute."/br $(text.R_7)"
else R_7
]

Function leftdq seq.word [encodeword.[char.17], dq_1, encodeword.[char.8]]

Below is generated from parser generator.

function action(ruleno:int, input:seq.word, place:int, R:reduction.attribute2) attribute2
{Alphabet.= ():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist
 while /for W do wl F2 P T L D E FP A F F1 G NM X}
{RulePrecedence | (| E NM | E comment E | E E_E |_| E W.E | E E * E | E-E | * | E E-E |-|
 E E > E | E E = E | = | > | E E ∧ E | ∧ | E E ∨ E | ∨ | /for | E if E then E else E /if | /if | E if
 E then E else E | E assert E report D E | A W = E | E let A E | D E |}
if ruleno = {G F #} 1 then R_1
else if ruleno = {F W NM (FP) T E} 2 then prettyfunc.R
else if ruleno = {F W_(FP) T E} 3 then prettyfunc.R
else if ruleno = {F W-(FP) T E} 4 then prettyfunc.R
else if ruleno = {F W = (FP) T E} 5 then prettyfunc.R
else if ruleno = {F W > (FP) T E} 6 then prettyfunc.R
else if ruleno = {F W * (FP) T E} 7 then prettyfunc.R
else if ruleno = {F W ∧ (FP) T E} 8 then prettyfunc.R
else if ruleno = {F W ∨ (FP) T E} 9 then prettyfunc.R
else if ruleno = {F W NM T E} 10 then
 if width.R_4 > maxwidth then
  pretty.[attribute."/keyword", R_1, R_2, R_3, attribute."/br", R_4]
 else pretty.[attribute."/keyword", R_1, R_2, R_3, R_4]
else if ruleno = {F W NM is P} 11 then
 pretty.[attribute."/keyword", R_1, R_2, R_3, list.R_4]
else if ruleno = {FP P} 12 then list.R_1
else if ruleno = {P T} 13 then R_1
else if ruleno = {P P, T} 14 then R_1 + R_3
else if ruleno = {P W:T} 15 then pretty.[R_1, R_2, R_3]
else if ruleno = {P P, W:T} 16 then R_1 + pretty.[R_3, R_4, R_5]
else if ruleno = {P comment W:T} 17 then pretty.[R_1, R_2, R_3, R_4]
else if ruleno = {P P, comment W:T} 18 then R_1 + pretty.[R_3, R_4, R_5, R_6]
else if ruleno = {E NM} 19 then R_1
else if ruleno = {E NM (L)} 20 then
 if length.R_3 = 1 ∧ length.text.R_1 = 1 then
  wrap(3, R_1, ".", R_3)
 else
  pretty.[R_1
  , attribute ([encodeword.[char.8]] + "(")
  , list.R_3
  , attribute.")"
  ]
else if ruleno = {E (E)} 21 then R_2
else if ruleno = {E if E then E else E} 22 then ifthenelse.R
else if ruleno = {E if E then E else E /if} 23 then ifthenelse.R
else if ruleno = {E E_E} 24 then wrap(1, R_1, text.R_2, R_3)
else if ruleno = {E-E} 25 then unaryminus.R_2
else if ruleno = {E W.E} 26 then wrap(3, R_1, text.R_2, R_3)
else if ruleno = {E E * E} 27 then wrap(4, R_1, text.R_2, R_3)
else if ruleno = {E E-E} 28 then wrap(5, R_1, text.R_2, R_3)
else if ruleno = {E E = E} 29 then wrap(6, R_1, text.R_2, R_3)
else if ruleno = {E E > E} 30 then wrap(7, R_1, text.R_2, R_3)
else if ruleno = {E E ∧ E} 31 then wrap(8, R_1, text.R_2, R_3)
else if ruleno = {E E ∨ E} 32 then wrap(9, R_1, text.R_2, R_3)
else if ruleno = {L E} 33 then R_1
else if ruleno = {L L, E} 34 then R_1 + R_3
else if ruleno = {E [L]} 35 then pretty.[R_1, list.R_2, R_3]
else if ruleno = {A W = E} 36 then
 pretty.[R_1, if width.R_3 > maxwidth then block.R_3 else R_3]
else if ruleno = {E let A E} 37 then
 attribute2.[prettyresult(0
 , 10000
 , "/keyword let" + first.text.R_2 + [space, "="_1, space]
 + protect(text.R_2 << 1, text.R_3)
 )
 ]
else if ruleno = {E assert E report D E} 38 then
 attribute2.[prettyresult(0
 , 10000
 , "/keyword assert $(text.R_2)
  $(if width.R_2 + width.R_4 > maxwidth then "
  /br" else "") /keyword report $(protect(text.R_4, text.R_5))"
 )
 ]
else if ruleno = {E I} 39 then R_1
else if ruleno = {E I.I} 40 then pretty.[R_1, R_2, R_3]
else if ruleno = {T W} 41 then R_1
else if ruleno = {T W.T} 42 then pretty.[R_1, R_2, R_3]
else if ruleno = {E $wordlist} 43 then
 breakup.attribute."/fmt literal $(escape2format (leftdq + text.R_1 << 1)) /end"
else if ruleno = {E comment E} 44 then
 precAttribute(prec.(toseq.R_2)_1
 , text.breakup.attribute."/fmt comment $(escape2format.text.R_1) /end"
 + if width.R_1 + width.R_2 > maxwidth then "/br $(text.R_2)"
 else text.R_2
 )
else if ruleno = {NM W} 45 then R_1
else if ruleno = {NM W:T} 46 then pretty.[R_1, R_2, R_3]
else if ruleno = {F1 W = E} 47 then
 pretty.[R_1, attribute.[space, "="_1, space], R_3]
else if ruleno = {F1 F1, W = E} 48 then
 R_1 + pretty.[R_3, attribute.[space, "="_1, space], R_5]
else if ruleno = {F2 F1, W-E} 49 then R_1 + pretty.[R_3, attribute."∈", R_5]
else if ruleno = {E for F2 do E /for (E)} 50 then
 let width7 = width.R_7
 let B = if width.R_2 + width.R_4 + width7 < maxwidth then "" else "/br"
 let finalexp = if width7 > maxwidth then block("/br", R_7) else removeclose.text.R_7
 pretty.[attribute."/keyword for"
 , list.R_2
 , attribute."/keyword do $(block(B, R_4)) $(B) /keyword /for ($(finalexp))"
 ]
else if ruleno = {E for F2 while E do E /for (E)} 51 then
 let width9 = width.R_9
 let B = 
  if width.R_2 + width.R_4 + width.R_6 + width9 < maxwidth then ""
  else "/br"
 let finalexp = if width9 > maxwidth then block("/br", R_9) else removeclose.text.R_9
 pretty.[attribute."/keyword for"
 , list.R_2
 , attribute."$(B) /keyword while $(text.R_4) $(B) /keyword do $(block(B, R_6))
  $(B) /keyword /for ($(finalexp))"
 ]
else if ruleno = {D E} 52 then R_1
else if ruleno = {X wl E} 53 then
 attribute.escape2format.subseq(text.R_1, 2, length.text.R_1 - 1)
 + attribute ("$" + "(/end $(removeclose.text.R_2) /fmt literal)")
else if ruleno = {X X wl E} 54 then
 R_1 + attribute.escape2format.subseq(text.R_2, 2, length.text.R_2 - 1)
 + attribute ("$" + "(/end $(removeclose.text.R_3) /fmt literal)")
else if ruleno = {E X $wordlist} 55 then
 breakup.attribute."/fmt literal $(leftdq
 + text.pretty.[R_1
 , attribute.escape2format.subseq(text.R_2, 2, length.text.R_2 - 1)
 ]
 + dq) /end"
else
 {ruleno}
 assert false report "invalid rule number" + toword.ruleno
 R_1 