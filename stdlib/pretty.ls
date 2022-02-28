Module pretty

use UTF8

use bits

use format

use standard

use parsersupport.attribute2

use seq.attribute2

use seq.byte

use seq.prettyresult

use otherseq.word

use seq.token.attribute2

use seq.seq.prettyresult

use seq.seq.word

use set.seq.word

use process.seq.seq.word

Function pretty(s:seq.word)seq.word
let tmp0 = text.(toseq.parse.s)_1
removeclose(tmp0, length.tmp0)

Function prettyfile(escape:boolean, modhead:seq.word, text:seq.seq.word) seq.word
for uses = empty:seq.seq.word, libbody = empty:seq.seq.word, result = empty:seq.seq.word, s ∈ text do
 if length.s = 0 then next(uses, libbody, result)
 else if s_1 ∈ "use"then next(uses + reverse.s, libbody, result)
 else if s_1 ∈ "Export unbound"then next(uses, libbody + (" /keyword" + s), result)
 else if s_1 ∈ "Function function type"then next(uses, libbody + pretty.s, result)
 else if s_1 ∈ "module Module"then
  let target = 
   if length.modhead > 1 then subseq(modhead, 1, 6) + s_2 + subseq(modhead, 8, length.modhead)
   else "/keyword"
  let newresult = result + sortuse.uses + libbody + (target + s)
  next(empty:seq.seq.word, empty:seq.seq.word, newresult)
 else
  let temp = 
   if s_1 ∈ "Library library"then
    let parts = break(s, "uses exports", true)
    " /keyword Library" + s_2 + alphasort(parts_1 << 2) + " /br  /keyword" + parts_2
    + " /br  /keyword exports"
    + alphasort(parts_3 << 1)
   else if escape then escapeformat.s else s
  if length.uses = 0 then next(uses, libbody, result + temp)
  else next(uses, libbody + temp, result)
/for(for txt = "", p ∈ result + sortuse.uses + libbody do txt + " /p" + p /for(txt))

function formatuse(a:seq.word)seq.word" /keyword" + reverse.a

Function escapeformat(s:seq.word)seq.word
for acc = "", linelength = 0, c ∈ s do
 if c ∈ " /<  /br  /p  /row"then
  if length.s > maxwidth then next(acc + merge.[encodeword.[char.10], c], 0)
  else next(acc + merge.[space, c], linelength + length.decodeword.c)
 else if c ∈ " /keyword  />  /em  /strong  /cell"then next(acc + merge.[space, c], linelength)
 else if linelength > maxwidth then next(acc + encodeword.[char.10] + c, length.decodeword.c)
 else next(acc + c, linelength + length.decodeword.c)
/for(acc)

function sortuse(a:seq.seq.word)seq.seq.word
for acc = empty:seq.seq.word, @e ∈ alphasort.toseq.asset.a do acc + formatuse.@e /for(acc)

function pretty(b:seq.attribute2)attribute2
let a = for acc = empty:seq.prettyresult, @e ∈ b do acc + toseq.@e /for(acc)
let text = for acc = "", @e ∈ a do acc + text.@e /for(acc)
attribute2.[prettyresult(prec.first.a, for acc = 0, @e ∈ a do acc + width.@e /for(acc), text)
]

function protect(a:seq.word, b:seq.word)seq.word
let a1 = lastsymbol(a, length.a)
let b1 = 
 if subseq(b, 1, 3) = " /< block  /keyword"then b_4
 else if subseq(b, 1, 2) = " /< block"then b_3
 else if first.b = " /keyword"_1 then b_2 else b_1
if a1 = "/if"_1 ∧ b1 ∉ "-+("then removeclose(a, length.a) + " /br" + b
else if b1 ∈ "-+" ∧ a1 ∉ "/if"then
 "(" + a + ") /br(" + b + ")"
else if b1 ∈ "(" ∧ a1 ∉ ("/if)]'" + dq)then
 "(" + a + ")" + " /br" + b
else a + " /br" + b

function removeclose(a:seq.word, i:int)seq.word
if a_i = " />"_1 then removeclose(a, i - 1) + " />"_1
else if a_i = "/if"_1 then removeclose(a, i - 1)else subseq(a, 1, i)

function removeclose(a:seq.word)seq.word if isempty.a then a else removeclose(a, length.a)

function lastsymbol(a:seq.word, i:int)word
if a_i = " />"_1 then lastsymbol(a, i - 1)else a_i

type prettyresult is prec:int, width:int, text:seq.word

type attribute2 is toseq:seq.prettyresult

function parse(l:seq.word)attribute2 parse:attribute2(l)

Export type:attribute2

Export type:prettyresult

Function attribute(text:seq.word)attribute2 attribute2.[prettyresult(0, width.text, text)]

Function precAttribute(p:int, text:seq.word)attribute2 attribute2.[prettyresult(p, width.text, text)]

function attribute:attribute2(text:seq.word)attribute2 attribute2.[prettyresult(0, width.text, text)]

function forward(stk:attribute2, token:attribute2)attribute2 token

Function text(a:attribute2)seq.word text.(toseq.a)_1

function width(a:attribute2)int width.(toseq.a)_1

function +(a:attribute2, b:attribute2)attribute2 attribute2(toseq.a + toseq.b)

function length(a:attribute2)int length.toseq.a

function maxwidth int 100

function list(a:attribute2)attribute2
let totwidth = for acc = 0, @e ∈ toseq.a do acc + width.@e + 2 /for(acc)
let noperline = 
 if totwidth < maxwidth then 10000
 else
  for itemmaxwidth = 0, @e ∈ toseq.a do max(itemmaxwidth, width.@e)/for(max(1, maxwidth / (itemmaxwidth * 5 + 10) * 5))
attribute2.[prettyresult(0
, if totwidth ≥ maxwidth then 10000 else totwidth
, for acc = "", i = 1, e ∈ toseq.a do
 next(acc + removeclose.text.e
 + if i = noperline then" /br, "else", "
 , if i = noperline then 1 else i + 1
 )
/for(acc >> 1)
)
]

function wrap(prec:int, prein:attribute2, binary:seq.word, postin:attribute2)attribute2
let pre = (toseq.prein)_1
let post = (toseq.postin)_1
let x = 
 if width.pre + width.post > maxwidth ∧ binary ≠ "."then
  " /br"
  + if binary ∈ [".", "_", "^"]then binary else binary + space
 else if binary ∈ [".", "_", "^"]then binary
 else[space] + binary + space
let pre1 = 
 if prec.pre > prec then"(" + text.pre + ")"else text.pre
let a = 
 if prec.post > prec ∨ prec ≠ 3 ∧ prec = prec.post then
  prettyresult(prec
  , width.pre + width.x + width.post
  , pre1 + if binary = "."then"("else x + "("/if
  + text.post
  + ")"
  )
 else
  {assert binary ≠"+"report"wrap"+print.prec.pre+print.prec.post+print.prec}
  prettyresult(prec, width.pre + width.x + width.post, pre1 + x + text.post)
attribute2.[a]

function unaryminus(exp:attribute2)attribute2
let prec = 3
let post = (toseq.exp)_1
attribute2.[if prec.post > prec then
 prettyresult(prec, 3 + width.post, "-" + "(" + text.post + ")")
else prettyresult(prec, 1 + width.post, "-" + text.post)
]

function block(b:attribute2)attribute2
let a = (toseq.b)_1
attribute2.[prettyresult(prec.a, 10000, " /< block" + text.a + " />")]

function width(s:seq.word)int
for acc = 0, w ∈ s
while acc < 10000
do if length.s > 20 ∧ w ∈ " /br"then 10000 else acc + length.decodeword.w
/for(acc)

function ifthenelse(R:reduction.attribute2)attribute2
let x1 = " /keyword if" + removeclose.text.R_2 + " /keyword then"
if width.R_2 + width.R_4 + width.R_6 < maxwidth - 13 then
 attribute(x1 + removeclose.text.R_4 + " /keyword else" + text.R_6 + "/if")
else
 let iselseif = subseq(text.(toseq.R_6)_1, 1, 2) = " /keyword if"
 attribute2.[prettyresult(0
 , 10000
 , x1 + removeclose.text.if width.R_2 + width.R_4 < maxwidth then R_4 else block.R_4 /if
 + " /br  /keyword else"
 + if width.R_6 < maxwidth ∨ iselseif then text.R_6
 else" /< block" + text.R_6 + " />"/if
 + "/if"
 )
 ]

function prettyfunc(R:reduction.attribute2)attribute2
pretty.[attribute." /keyword"
, R_1
, if first.text.R_2 ∈ "+=_-^"then attribute([space] + text.R_2)else R_2
, R_3
, R_4
, R_5
, R_6
, if width.R_4 + width.R_7 > maxwidth then attribute(" /br" + text.R_7)else R_7
]

function keyword  seq.word "/keyword"

function bracket( s:seq.word)seq.word "/<"+s+"/>"

Below is generated from parser generator.

function action(ruleno:int, input:seq.word, place:int, R:reduction.attribute2)attribute2
{Alphabet.=():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while /for W do F2 P T L D E FP A F F1 G NM 
}
{RulePrecedence |(| E NM | E comment E | E E_E |_| E W.E | E E * E | E-E | * | E E-E |-| E E > E | E E=E |=| > | E E ∧ E | ∧ | E E ∨ E | ∨ | /for 
| E if E then E else E /if | /if | E if E then E else E | E assert E report D E | A W=E | E let A E | D E |}
if ruleno = {G F #}1 then R_1
else if ruleno = {F W NM(FP)T E}2 then prettyfunc.R
else if ruleno = {F W_(FP)T E}3 then prettyfunc.R
else if ruleno = {F W-(FP)T E}4 then prettyfunc.R
else if ruleno = {F W=(FP)T E}5 then prettyfunc.R
else if ruleno = {F W >(FP)T E}6 then prettyfunc.R
else if ruleno = {F W *(FP)T E}7 then prettyfunc.R
else if ruleno = {F W ∧(FP)T E}8 then prettyfunc.R
else if ruleno = {F W ∨(FP)T E}9 then prettyfunc.R
else if ruleno = {F W NM T E}10 then
 if width.R_4 > maxwidth then pretty.[attribute.keyword, R_1, R_2, R_3, attribute.EOL, R_4]
 else pretty.[attribute.keyword, R_1, R_2, R_3, R_4]
else if ruleno = {F W NM is P}11 then pretty.[attribute.keyword, R_1, R_2, R_3, list.R_4]
else if ruleno = {FP P}12 then list.R_1
else if ruleno = {P T}13 then R_1
else if ruleno = {P P, T}14 then R_1 + R_3
else if ruleno = {P W:T}15 then pretty.[R_1, R_2, R_3]
else if ruleno = {P P, W:T}16 then R_1 + pretty.[R_3, R_4, R_5]
else if ruleno = {P comment W:T}17 then pretty.[R_1, R_2, R_3, R_4]
else if ruleno = {P P, comment W:T}18 then R_1 + pretty.[R_3, R_4, R_5, R_6]
else if ruleno = {E NM}19 then R_1
else if ruleno = {E NM(L)}20 then
 if length.R_3 = 1 ∧ length.text.R_1 = 1 then wrap(3, R_1, ".", R_3)
 else pretty.[R_1, attribute."(", list.R_3, attribute.")"]
else if ruleno = {E(E)}21 then R_2
else if ruleno = {E if E then E else E}22 then ifthenelse.R
else if ruleno = {E if E then E else E /if}23 then ifthenelse.R
else if ruleno = {E E_E}24 then wrap(1, R_1, text.R_2, R_3)
else if ruleno = {E-E}25 then unaryminus.R_2
else if ruleno = {E W.E}26 then wrap(3, R_1, text.R_2, R_3)
else if ruleno = {E E * E}27 then wrap(4, R_1, text.R_2, R_3)
else if ruleno = {E E-E}28 then wrap(5, R_1, text.R_2, R_3)
else if ruleno = {E E=E}29 then wrap(6, R_1, text.R_2, R_3)
else if ruleno = {E E > E}30 then wrap(7, R_1, text.R_2, R_3)
else if ruleno = {E E ∧ E}31 then wrap(8, R_1, text.R_2, R_3)
else if ruleno = {E E ∨ E}32 then wrap(9, R_1, text.R_2, R_3)
else if ruleno = {L E}33 then R_1
else if ruleno = {L L, E}34 then R_1 + R_3
else if ruleno = {E[L]}35 then pretty.[R_1, list.R_2, R_3]
else if ruleno = {A W=E}36 then
 pretty.[R_1, if width.R_3 > maxwidth then block.R_3 else R_3]
else if ruleno = {E let A E}37 then
 attribute2.[prettyresult(0
 , 10000
 ,  keyword+"let" + first.text.R_2 + [space, "="_1, space]
 + protect(text.R_2 << 1, text.R_3)
 )
 ]
else if ruleno = {E assert E report D E}38 then
 attribute2.[prettyresult(0
 , 10000
 ,  keyword+"assert" + text.R_2
 + if width.R_2 + width.R_4 > maxwidth then EOL else""/if
 + keyword
 + "report"
 + protect(text.R_4, text.R_5)
 )
 ]
else if ruleno = {E I}39 then R_1
else if ruleno = {E I.I}40 then pretty.[R_1, R_2, R_3]
else if ruleno = {T W}41 then R_1
else if ruleno = {T W.T}42 then pretty.[R_1, R_2, R_3]
else if ruleno = {E $wordlist}43 then attribute.bracket("literal" + escapeformat.text.R_1)
else if ruleno = {E comment E}44 then
 precAttribute(prec.(toseq.R_2)_1
 , bracket( "comment" + escapeformat.text.R_1  )
 + if width.R_1 + width.R_2 > maxwidth then EOL + text.R_2 else text.R_2
 )
else if ruleno = {NM W}45 then R_1
else if ruleno = {NM W:T}46 then pretty.[R_1, R_2, R_3]
else if ruleno = {F1 W=E}47 then pretty.[R_1, attribute.[space, "="_1, space], R_3]
else if ruleno = {F1 F1, W=E}48 then
 R_1 + pretty.[R_3, attribute.[space, "="_1, space], R_5]
else if ruleno = {F2 F1, W-E}49 then R_1 + pretty.[R_3, attribute."∈", R_5]
else if ruleno = {E for F2 do E /for(E)}50 then
 if width.R_2 + width.R_4 < maxwidth then
  pretty.[attribute(keyword+"for")
  , list.R_2
  , attribute( keyword+"do" + removeclose.text.R_4 +  keyword+"/for")
  , R_6
  , R_7
  , R_8
  ]
 else
  pretty.[attribute(keyword+"for")
  , list.R_2
  , attribute(keyword + "do" + removeclose.text.block.R_4 + EOL + keyword + "/for")
  , R_6
  , R_7
  , R_8
  ]
else if ruleno = {E for F2 while E do E /for(E)}51 then
 if width.R_2 + width.R_4 + width.R_6 < maxwidth then
  pretty.[attribute(keyword+"for")
  , list.R_2
  , attribute(keyword + "while" + text.R_4 + keyword + "do" + removeclose.text.R_6 + keyword
  + "/for")
  , R_8
  , R_9
  , R_10
  ]
 else
  pretty.[attribute(keyword+"for")
  , list.R_2
  , attribute(EOL + keyword + "while" + text.R_4 + EOL + keyword + "do" + removeclose.text.R_6
  + EOL
  + keyword
  + "/for")
  , R_8
  , R_9
  , R_10
  ]
else if ruleno = {D E}52 then R_1
else
 {ruleno}
 assert false report"invalid rule number" + toword.ruleno
 R_1 