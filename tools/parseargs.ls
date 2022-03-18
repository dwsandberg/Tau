module parseargs

use standard

use seq.stkele

use stack.stkele

use set.word

use seq.seq.word

use process.seq.seq.word

Function getarg(b:seq.seq.word, name:word)seq.word
for acc = empty:seq.seq.word, p1 ∈ b
while isempty.acc
do let p = if first.p1 = first."-"then p1 << 1 else p1
if p_1 = name then[p << 1]else acc
/for(if isempty.acc then""else acc_1 /if)

Function getarg:boolean(b:seq.seq.word, name:word)boolean
for acc = empty:seq.seq.word, p1 ∈ b
while isempty.acc
do let p = if first.p1 = first."-"then p1 << 1 else p1
if p_1 = name then[p << 1]else acc
/for(not.isempty.acc)

______________

Function parseargs(otherargs:seq.word, options:seq.word, types:seq.seq.word)seq.seq.word
{let p=parse("b=890 abc-w dfa-d(j(here))")let options="b w d args"let types=["1 890 891 892", "f", "*", ">0", "m b"]}
let p = parse.otherargs
let errors = 
 for txt = "", present = "", t ∈ parse.otherargs do
  next(let i = findindex(first.t, options)
  if i > length.options then txt + "invalid option" + first.t + "."
  else
   let typdesc = types_i
   let typ = first.typdesc
   if typ ∈ "f" ∧ length.t = 1 ∨ typ ∈ "1" ∧ length.t = 2
   ∨ typ ∈ ">0" ∧ length.t > 1
   ∨ typ ∈ "*"then
    if length.typdesc > 1 ∧ last.t ∉ typdesc << 1 then
     txt + "invalid option:" + t + ". Valid values are" + typdesc << 1
    else txt
   else txt + "no of arguments for option" + t + "is incorrect"
  , present + t
  )
 /for(if length.options < length.types then
  let missing = asset.types_(length.options + 1) \ asset.present
  if isempty.missing then txt else txt + "missing options" + toseq.missing
 else txt /if)
assert isempty.errors report"Cmd line syntax errors:" + errors
p

type ATTR is val:seq.seq.word

type stkele is stateno:int, attribute:ATTR

type reduction is toseq:seq.stkele

function forward(stk:ATTR, token:ATTR)ATTR token

Function _(r:reduction, n:int)ATTR attribute.(toseq.r)_n

Function parse(input:seq.word)seq.seq.word
for lrpart = push(empty:stack.stkele, stkele(startstate, ATTR.[""]))
, idx = 1
, this ∈ input + "#"
while stateno.top.lrpart ≠ finalstate
do let tokenno = min(findindex(this, tokenlist), 6)
let newlrpart = step(lrpart, input, ATTR.[[this]], tokenno, idx)
next(newlrpart, idx + 1)
/for(val.attribute.undertop(lrpart, 1))

function step(stk:stack.stkele, input:seq.word, attrib:ATTR, tokenno:int, place:int)stack.stkele
let stateno = stateno.top.stk
let actioncode = actiontable_(tokenno + length.tokenlist * stateno)
if actioncode > 0 then
 if stateno = finalstate then stk
 else push(stk, stkele(actioncode, forward(attribute.top.stk, attrib)))
else
 assert actioncode < 0
 report{errormessage(if text.attrib="#"then"parse error:unexpected end of paragraph"else"parse error state", input, place 
)+" /br"+expect(stateno)}
 "ERROR"
 + subseq(input, 1, place)
 let ruleno = -actioncode
 let rulelen = rulelength_ruleno
 let newstk = pop(stk, rulelen)
 let newstateno = actiontable_(leftside_ruleno + length.tokenlist * stateno.top.newstk)
 assert newstateno > 0 report"????"
 let newstkele = stkele(newstateno, action(ruleno, input, place, reduction.top(stk, rulelen)))
 step(push(newstk, newstkele), input, attrib, tokenno, place)

Function action(ruleno:int, input:seq.word, place:int, R:reduction)ATTR
{Alphabet #()-=W L O F V G}
if ruleno = {G F #}1 then R_1
else if ruleno = {F O}2 then R_1
else if ruleno = {F F O}3 then
 if first.first.val.R_2 ≠ first."args"then ATTR(val.R_1 + val.R_2)
 else if first.first.val.R_1 ≠ first."args"then ATTR(val.R_2 + val.R_1)
 else ATTR([first.val.R_1 + first.val.R_2 << 1] + val.R_1 << 1)
else if ruleno = {O W}4 then ATTR.["args" + first.val.R_1]
else if ruleno = {O-W}5 then R_2
else if ruleno = {O W=W}6 then ATTR.[first.val.R_1 + first.val.R_3]
else if ruleno = {O-W(L)}7 then ATTR.[first.val.R_2 + first.val.R_4]
else if ruleno = {V W}8 then R_1
else if ruleno = {V-}9 then R_1
else if ruleno = {V=}10 then R_1
else if ruleno = {V(V)}11 then ATTR.[first.val.R_1 + first.val.R_2 + first.val.R_3]
else if ruleno = {L V}12 then R_1
else if ruleno = {L L V}13 then ATTR.[first.val.R_1 + first.val.R_2]
else
 {ruleno}
 assert false report"invalid rule number" + toword.ruleno
 R_1

function rulelength seq.int[2, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2]

function leftside seq.int[11, 10, 10, 8, 8, 8, 8, 9, 9, 9, 9, 7, 7]

function tokenlist seq.word"#()-=W L O V F G"

function startstate int 1

function finalstate int 8

function actiontable seq.int
[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 3, 0
, 5, 0, -4, 0, 0, -4, 6, -4, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, -2, 0
, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 8, 0, 0, 4, 0
, 2, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, -5, 11, 0
, -5, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3
, 0, 0, -3, 0, -3, 0, 0, 0, 0, 0, -6, 0, 0, -6, 0, -6, 0, 0, 0, 0
, 0, 0, 17, 0, 15, 12, 14, 13, 0, 16, 0, 0, 0, -10, -10, -10, -10, -10, 0, 0
, 0, 0, 0, 0, 17, 18, 15, 12, 14, 0, 0, 19, 0, 0, 0, -8, -8, -8, -8, -8
, 0, 0, 0, 0, 0, 0, -9, -9, -9, -9, -9, 0, 0, 0, 0, 0, 0, -12, -12, -12
, -12, -12, 0, 0, 0, 0, 0, 0, 17, 0, 15, 12, 14, 0, 0, 20, 0, 0, -7, 0
, 0, -7, 0, -7, 0, 0, 0, 0, 0, 0, -13, -13, -13, -13, -13, 0, 0, 0, 0, 0
, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, -11, -11, -11, -11, -11] 