Module parsersupport.T

use seq.stkele.T

use stack.stkele.T

use otherseq.token.T

use otherseq.int

use stack.int

use pretty

use standard

use process.seq.word

Export type:stkele.T

Export type:reduction.T

Export type:token.T

type token is w:word, tokenno:int, attribute:T

type stkele is stateno:int, attribute:T

type reduction is toseq:seq.stkele.T

unbound attribute:T(seq.word) T

unbound action(int, seq.word, int, reduction.T, stack.stkele.T) T

unbound text(T) seq.word

unbound forward(stk:T, T) T

unbound errormessage(message:seq.word, input:seq.word, place:int, parsestk:stack.stkele.T) seq.word

Function >1(a:token.T, b:token.T) ordering w.a >1 w.b

Function =(a:token.T, b:token.T) boolean w.a = w.b

Function _(r:reduction.T, n:int) T attribute.(toseq.r)_n

Function last(r:reduction.T) T attribute.(toseq.r)_(length.toseq.r)

Function errormessage:T(message:seq.word, input:seq.word, place:int, parsestk:stack.stkele.T) seq.word
let m = "<* literal $(message) *>"
if subseq(message, 1, 3) = "missing string terminator" then
 m + "/br" + input
else
 m + "/br"
 + for acc = empty:stack.int, x ∈ toseq.parsestk do
  push(acc, stateno.x)
 /for (
  let action = recovery:T_(top.acc)
  let tail = 
   if action > 0 then
    recoverStep:T(acc, action, decodetoken:T(action))
   else
    recoverStep:T(acc, 0, "")
  let m2 = 
   if place > length.input then
    "/br At end of paragraph /br $(m)"
   else
    "/br $(m) /br part of unprocessed input: $(subseq(input, place + 1, place + 10))"
  if subseq(tail, 1, 1) = "problem" then
   tail + "/br failed problem" + %.toseq.acc + m2 + "/br" + input
  else
   let marker = if subseq(tail, 1, 1) = "I" then "99599"_1 else merge."! !"
   let tail2 = 
    if isempty.tail then
     tail
    else if first.tail ∈ ("E T W NM L FP D I" + marker) then
     [marker] + tail << 1
    else if first.tail ∈ "do report then else /for]" then
     "-" + marker + tail
    else if subseq(tail, 1, 3) ∈ ["-E do", "-E while"] then
     "∈" + marker + tail << 2
    else if first.tail ∈ "=" then
     "= $(marker) $(tail << 2)"
    else if first.tail ∈ "," then
     ", $(marker)-$(tail << 2)"
    else if subseq(tail, 1, 2) ∈ ["(FP", "(E"] then
     "(" + marker + tail << 2
    else if subseq(tail, 1, 2) ∈ [") T", ") E", ") $(dq)"] then
     ")" + marker + tail << 2
    else if first.tail ∈ ")" then
     "-$(marker)) $(tail << 1)"
    else if first.tail ∈ "/for" then "/for (" + marker + tail << 3 else tail
   if not.isempty.tail ∧ tail2 = tail then
    "failed unexpected first of tail $(tail)"
   else
    let p = process.pretty(subseq(input, 1, place) + tail2)
    if aborted.p then
     "failed recovery ?L
      /br $(subseq(input, 1, place)) %%%%%%% $(tail2 + "::" + tail)
      /br $(input) mess $(message.p) $(toseq.acc)
      /p"
    else
     {find location of maker in prettied input and remove input after marker and possibly some before}
     if isempty.tail2 then
      result.p + m2
     else
      for acc3 = "", skip = false, w ∈ result.p do
       if w = marker then
        if marker = first.tail2 then next(acc3, true) else next(removemore:T(tail2, acc3), true)
       else if skip ∧ w ∉ "*>" then next(acc3, skip) else next(acc3 + w, skip)
      /for (acc3 + m2)
 )

Function removemore:T(tail2:seq.word, acc3:seq.word) seq.word
let hasblock = if subseq(acc3, length.acc3 - 1, length.acc3) = "<* block" then 2 else 0
let haswhite = 
 if acc3_(length.acc3 - hasblock) ∈ ("/br" + space) then hasblock + 1 else hasblock
let a = acc3 >> haswhite
let len = length.a
if first.tail2 ∈ "/for" ∧ subseq(a, len - 1, len) = "/for (" then
 a << 2
else if first.tail2 ∈ "-" ∧ last.a ∈ "∈" then
 a << 1
else
 {if first.tail2 /in". ." /and last.a /in". ." then a << 1 else}
 if last.a = first.tail2 then
  a << 1
 else if subseq(tail2, 1, 2) = ") !!" then
  {ignore close para} a
 else
  a + "failed $(haswhite)"
  + for acc = "", x ∈ tail2 + "??" + subseq(a, len - 4, len) do
   acc + encodeword([char.0] + decodeword.x)
  /for (acc)
 /if
 + if hasblock = 1 then "<* block" else ""

Function parse:T(initial:T, lextable:seq.token.T, input:seq.word, headeronly:boolean) T
let stringtoken = findindex(tokenlist:T, "$wordlist"_1)
let wlendtoken = findindex(tokenlist:T, "wlend"_1)
let commenttoken = findindex(tokenlist:T, "comment"_1)
let codeinstringtoken = findindex(tokenlist:T, "wl"_1)
let lastrule = if headeronly then 24 else 58
for state = ""
 , lrpart = push(empty:stack.stkele.T, stkele(startstate:T, initial))
 , last = 0
 , idx = 1
 , this ∈ input + "#"
while stateno.top.lrpart ≠ -1
do
 if {in code} isempty.state ∨ first.state ∈ ")" ∧ not(this ∈ ")" ∧ state_2 ∈ dq) then
  if this ∈ "{" then
   next("} $(state)", lrpart, idx, idx + 1)
  else if this ∈ dq then
   next(dq + state, lrpart, idx, idx + 1)
  else
   assert true ∨ this ∉ "}" report errormessage("stray}", input, idx, lrpart)
   let lexindex = binarysearch(lextable, token(this, 0, attribute:T("")))
   let newlrpart = 
    let tokenno = 
     if lexindex < 0 then
      {this is not in lex table}
      let kind = checkinteger.this
      if kind = "WORD"_1 then
       Wtoken:T
      else
       assert kind ≠ "ILLEGAL"_1 report "Illegal character in Integer" + this
       Itoken:T
     else
      tokenno.lextable_lexindex
    let att = if lexindex < 0 then attribute:T([this]) else attribute.lextable_lexindex
    step(lrpart, input, att, tokenno, idx - 1, lastrule)
   let newstate = 
    if isempty.state then
     state
    else if this ∈ "(" then ") $(state)" else if this ∈ ")" then state << 1 else state
   next(newstate, newlrpart, idx, idx + 1)
 else
  let kind = 
   if first.state ∈ dq ∧ this ∈ "(" ∧ input_(idx - 1) = "$"_1 then
    codeinstringtoken
   else if first.state ∈ dq ∧ this ∈ dq then
    if subseq(input, last, last) = dq then stringtoken else wlendtoken
   else if first.state ∈ "}" ∧ this ∈ "}" ∧ subseq(state, 2, 2) ≠ "}" then
    commenttoken
   else
    0
  let newlrpart = 
   if kind = 0 then
    lrpart
   else
    step(lrpart
     , input
     , attribute:T(subseq(input, last, if kind = codeinstringtoken then idx - 1 else idx))
     , {tokenno} kind
     , last - 1
     , lastrule)
  if kind ∈ [commenttoken, stringtoken, wlendtoken]
  ∨ this ∈ ")" ∧ subseq(state, 1, 2) = ") $(dq)" then
   next(state << 1, newlrpart, idx, idx + 1)
  else if kind = codeinstringtoken then
   next(") $(state)", newlrpart, idx, idx + 1)
  else
   {in string or comment.}
   let newstate = 
    if first.state ∈ dq then
     state
    else if this ∈ "{" then "} $(state)" else if this ∈ "}" then state << 1 else state
   next(newstate, lrpart, last, idx + 1)
/for (
 let r = toseq.lrpart
 assert isempty.state ∨ headeronly
 report errormessage("missing string terminator $(state)", input, idx, lrpart)
 attribute.r_min(length.r, 2)
)

function step(stk:stack.stkele.T
 , input:seq.word
 , attrib:T
 , tokenno:int
 , place:int
 , lastrule:int) stack.stkele.T
let stateno = stateno.top.stk
let actioncode = actiontable:T_(tokenno + length.tokenlist:T * stateno)
if actioncode > 0 then
 push(stk, stkele(actioncode, forward(attribute.top.stk, attrib)))
else
 assert actioncode < 0 report errormessage("syntax error", input, place, stk)
 let ruleno = -actioncode
 let rulelen = rulelength:T_ruleno
 let leftside = action(ruleno, input, place, reduction.top(stk, rulelen), stk)
 let newstk = pop(stk, rulelen)
 if ruleno ≥ lastrule then
  push(newstk, stkele(-1, leftside))
 else
  let newstateno = actiontable:T_(leftside:T_ruleno + length.tokenlist:T * stateno.top.newstk)
  assert newstateno > 0 report "???"
  let newstkele = stkele(newstateno, leftside)
  step(push(newstk, newstkele), input, attrib, tokenno, place, lastrule)

function recoverStep:T(stk:stack.int, tokenno:int, list:seq.word) seq.word
let actioncode = 
 if tokenno = 0 then 0 else actiontable:T_(tokenno + length.tokenlist:T * top.stk)
if actioncode > 0 then
 {shift} recoverStep:T(push(stk, actioncode), 0, list)
else if actioncode < 0 then
 {reduce}
 recoverStep:T(pop(stk, rulelength:T_(-actioncode)), leftside:T_(-actioncode), list)
else
 let action2 = recovery:T_(top.stk)
 if action2 > 0 then
  {shift}
  if tokenlist:T_action2 ∈ "#" then
   list
  else
   recoverStep:T(stk, action2, list + decodetoken:T(action2))
 else if action2 = 0 then
  "problem $(tokenno) $(toseq.stk) $(list)"
 else
  let leftside = leftside:T_(-action2)
  {reduce} recoverStep:T(pop(stk, rulelength:T_(-action2)), leftside, list)

function decodetoken:T(token:int) seq.word
let t = tokenlist:T_token
if t ∈ "F2" then
 "W = W, W ∈ W"
else if t ∈ "A" then "W = W" else if t ∈ "wlend" then ") $(dq)" else [t]

Function sortedlextable:T seq.token.T sort.lextable:T

function lextable:T seq.token.T
{generated by genlex module in tools}
[token("#"_1, 19, attribute:T("#"))
 , token("("_1, 3, attribute:T("("))
 , token(")"_1, 4, attribute:T(")"))
 , token("*"_1, 10, attribute:T("*"))
 , token("+"_1, 8, attribute:T("+"))
 , token(","_1, 12, attribute:T(","))
 , token("-"_1, 8, attribute:T("-"))
 , token("."_1, 1, attribute:T("."))
 , token(". "_1, 1, attribute:T("."))
 , token("/"_1, 10, attribute:T("/"))
 , token("/for"_1, 29, attribute:T("/for"))
 , token("/if"_1, 15, attribute:T("/if"))
 , token("0"_1, 17, attribute:T("0"))
 , token("2"_1, 17, attribute:T("2"))
 , token(":"_1, 5, attribute:T(":"))
 , token("<"_1, 6, attribute:T("<"))
 , token("<<"_1, 10, attribute:T("<<"))
 , token("="_1, 2, attribute:T("="))
 , token(">"_1, 6, attribute:T(">"))
 , token(">1"_1, 6, attribute:T(">1"))
 , token(">2"_1, 6, attribute:T(">2"))
 , token(">>"_1, 10, attribute:T(">>"))
 , token("Function"_1, 30, attribute:T("Function"))
 , token("I"_1, 17, attribute:T("I"))
 , token("T"_1, 30, attribute:T("T"))
 , token("W"_1, 30, attribute:T("W"))
 , token("["_1, 13, attribute:T("["))
 , token("\"_1, 10, attribute:T("\"))
 , token("]"_1, 7, attribute:T("]"))
 , token("^"_1, 14, attribute:T("^"))
 , token("_"_1, 14, attribute:T("_"))
 , token("a"_1, 30, attribute:T("a"))
 , token("assert"_1, 23, attribute:T("assert"))
 , token("do"_1, 31, attribute:T("do"))
 , token("else"_1, 21, attribute:T("else"))
 , token("empty"_1, 30, attribute:T("empty"))
 , token("for"_1, 9, attribute:T("for"))
 , token("function"_1, 30, attribute:T("function"))
 , token("i"_1, 30, attribute:T("i"))
 , token("if"_1, 18, attribute:T("if"))
 , token("in"_1, 30, attribute:T("in"))
 , token("inst"_1, 30, attribute:T("inst"))
 , token("int"_1, 30, attribute:T("int"))
 , token("is"_1, 16, attribute:T("is"))
 , token("let"_1, 22, attribute:T("let"))
 , token("mod"_1, 10, attribute:T("mod"))
 , token("mytype"_1, 30, attribute:T("mytype"))
 , token("report"_1, 24, attribute:T("report"))
 , token("seq"_1, 30, attribute:T("seq"))
 , token("then"_1, 20, attribute:T("then"))
 , token("use"_1, 30, attribute:T("use"))
 , token("while"_1, 28, attribute:T("while"))
 , token("wlend"_1, 33, attribute:T("wlend"))
 , token("word"_1, 30, attribute:T("word"))
 , token("∈"_1, 8, attribute:T("∈"))
 , token("∉"_1, 8, attribute:T("∉"))
 , token("∧"_1, 25, attribute:T("∧"))
 , token("∨"_1, 26, attribute:T("∨"))
 , token("∩"_1, 10, attribute:T("∩"))
 , token("∪"_1, 10, attribute:T("∪"))
 , token("≠"_1, 6, attribute:T("≠"))
 , token("≤"_1, 6, attribute:T("≤"))
 , token("≥"_1, 6, attribute:T("≥"))
 , token("⊻"_1, 26, attribute:T("⊻"))
 , token(dq_1, 27, attribute:T(dq))
 , token(merge."/ and", 25, attribute:T("∧"))
 , token(merge."/ cap", 10, attribute:T("∩"))
 , token(merge."/ cup", 10, attribute:T("∪"))
 , token(merge."/ ge", 6, attribute:T("≥"))
 , token(merge."/ in", 8, attribute:T("∈"))
 , token(merge."/ le", 6, attribute:T("≤"))
 , token(merge."/ ne", 6, attribute:T("≠"))
 , token(merge."/ nin", 8, attribute:T("∉"))
 , token(merge."/ or", 26, attribute:T("∨"))
 , token(merge."/ xor", 8, attribute:T("⊻"))]

function Wtoken:T int {generated by genlex module in tools} 30

function Itoken:T int {generated by genlex module in tools} 17

function rulelength:T seq.int
[2, 1, 2, 6, 6, 6, 6, 6, 6, 6, 6, 3, 4, 1, 3, 3, 5, 4, 6, 1
 , 3, 1, 3, 1, 4, 3, 6, 7, 3, 2, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3
 , 3, 3, 5, 1, 3, 1, 2, 3, 5, 5, 8, 10, 1, 2, 3, 2, 2]

function leftside:T seq.int
[43, 43, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 39, 39, 39, 39, 39, 39, 40
 , 40, 34, 34, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 41, 41, 38
 , 37, 38, 38, 38, 38, 38, 38, 44, 44, 36, 38, 38, 42, 35, 35, 38, 45]

function tokenlist:T seq.word
".= ():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while /for W do
 wl wlend T X F2 A E FP NM L D F F1 G HH"

function startstate:T int 1

function finalstate:T int 14

function recovery:T seq.int
[{1}-0, {2 NM} 40, {3 #} 19, {4}-2, {5 (} 3
 , {6 (} 3, {7 (} 3, {8}-20, {9 (} 3, {10 (} 3
 , {11 (} 3, {12 (} 3, {13 T} 34, {14}-57, {15}-3
 , {16 A} 37, {17 F2} 36, {18 E} 38, {19}-46, {20 E} 38
 , {21}-20, {22 E} 38, {23 E} 38, {24 E} 38, {25}-44
 , {26 L} 41, {27 wlend} 33, {28}-1, {29}-24, {30 FP} 39
 , {31 FP} 39, {32 FP} 39, {33 T} 34, {34 FP} 39, {35 FP} 39
 , {36 FP} 39, {37 FP} 39, {38 FP} 39, {39}-12, {40}-22
 , {41 FP} 39, {42 E} 38, {43}-47, {44 =} 2, {45 E} 38
 , {46 =} 2, {47 do} 31, {48,} 12, {49}-54, {50 report} 24
 , {51 E} 38, {52}-30, {53 then} 20, {54)} 4, {55 I} 17
 , {56}-38, {57]} 7, {58 E} 38, {59}-56, {60 E} 38
 , {61 E} 38, {62 E} 38, {63 E} 38, {64 E} 38, {65 E} 38
 , {66 E} 38, {67 L} 41, {68 W} 30, {69}-14, {70}-22
 , {71)} 4, {72)} 4, {73)} 4, {74}-21, {75)} 4
 , {76)} 4, {77)} 4, {78)} 4, {79}-13, {80 T} 34
 , {81)} 4, {82 E} 38, {83}-42, {84 E} 38, {85 E} 38
 , {86 E} 38, {87 W} 30, {88 D} 42, {89}-31, {90 E} 38
 , {91}-26, {92}-45, {93}-40, {94 E} 38, {95}-55
 , {96}-32, {97}-34, {98}-35, {99}-33, {100}-36
 , {101}-37, {102}-29, {103)} 4, {104:} 5, {105 T} 34
 , {106 T} 34, {107 T} 34, {108 T} 34, {109 T} 34, {110 T} 34
 , {111 T} 34, {112 T} 34, {113 T} 34, {114}-23, {115 T} 34
 , {116}-41, {117}-48, {118 /for} 29, {119 do} 31, {120-} 8
 , {121}-53, {122 E} 38, {123 else} 21, {124}-39, {125}-25
 , {126 T} 34, {127}-16, {128}-9, {129 W} 30, {130}-15
 , {131}-22, {132}-7, {133}-8, {134}-6, {135}-10
 , {136}-11, {137}-5, {138}-4, {139 (} 3, {140 E} 38
 , {141 E} 38, {142 E} 38, {143}-43, {144 E} 38, {145}-18
 , {146:} 5, {147 T} 34, {148 E} 38, {149 /for} 29, {150}-49
 , {151}-50, {152}-27, {153 T} 34, {154}-17, {155)} 4
 , {156 (} 3, {157}-28, {158}-19, {159}-51, {160 E} 38
 , {161)} 4, {162}-52]

function actiontable:T seq.int
[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0
 , 0, 4, 0, 6, 0, 0, 0, 7, 0, 9, 0, 5, 0, 0, 0
 , 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 11, 0, 0
 , 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 15
 , 0, 26, 0, 0, 0, 25, 23,-2, 0, 0, 16, 20, 0, 0, 0
 , 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 28, 0, 29, 0
 , 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0,-20,-20,-20, 33,-20,-20
 ,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20
 ,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0
 , 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0,-3, 0, 0, 0, 0,-3,-3, 0,-3, 0,-3, 0, 0
 , 0,-3,-3,-3, 0, 0,-3,-3, 0, 0, 0,-3, 0, 0,-3
 , 0,-3, 0, 0, 27, 0, 0, 43, 0, 29, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 44, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 46, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0
 , 48, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42, 0
 , 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0, 19
 , 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 49, 0, 29, 0, 0
 , 0, 0, 0, 0, 0,-46,-46,-46, 0,-46,-46,-46,-46,-46,-46
 ,-46,-46,-46,-46, 0,-46,-46,-46,-46,-46,-46,-46,-46,-46,-46
 ,-46,-46,-46,-46,-46,-46,-46, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0
 , 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0
 , 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 50, 0, 29
 , 0, 0, 0, 0, 0, 0, 51,-20,-20,-20, 33,-20,-20,-20,-20
 ,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20,-20
 ,-20,-20,-20,-20,-20,-20,-20,-20,-20, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22
 , 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20
 , 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 52
 , 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0
 , 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16
 , 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0
 , 53, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0
 , 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0
 , 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0
 , 0, 54, 0, 29, 0, 0, 0, 0, 0, 0, 55,-44,-44,-44, 0
 ,-44,-44,-44,-44,-44,-44,-44,-44,-44,-44, 0,-44,-44,-44,-44
 ,-44,-44,-44,-44,-44,-44,-44,-44,-44,-44,-44,-44,-44, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0
 , 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0
 , 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0
 , 27, 0, 0, 56, 0, 29, 57, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 59
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61
 , 0, 0, 0, 62, 0, 63, 0, 60, 0, 0, 0, 66, 0, 0, 0
 , 0,-1, 0, 0, 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 ,-24, 67,-24, 0,-24,-24,-24,-24,-24,-24,-24,-24,-24,-24, 0
 ,-24,-24,-24,-24,-24,-24,-24,-24,-24,-24,-24,-24,-24,-24,-24
 ,-24,-24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70
 , 0, 0, 0, 69, 0, 0, 0, 0, 71, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 70, 0, 0, 0, 69, 0, 0, 0, 0, 72, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 70, 0, 0, 0, 69, 0, 0, 0, 0, 73, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 40, 0, 0, 0, 74, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 70, 0, 0, 0, 69, 0, 0, 0, 0, 75, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 70, 0, 0, 0, 69, 0, 0, 0, 0, 76, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 70, 0, 0, 0, 69, 0, 0, 0, 0, 77
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 69, 0, 0, 0, 0
 , 78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 69, 0, 0, 0
 , 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0,-12, 0, 0, 0
 , 0,-12,-12, 0,-12, 0,-12, 0, 0, 0,-12,-12,-12, 0, 0
 ,-12,-12, 0, 0, 0,-12, 0, 0,-12, 0,-12, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80,-22,-22,-22, 0
 ,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22
 ,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 69
 , 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24
 , 0, 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23
 , 0, 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0
 , 0, 27, 0, 0, 43, 0, 29, 0, 0, 0, 0, 0, 0, 0,-47
 ,-47,-47, 0,-47,-47,-47,-47,-47,-47,-47,-47,-47,-47, 0,-47
 ,-47,-47,-47,-47,-47,-47,-47,-47,-47,-47,-47,-47,-47,-47,-47
 ,-47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0
 , 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21
 , 0, 18, 0, 0, 27, 0, 0, 83, 0, 29, 0, 0, 0, 0, 0
 , 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86
 , 0, 0, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 61, 0, 0, 0, 62, 0, 63, 0, 60, 0
 , 0, 0, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 65
 , 0, 0, 0, 0, 0,-54,-54, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 62, 0, 63, 0, 60
 , 0, 0, 0, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 88, 64
 , 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17
 , 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0
 , 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 89, 0
 , 29, 0, 0, 0, 0, 0, 0, 0,-30,-30,-30, 0,-30,-30,-30
 ,-30,-30,-30,-30,-30, 66,-30, 0,-30,-30,-30,-30,-30,-30,-30
 ,-30,-30,-30,-30,-30,-30,-30,-30,-30,-30, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 62, 0
 , 63, 0, 60, 0, 0, 0, 66, 0, 0, 0, 0, 0, 90, 0, 0
 , 0, 0, 64, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 91, 0, 62
 , 0, 63, 0, 60, 0, 0, 0, 66, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0,-38
 , 0, 62,-38, 63, 0, 60, 0,-38, 0, 66, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 93, 0, 0, 0, 0, 94, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25
 , 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18
 , 0, 0, 27, 0, 0, 95, 0, 29, 0, 0, 0, 0, 0, 0, 0
 ,-56,-56,-56, 0,-56,-56,-56,-56,-56,-56,-56,-56,-56,-56, 0
 ,-56,-56,-56,-56,-56,-56,-56,-56,-56,-56,-56,-56,-56,-56,-56
 ,-56,-56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0
 , 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21
 , 0, 18, 0, 0, 27, 0, 0, 96, 0, 29, 0, 0, 0, 0, 0
 , 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26, 0
 , 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0, 0
 , 21, 0, 18, 0, 0, 27, 0, 0, 97, 0, 29, 0, 0, 0, 0
 , 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26
 , 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0
 , 0, 21, 0, 18, 0, 0, 27, 0, 0, 98, 0, 29, 0, 0, 0
 , 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42, 0
 , 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0, 19
 , 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 99, 0, 29, 0, 0
 , 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42
 , 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0
 , 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 100, 0, 29, 0
 , 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0
 , 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0
 , 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 101, 0, 29
 , 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17
 , 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0
 , 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 102, 0
 , 29, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22
 , 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20
 , 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 56
 , 0, 29, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 104, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-14,-14, 0, 0
 , 0,-14,-14, 0,-14,-14,-14, 0, 0, 0,-14,-14,-14, 0, 0
 ,-14,-14, 0, 0, 0,-14, 0, 0,-14, 0,-14, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80,-22,-22,-22, 105
 ,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22
 ,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106
 , 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 108, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 109, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 ,-21,-21,-21, 0,-21,-21,-21,-21,-21,-21,-21,-21,-21,-21,-21
 ,-21,-21,-21,-21,-21,-21,-21,-21,-21,-21,-21,-21,-21,-21,-21
 ,-21,-21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 111, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 112, 0, 0, 0, 0, 0, 0, 0, 107, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 113, 0, 0, 0, 0, 0, 0, 0, 107
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0,-13, 0, 0, 0, 0,-13,-13, 0,-13
 , 107,-13, 0, 0, 0,-13,-13,-13, 0, 0,-13,-13, 0, 0, 0
 ,-13, 0, 0,-13, 0,-13, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 40, 0, 0, 0, 114, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 115, 0, 0, 0, 0, 0
 , 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22
 , 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20
 , 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 116
 , 0, 29, 0, 0, 0, 0, 0, 0, 0, 61,-42,-42, 0, 62,-42
 , 63,-42, 60,-42,-42,-42, 66,-42, 0,-42,-42,-42,-42,-42,-42
 ,-42,-42, 64, 65,-42,-42,-42,-42,-42,-42,-42, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0
 , 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0
 , 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0
 , 0, 117, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0
 , 0, 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0
 , 0, 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27
 , 0, 0, 118, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0
 , 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0
 , 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0
 , 27, 0, 0, 119, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 120, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25
 , 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18
 , 0, 0, 27, 0, 0, 121, 0, 29, 0, 122, 0, 0, 0, 0, 0
 ,-31,-31,-31, 0,-31,-31,-31,-31,-31,-31,-31,-31, 66,-31, 0
 ,-31,-31,-31,-31,-31,-31,-31,-31,-31,-31,-31,-31,-31,-31,-31
 ,-31,-31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0
 , 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21
 , 0, 18, 0, 0, 27, 0, 0, 123, 0, 29, 0, 0, 0, 0, 0
 , 0, 0,-26,-26,-26, 0,-26,-26,-26,-26,-26,-26,-26,-26,-26
 ,-26, 0,-26,-26,-26,-26,-26,-26,-26,-26,-26,-26,-26,-26,-26
 ,-26,-26,-26,-26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0,-45,-45,-45, 0,-45,-45,-45,-45,-45,-45,-45,-45
 ,-45,-45, 0,-45,-45,-45,-45,-45,-45,-45,-45,-45,-45,-45,-45
 ,-45,-45,-45,-45,-45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0,-40,-40,-40, 0,-40,-40,-40,-40,-40,-40,-40
 ,-40,-40,-40, 0,-40,-40,-40,-40,-40,-40,-40,-40,-40,-40,-40
 ,-40,-40,-40,-40,-40,-40, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42
 , 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0
 , 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 124, 0, 29, 0
 , 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 62, 0, 63, 0, 60
 , 0, 0, 0, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64
 , 65, 0, 0, 0, 0, 0,-55,-55, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0,-32,-32,-32, 0,-32,-32,-32,-32
 ,-32,-32,-32,-32, 66,-32, 0,-32,-32,-32,-32,-32,-32,-32,-32
 ,-32,-32,-32,-32,-32,-32,-32,-32,-32, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0,-34,-34,-34, 0,-34,-34, 63
 ,-34, 60,-34,-34,-34, 66,-34, 0,-34,-34,-34,-34,-34,-34,-34
 ,-34,-34,-34,-34,-34,-34,-34,-34,-34,-34, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0,-35,-35,-35, 0,-35,-35
 , 63,-35, 60,-35,-35,-35, 66,-35, 0,-35,-35,-35,-35,-35,-35
 ,-35,-35,-35,-35,-35,-35,-35,-35,-35,-35,-35, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-33,-33,-33, 0,-33
 ,-33,-33,-33, 60,-33,-33,-33, 66,-33, 0,-33,-33,-33,-33,-33
 ,-33,-33,-33,-33,-33,-33,-33,-33,-33,-33,-33,-33, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61,-36,-36, 0
 , 62,-36, 63,-36, 60,-36,-36,-36, 66,-36, 0,-36,-36,-36,-36
 ,-36,-36,-36,-36,-36,-36,-36,-36,-36,-36,-36,-36,-36, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61,-37,-37
 , 0, 62,-37, 63,-37, 60,-37,-37,-37, 66,-37, 0,-37,-37,-37
 ,-37,-37,-37,-37,-37, 64,-37,-37,-37,-37,-37,-37,-37,-37, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-29,-29
 ,-29, 0,-29,-29,-29,-29,-29,-29,-29,-29,-29,-29, 0,-29,-29
 ,-29,-29,-29,-29,-29,-29,-29,-29,-29,-29,-29,-29,-29,-29,-29
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 125, 0, 0, 0, 0, 0, 0, 0, 94, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40
 , 0, 0, 0, 127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 40, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 131, 0, 0, 0, 130, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 40, 0, 0, 0, 132, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 40, 0, 0, 0, 133, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 40, 0, 0, 0, 134, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 40, 0, 0, 0, 135, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 136, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 137, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-23,-23,-23, 0,-23
 ,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23
 ,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23,-23, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 138, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61,-41, 0
 , 0, 62, 0, 63,-41, 60,-41, 0,-41, 66, 0, 0,-41,-41, 0
 , 0, 0,-41,-41, 0, 64, 65,-41, 0, 0,-41, 0,-41, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0
 , 0, 0, 62, 0, 63, 0, 60, 0,-48, 0, 66, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61
 , 0, 0, 0, 62, 0, 63, 0, 60, 0, 0, 0, 66, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 64, 65, 0, 0, 139, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 61, 0, 0, 0, 62, 0, 63, 0, 60, 0, 0, 0, 66, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 64, 65, 0, 0, 0, 0, 140
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 141, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 61,-53, 0, 0, 62, 0, 63,-53, 60,-53, 0,-53, 66
 , 0, 0,-53,-53, 0, 0, 0,-53,-53, 0, 64, 65,-53, 0, 0
 ,-53, 0,-53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26
 , 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0
 , 0, 21, 0, 18, 0, 0, 27, 0, 0, 143, 0, 29, 0, 0, 0
 , 0, 0, 0, 0, 61, 0, 0, 0, 62, 0, 63, 0, 60, 0, 0
 , 0, 66, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 64, 65, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 61, 0,-39, 0, 62,-39, 63, 0, 60, 0
 ,-39, 0, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 65
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0,-25,-25,-25, 0,-25,-25,-25,-25,-25
 ,-25,-25,-25,-25,-25, 0,-25,-25,-25,-25,-25,-25,-25,-25,-25
 ,-25,-25,-25,-25,-25,-25,-25,-25, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 40, 0, 0, 0, 145, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0,-16,-16, 0, 0, 0,-16
 ,-16, 0,-16,-16,-16, 0, 0, 0,-16,-16,-16, 0, 0,-16,-16
 , 0, 0, 0,-16, 0, 0,-16, 0,-16, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-9, 0, 0, 0, 0
 ,-9,-9, 0,-9, 0,-9, 0, 0, 0,-9,-9,-9, 0, 0,-9
 ,-9, 0, 0, 0,-9, 0, 0,-9, 0,-9, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-15,-15, 0
 , 0, 0,-15,-15, 0,-15,-15,-15, 0, 0, 0,-15,-15,-15, 0
 , 0,-15,-15, 0, 0, 0,-15, 0, 0,-15, 0,-15, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80,-22,-22,-22
 , 147,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22
 ,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22,-22, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-7
 , 0, 0, 0, 0,-7,-7, 0,-7, 0,-7, 0, 0, 0,-7,-7
 ,-7, 0, 0,-7,-7, 0, 0, 0,-7, 0, 0,-7, 0,-7, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 ,-8, 0, 0, 0, 0,-8,-8, 0,-8, 0,-8, 0, 0, 0,-8
 ,-8,-8, 0, 0,-8,-8, 0, 0, 0,-8, 0, 0,-8, 0,-8
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0,-6, 0, 0, 0, 0,-6,-6, 0,-6, 0,-6, 0, 0, 0
 ,-6,-6,-6, 0, 0,-6,-6, 0, 0, 0,-6, 0, 0,-6, 0
 ,-6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0,-10, 0, 0, 0, 0,-10,-10, 0,-10, 0,-10, 0, 0
 , 0,-10,-10,-10, 0, 0,-10,-10, 0, 0, 0,-10, 0, 0,-10
 , 0,-10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0,-11, 0, 0, 0, 0,-11,-11, 0,-11, 0,-11, 0
 , 0, 0,-11,-11,-11, 0, 0,-11,-11, 0, 0, 0,-11, 0, 0
 ,-11, 0,-11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0,-5, 0, 0, 0, 0,-5,-5, 0,-5, 0,-5
 , 0, 0, 0,-5,-5,-5, 0, 0,-5,-5, 0, 0, 0,-5, 0
 , 0,-5, 0,-5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0,-4, 0, 0, 0, 0,-4,-4, 0,-4, 0
 ,-4, 0, 0, 0,-4,-4,-4, 0, 0,-4,-4, 0, 0, 0,-4
 , 0, 0,-4, 0,-4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 148, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17, 0
 , 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0, 0
 , 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 149, 0, 29
 , 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22, 17
 , 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20, 0
 , 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 150, 0
 , 29, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 22
 , 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0, 16, 20
 , 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0, 0, 151
 , 0, 29, 0, 0, 0, 0, 0, 0, 0, 61,-43,-43, 0, 62,-43
 , 63,-43, 60,-43,-43,-43, 66,-43, 0,-43,-43,-43,-43,-43,-43
 ,-43,-43, 64, 65,-43,-43,-43,-43,-43,-43,-43, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0
 , 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0, 0
 , 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27, 0
 , 0, 152, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0,-18,-18, 0
 , 0, 0,-18,-18, 0,-18,-18,-18, 0, 0, 0,-18,-18,-18, 0
 , 0,-18,-18, 0, 0, 0,-18, 0, 0,-18, 0,-18, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0
 , 154, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 24, 0, 0, 0, 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25
 , 23, 0, 0, 0, 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18
 , 0, 0, 27, 0, 0, 155, 0, 29, 0, 0, 0, 0, 0, 0, 0
 , 61, 0, 0, 0, 62, 0, 63, 0, 60, 0, 0, 0, 66, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 64, 65, 0, 0, 156, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 61, 0, 0, 0, 62, 0, 63, 0, 60, 0,-49, 0, 66, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 65, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 61, 0, 0, 0, 62, 0, 63, 0, 60, 0, 0, 0, 66
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 65, 0,-50, 0
 , 0,-50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 61,-27,-27, 0, 62,-27, 63,-27, 60,-27,-27,-27
 , 66, 157, 0,-27,-27,-27,-27,-27,-27,-27,-27, 64, 65,-27,-27
 ,-27,-27,-27,-27,-27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 40, 0, 0, 0, 158, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0,-17,-17, 0, 0, 0,-17,-17, 0,-17
 ,-17,-17, 0, 0, 0,-17,-17,-17, 0, 0,-17,-17, 0, 0, 0
 ,-17, 0, 0,-17, 0,-17, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 61, 0, 159, 0, 62, 0, 63, 0, 60
 , 0, 0, 0, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64
 , 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 160, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0,-28,-28,-28, 0,-28,-28,-28
 ,-28,-28,-28,-28,-28,-28,-28, 0,-28,-28,-28,-28,-28,-28,-28
 ,-28,-28,-28,-28,-28,-28,-28,-28,-28,-28, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-19,-19, 0, 0, 0
 ,-19,-19, 0,-19,-19,-19, 0, 0, 0,-19,-19,-19, 0, 0,-19
 ,-19, 0, 0, 0,-19, 0, 0,-19, 0,-19, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-51,-51,-51, 0,-51
 ,-51,-51,-51,-51,-51,-51,-51,-51,-51, 0,-51,-51,-51,-51,-51
 ,-51,-51,-51,-51,-51,-51,-51,-51,-51,-51,-51,-51, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0
 , 0, 0, 22, 17, 0, 42, 0, 26, 0, 0, 0, 25, 23, 0, 0
 , 0, 16, 20, 0, 0, 0, 19, 0, 0, 21, 0, 18, 0, 0, 27
 , 0, 0, 161, 0, 29, 0, 0, 0, 0, 0, 0, 0, 61, 0, 162
 , 0, 62, 0, 63, 0, 60, 0, 0, 0, 66, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 0, 0, 0
 , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-52,-52
 ,-52, 0,-52,-52,-52,-52,-52,-52,-52,-52,-52,-52, 0,-52,-52
 ,-52,-52,-52,-52,-52,-52,-52,-52,-52,-52,-52,-52,-52,-52,-52] 