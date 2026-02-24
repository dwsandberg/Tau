Module genPEG

use PEG

use PEGgenNoTable

use PEGparse

use PEGrules

use seq.int

use seq1.int

use set.int

use seq.pegpart

use seq.pegrule

use standard

use seq1.tableEntry

use seq.word

use set.word

function createSubTable(rules:seq.pegrule) PEGtable
let flaglist = "/trace /error /notable /isWords /common /wordsAttribute /nogrammar"
for
 flags = empty:seq.pegpart
 , flags2 = empty:set.word
 , subs = empty:seq.pegpart
 , p ∈ parts.rules sub 1
do
 if (part.p) sub 1 ∈ flaglist then next(flags + p, flags2 + (part.p) sub 1, subs)
 else next(flags, flags2, subs + p)
for flags3 = flags, e ∈ toseq(asset.flaglist \ flags2)
do flags3 + pegpart(%.e + "S2 Else /end", "$.0 $.2")
for lastpart = "", e ∈ flaglist do lastpart + "!" + e
let z3 =
 adjust.[
  rule(
   "*"
   , "S2"
   , [pegpart("S1", "$.0 $.1")]
   + subs
   + pegpart("//br", "$.0")
   + pegpart("$semicolon", "$.0:")
   + pegpart(lastpart + "! /end ! /else any", "$.0 $.1")
  )
  , rule("S1", flags3)
  , rule("Else", [pegpart("/else S2", "$.1"), pegpart("", "")])
 ],
maketable(
 z3
 , "dq:(dq), // /, //action /action, //br /br
 "
 , false
)

function rule(kind:seq.word, left:seq.word, parts:seq.pegpart) pegrule
pegrule(kind sub 1, left sub 1, parts, 0, NT)

function rule(left:seq.word, parts:seq.pegpart) pegrule
pegrule("d" sub 1, left sub 1, parts, 0, NT)

Function generatePEG(input:seq.word) seq.seq.word
let r = parse(input, attribute("", empty:seq.pegrule))
let maxi = i.top.stk.r
assert status.r ∈ "MatchPrefix" ∧ subseq(input, maxi, maxi) = "[" ∨ maxi = n.input report
 red."Error in PEG grammar"
 + "/br:(subseq(input, 1, maxi - 1))/br Unparsed Input: :(subseq(input, maxi, maxi + 8))"
let grammarpart = input << (maxi - 1)
let substitutionsTable = createSubTable.grammar.result.r
let templatedecs = applySubstitutions(substitutionsTable, template),
if grammarpart sub 1 ∉ "[" then templatedecs
else
 let gin = PEGparse.grammarpart
 let wordmap = extractValue(input >> (n.grammarpart + 1), "wordmap")
 let vals =
  run(
   substitutionsTable
   , "/isWords T /else F /end /error T /else F /end /notable T /else F /end wordmap"
  )
 let isWords = vals sub 2 = "T" sub 1
 {Generate table code}
 let errors = vals sub 3 = "T" sub 1
 let notable = vals sub 4 = "T" sub 1
 let addrecover = errors ∧ not.notable,
 let tbl = makeTbl(gin, addrecover),
 if notable then applySubstitutions(substitutionsTable, notable(gin, tbl, wordmap))
 else
  let tblEle = if isWords then "tableEntry" else "tblEle"
  for table2 = "", i ∈ arithseq(n.tbl, 1, 1)
  do
   let te = tbl sub i
   let Recover =
    if not.addrecover ∧ not.isWords then ""
    else if isempty.recover.te then ",:(dq."")"
    else ",:(dq.recover.te)",
   table2
   + "{:(i)}:(tblEle)(:(action.te),:(applySubs(wordmap, [match.te])),:(Sstate.te),:(Fstate.te):(Recover)),",
  [
   textGrammar.gin
   , applySubs(
    substitutionsTable
    , "function action(partno:int, R:seq.attributeType /common, commonName:commonType /end /error, rinfo:resultType /end)attributeType"
   )
   + makeAction.gin
   , "function mytable seq.:(tblEle)[:(table2 >> 1)]"
  ]
  + templatedecs

function makeAction(gin:seq.pegrule) seq.word
for acc = "", partno = 2, r ∈ gin
do
 let x =
  for partno0 = partno, acc0 = acc, p ∈ parts.r
  do
   let tmp =
    if replacement.p ∈ ["/All"] then ""
    else "if partno =:(partno0)then:(fixit(replacement.p, NTcount(p, gin) + 1))else",
   next(partno0 + 1, acc0 + tmp),
  acc0,
 next(x, partno + n.parts.r),
acc >> 1 + "else R sub 1"

function fixit(r:seq.word, noNT:int) seq.word
if n.r < 3 then r
else
 let none = merge.".."
 for acc = "", l2 = none, l1 = none, e ∈ r + ".."
 do
  if l1 ∈ "." ∧ l2 ∈ "$" then
   let offset = noNT - toint.e - 1
   let new = if offset = 0 then "R sub n.R" else "R sub(n.R-:(offset))",
   next(acc + new, none, none)
  else next(if l2 = none then acc else acc + l2, l1, e),
 acc

Function applySubstitutions(table:PEGtable, intemplate:seq.seq.word) seq.seq.word
for acc = empty:seq.seq.word, p ∈ intemplate
do
 let tmp = applySubs(table, p),
 if isempty.tmp then acc else acc + tmp,
acc

function applySubs(wordmap:seq.word, p:seq.word) seq.word replaceWords(p, wordmap)

function applySubs(table:PEGtable, p:seq.word) seq.word
let tmp = run(table, p)
assert tmp sub 1 ∈ "Match" report "sub problem in genPEG::(p):(tmp)",
tmp << 1

function template seq.seq.word
[
 "/wordsAttribute /else function =(seq.word, attributeType)boolean true /end"
 , "function $(int)attributeType empty:seq.attributeType sub 1"
 , "use standard"
 , "use seq.tblEle"
 , "use seq1.frame"
 , "use stack.frame"
 , "use seq1.attributeType"
 , "use PEGrules"
 , "/isWords /else type tblEle is action:state, match:seqElementType, Sstate:state, Fstate:state /error, recover:seq.word /end /end"
 , "/error function recoveryEnding(rinfo:resultType /nogrammar, mytable:seq.tableEntry /end)seq.word /br
 for acc =:(dq.""), frame ∈ reverse.toseq.stk.rinfo do /br
 if action.Sstate.frame ∈[T, T', NT]then acc+recover.mytable sub index.Sstate.frame else acc acc /else function place(r:resultType)int i.top.stk.r /end"
 , "type frame is Sstate:state, Fstate:state, i:int, result:seq.attributeType, faili:int, failresult:seq.attributeType"
 , "type resultType is stk:stack.frame /error, input:seq.seqElementType, place:int, faili:int /end /trace, trace:seq.word /end"
 , "Function status(a:resultType)word if Sstate.top.stk.a ≠ Match then 'Failed else if place.a ={length of input}faili.top.stk.a then 'Match else 'MatchPrefix"
 , "Function result(a:resultType)attributeType last.result.top.stk.a"
 , "/trace function tracestart(trace:seq.word)seq.word:(dq)/br Key to column labels S--step no; D--Depth of Stack F--on fail reset I to F; I--Location in input; Lower case are values on top of stack /p
 S /td D /td f /td success /td fail /td result /td Result /td F /td State /td I /td Remaining input /td /tr
 $semicolon(trace):(dq)/end"
 , "/trace function trace(stepno:int, trace0:seq.word, stk:stack.frame, result:seq.attributeType, faili:int, state:state, i:int, input:seq.seqElementType /error, recovery:seq.word /end)seq.word let stkdata = %.n.toseq.stk+if isempty.stk then:(dq)/td /td /td /td:(dq)else:(dq)/td $semicolon(faili.top.stk)/td $semicolon(Sstate.top.stk)/td $semicolon(Fstate.top.stk)/td $semicolon(last.result.top.stk):(dq), trace0+:(dq)$semicolon(stepno)/td $semicolon(stkdata)/td $semicolon(%(:(dq)^:(dq), result)>> 1)/td $semicolon(faili)/td $semicolon(state)/td $semicolon(i)/td $semicolon(subseq(input, i, min(i+20, n.input-1)))/td /error $semicolon(recovery)/td /end /tr
 :(dq)/end"
 , "function parse(myinput0:seq.seqElementType, /nogrammar table:seq.tblEle, /else /end initAttr:attributeType /common, commonName:commonType /end /trace, startStep:int, endStep:int /end)resultType /br
 let myinput = packed(myinput0+endMark)/br
 let packedTable = packed./nogrammar table /else mytable /end /br
 for /trace stepno = 1, trace0 =:(dq):(dq), /end /error rinfo = resultType(empty:stack.frame, myinput, 0, 1 /trace,:(dq):(dq)/end), /end stk = empty:stack.frame, state = startstate, i = 1, inputi = myinput sub 1, result =[initAttr], faili = 1, failresult =[initAttr]/br
 while(toint.state > toint.Match /br
 /trace ∧ stepno ≤ endStep)do let trace = if stepno < startStep then trace0 else /error let tmp = if isempty.stk.rinfo then:(dq."")else:(dq)$semicolon(place.rinfo)/td $semicolon(recoveryEnding(rinfo, table)):(dq)/end trace(stepno, trace0, stk, result, faili, state, i, myinput /error, tmp /end)/else)do /end /br
 let actionState = action.state /br
 if actionState = Fail then{goto Fstate.top.stk, i = faili.top, pop.stk, discard result}/br
 let top = top.stk /br
 if toint.action.Fstate.top ≥ toint.S' then let newi = i.top next(/trace stepno+1, trace, /end /error rinfo, /end pop.stk, nextState.Fstate.top, newi, idxNB(myinput, newi), result.top, faili.top, failresult.top)else /br
 next(/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Fstate.top, faili.top, idxNB(myinput, faili.top), failresult.top, faili.top, failresult.top)/br
 else if actionState = Success* then{goto Sstate.top.stk, pop.stk, keep result}let top = top.stk, next(/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Sstate.top, i, inputi, result.top+result, faili.top, failresult.top)/br
 else if actionState = Discard* then /br
 let top = top.stk, /br
 /error let newrinfo = if i > place.rinfo then resultType(stk, myinput, i, faili /trace, trace /end)else rinfo /end next(/trace stepno+1, trace, /end /error newrinfo, /end stk, nextState.state, i, inputi, result.top, i, result.top)/br
 else if actionState = All then let top = top.stk let att =[toAttribute(result sub n.result, subseq(myinput, i.top, i-1))], next(/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Sstate.top, i, inputi, result.top+att, faili.top, failresult.top)/br
 else if actionState = Lambda then /br
 /error let newrinfo = if i > place.rinfo then resultType(stk, myinput, i, faili /trace, trace /end)else rinfo /end /br
 let att =[action(reduceNo.state, result /common, commonName /end /error, newrinfo /end)]next(/trace stepno+1, trace, /end /error newrinfo, /end stk, nextState2.state, i, inputi, result+att, faili, failresult)/br
 else if actionState = Reduce then let top = top.stk, /br
 /error let newrinfo = if i > place.rinfo ∨ faili ≠ faili.rinfo then resultType(stk, myinput, i, faili /trace, trace /end)else rinfo /end /br
 let att =[action(reduceNo.state, result /common, commonName /end /error, newrinfo /end)]next(/trace stepno+1, trace, /end /error newrinfo, /end pop.stk, Sstate.top, i, inputi, result.top+att, faili.top, failresult.top)/br
 else if actionState = Reduce* then /error let newrinfo = if i > place.rinfo ∨ faili ≠ faili.rinfo then resultType(stk, myinput, i, faili /trace, trace /end)else rinfo /end /br
 let att =[action(reduceNo.state, result /common, commonName /end /error, newrinfo /end)]/br
 let top = top.stk, /br
 next(/trace stepno+1, trace, /end /error newrinfo, /end stk, nextState.state, i, inputi, att, i, att)/br
 else if actionState = !Reduce then let top = top.stk, let ini = idxNB(myinput, faili.top)next(/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Fstate.top, faili.top, ini, failresult.top, faili.top, failresult.top)/br
 else if actionState = !Fail then let top = top.stk, let ini = idxNB(myinput, i.top)next(/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Sstate.top, i.top, ini, result.top, faili.top, failresult.top)/br
 else if actionState = T then let te = idxNB(packedTable, index.state)if inputi ≠ match.te then{fail}next(/trace stepno+1, trace, /end /error rinfo, /end stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)else next(/trace stepno+1, trace, /end /error rinfo, /end stk, Sstate.te, i+1, idxNB(myinput, i+1), result, faili, failresult)else if actionState = !T then let te = idxNB(packedTable, index.state)if inputi = match.te then{fail}next(/trace stepno+1, trace, /end /error rinfo, /end stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)else next(/trace stepno+1, trace, /end /error rinfo, /end stk, Fstate.te, i, inputi, result, faili, failresult)/br
 else if actionState = MatchAny then let te = idxNB(packedTable, index.state), if inputi = endMark then{fail}next(/trace stepno+1, trace, /end /error rinfo, /end stk, Fstate.te, i, inputi, result, faili, failresult)else let reslt = result+toAttribute(result sub n.result,[inputi])let ini = idxNB(myinput, i+1), next(/trace stepno+1, trace, /end /error rinfo, /end stk, Sstate.te, i+1, ini, reslt, faili, failresult)/br
 else if actionState = T' then /br
 let te = idxNB(packedTable, index.state)if inputi = match.te then /br
 next(/trace stepno+1, trace, /end /error rinfo, /end stk, Sstate.te, i+1, idxNB(myinput, i+1), result, faili, failresult)/br
 else next(/trace stepno+1, trace, /end /error rinfo, /end stk, Fstate.te, i, inputi, result, faili, failresult)/br
 else{match non Terminal}let te = idxNB(packedTable, index.state)assert action.action.te ∈[NT, NT*]report:(dq)PROBLEM PEG $semicolon(state):(dq)/br let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))let tmp =[toAttribute(result sub n.result, empty:seq.seqElementType)]next(/trace stepno+1, trace, /end /error rinfo, /end newstk, nextState.action.te, i, inputi, tmp, i, tmp)/br
 resultType(push(/error stk.rinfo /else stk /end, frame(state, state, /error place.rinfo /else i /end, result, n.myinput, result))/br
 /error, input.rinfo, place.rinfo, faili.rinfo /end /trace, tracestart.trace0 /end)"
]

type attribute is str:seq.word, grammar:seq.pegrule

function toAttribute(a:attribute, b:seq.word) attribute attribute(b, empty:seq.pegrule)

function endMark word encodeword.[char.254]

function toAttribute(a:seq.pegpart) attribute
attribute("", [pegrule("d" sub 1, "?" sub 1, a, 0, NT)])

function parts(a:attribute) seq.pegpart
if isempty.grammar.a then empty:seq.pegpart else parts.(grammar.a) sub 1

function FP(a:seq.word, value:seq.word) attribute
toAttribute(
 if a sub 1 ∈ "attributeType" ∧ value = "seq.word" then [pegpart(a, "$.0:(value)"), pegpart("/wordsAttribute S2 Else /end", "$.0 $.1")]
 else if a sub 1 ∈ "seqElementType" ∧ value = "word" then
  [
   pegpart(a, "$.0:(value)")
   , pegpart("/isWords S2 Else /end", "$.0 $.1")
   , pegpart("tblEle", "$.0 tableEntry")
  ]
 else if a sub 1 ∈ "commonName" then [pegpart(a, "$.0:(value)"), pegpart("/common S2 Else /end", "$.0 $.1")]
 else if a sub 1 ∈ "seqElementType attributeType resultType commonType wordmap" then [pegpart(a, "$.0:(value)")]
 else if a sub 1 ∈ "error trace fix nogrammar notable" then [pegpart(%.merge."/:(a)" + "S2 Else /end", "$.0 $.1")]
 else empty:seq.pegpart
)

function genPEG(
seqElementType:word
, attributeType:attribute
, resultType:thisresult
, place:int
) seq.boolean
{wordmap: K"/br
"sub 1, dq dq sub 1, //"/"sub 1, //action"/action"sub 1,"$"sub 1}
[
 "S function genPEG(FP FP')Type{Str3 B}"
 = toAttribute(parts.$.1 + parts.$.2 + parts.$.5)
 , "/ function genPEG(FP FP')Type" = toAttribute(parts.$.1 + parts.$.2)
 , "Type any.Type" = toAttribute($.1, str.$.1 + "." + str.$.2)
 , "/ any" = $.1
 , "* FP', FP" = toAttribute(parts.$.0 + parts.$.1)
 , "FP any:Type" = FP(str.$.1, str.$.2)
 , "* B any: Str3" = toAttribute(parts.$.0 + parts.FP(str.$.1, str.$.2))
 , "* Str3 !}! C any" = /All
 , "C any: " = $.0
]

<<<< Below is auto generated code >>>>

/br Non-terminals:B C FP FP' S Str3 Type /br
Terminals:(),.:: any function genPEG{}/br
S ← function genPEG(FP FP')Type{Str3 B}/ function genPEG(FP FP')Type /br
Type ← any.Type / any /br
* FP' ←, FP /br
FP ← any:Type /br
* B ← any: Str3 /br
* Str3 ← !}! C any /br
C ← any: 

function action(partno:int, R:seq.attribute) attribute
if partno = 2 then toAttribute(parts.R sub (n.R - 4) + parts.R sub (n.R - 3) + parts.R sub n.R)
else if partno = 3 then toAttribute(parts.R sub (n.R - 2) + parts.R sub (n.R - 1))
else if partno = 4 then toAttribute(R sub (n.R - 1), str.R sub (n.R - 1) + "." + str.R sub n.R)
else if partno = 5 then R sub n.R
else if partno = 6 then toAttribute(parts.R sub (n.R - 1) + parts.R sub n.R)
else if partno = 7 then FP(str.R sub (n.R - 1), str.R sub n.R)
else if partno = 8 then toAttribute(parts.R sub (n.R - 2) + parts.FP(str.R sub (n.R - 1), str.R sub n.R))
else if partno = 10 then R sub (n.R - 1)
else R sub 1

function mytable seq.tableEntry
[
 {1}tableEntry(NT.T'.2, "?" sub 1, Match, Failure, "")
 , {2}tableEntry(T', "function" sub 1, T'.3, Fail, "")
 , {3}tableEntry(T', "genPEG" sub 1, T'.4, Fail, "")
 , {4}tableEntry(T', "(" sub 1, NT.5, Fail, "")
 , {5}tableEntry(NT.MatchAny.26, "FP" sub 1, NT.6, Fail, "")
 , {6}tableEntry(NT.T.24, "FP'" sub 1, T'.7, Fail, "")
 , {7}tableEntry(T', ")" sub 1, NT.8, T.18, "")
 , {8}tableEntry(NT.MatchAny.20, "Type" sub 1, T.9, Fail, "")
 , {9}tableEntry(T, "{" sub 1, NT.10, T.13, "")
 , {10}tableEntry(NT.!T.32, "Str3" sub 1, NT.11, T.13, "")
 , {11}tableEntry(NT.MatchAny.29, "B" sub 1, T.12, T.13, "")
 , {12}tableEntry(T, "}" sub 1, Reduce.2, T.13, "")
 , {13}tableEntry(T, "function" sub 1, T.14, Fail, "")
 , {14}tableEntry(T, "genPEG" sub 1, T.15, Fail, "")
 , {15}tableEntry(T, "(" sub 1, NT.16, Fail, "")
 , {16}tableEntry(NT.MatchAny.26, "FP" sub 1, NT.17, Fail, "")
 , {17}tableEntry(NT.T.24, "FP'" sub 1, T.18, Fail, "")
 , {18}tableEntry(T, ")" sub 1, NT.19, Fail, "")
 , {19}tableEntry(NT.MatchAny.20, "Type" sub 1, Reduce.3, Fail, "")
 , {20}tableEntry(MatchAny, "?" sub 1, T.21, MatchAny.23, "")
 , {21}tableEntry(T, "." sub 1, NT.22, MatchAny.23, "")
 , {22}tableEntry(NT.MatchAny.20, "Type" sub 1, Reduce.4, MatchAny.23, "")
 , {23}tableEntry(MatchAny, "?" sub 1, Reduce.5, Fail, "")
 , {24}tableEntry(T, "," sub 1, NT.25, Success*, "")
 , {25}tableEntry(NT.MatchAny.26, "FP" sub 1, Reduce*(6, T.24), Success*, "")
 , {26}tableEntry(MatchAny, "?" sub 1, T.27, Fail, "")
 , {27}tableEntry(T, ":" sub 1, NT.28, Fail, "")
 , {28}tableEntry(NT.MatchAny.20, "Type" sub 1, Reduce.7, Fail, "")
 , {29}tableEntry(MatchAny, "?" sub 1, T.30, Success*, "")
 , {30}tableEntry(T, ": " sub 1, NT.31, Success*, "")
 , {31}tableEntry(NT.!T.32, "Str3" sub 1, Reduce*(8, MatchAny.29), Success*, "")
 , {32}tableEntry(!T, "}" sub 1, All, NT.33, "")
 , {33}tableEntry(NT.MatchAny.35, "C" sub 1, MatchAny.34, All, "")
 , {34}tableEntry(MatchAny, "?" sub 1, Discard*.!T.32, All, "")
 , {35}tableEntry(MatchAny, "?" sub 1, T.36, !Fail, "")
 , {36}tableEntry(T, ": " sub 1, !Reduce, !Fail, "")
]

function =(seq.word, attribute) boolean true

function $(int) attribute empty:seq.attribute sub 1

use standard

use seq.tableEntry

use seq1.frame

use stack.frame

use seq1.attribute

use PEGrules

function place(r:thisresult) int i.top.stk.r

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.attribute
, faili:int
, failresult:seq.attribute

type thisresult is stk:stack.frame

Function status(a:thisresult) word
if Sstate.top.stk.a ≠ Match then 'Failed
else if place.a = {length of input}faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:thisresult) attribute last.result.top.stk.a

function parse(myinput0:seq.word, initAttr:attribute) thisresult
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = myinput sub 1
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while toint.state > toint.Match
do
 let actionState = action.state,
 if actionState = Fail then
  {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
  let top = top.stk,
  if toint.action.Fstate.top ≥ toint.S' then
   let newi = i.top,
   next(
    pop.stk
    , nextState.Fstate.top
    , newi
    , idxNB(myinput, newi)
    , result.top
    , faili.top
    , failresult.top
   )
  else
   next(
    pop.stk
    , Fstate.top
    , faili.top
    , idxNB(myinput, faili.top)
    , failresult.top
    , faili.top
    , failresult.top
   )
 else if actionState = Success* then
  {goto Sstate.top.stk, pop.stk, keep result}
  let top = top.stk,
  next(pop.stk, Sstate.top, i, inputi, result.top + result, faili.top, failresult.top)
 else if actionState = Discard* then
  let top = top.stk,
  next(stk, nextState.state, i, inputi, result.top, i, result.top)
 else if actionState = All then
  let top = top.stk
  let att = [toAttribute(result sub n.result, subseq(myinput, i.top, i - 1))],
  next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Lambda then
  let att = [action(reduceNo.state, result)],
  next(stk, nextState2.state, i, inputi, result + att, faili, failresult)
 else if actionState = Reduce then
  let top = top.stk
  let att = [action(reduceNo.state, result)],
  next(pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Reduce* then
  let att = [action(reduceNo.state, result)]
  let top = top.stk,
  next(stk, nextState.state, i, inputi, att, i, att)
 else if actionState = !Reduce then
  let top = top.stk
  let ini = idxNB(myinput, faili.top),
  next(pop.stk, Fstate.top, faili.top, ini, failresult.top, faili.top, failresult.top)
 else if actionState = !Fail then
  let top = top.stk
  let ini = idxNB(myinput, i.top),
  next(pop.stk, Sstate.top, i.top, ini, result.top, faili.top, failresult.top)
 else if actionState = T then
  let te = idxNB(packedTable, index.state),
  if inputi ≠ match.te then {fail}next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then {fail}next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then {fail}next(stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(result sub n.result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG:(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(result sub n.result, empty:seq.word)],
  next(newstk, nextState.action.te, i, inputi, tmp, i, tmp),
thisresult.push(stk, frame(state, state, i, result, n.myinput, result)) 