Module PEGparse

use PEGmachine

use PEGrules

use seq.attribute

use seq.pegpart

use seq1.pegrule

use seq.pegrule

use standard

use seq.word

use set.word

function endMark word encodeword.[char.254]

function toAttribute(a:seq.pegpart) attribute
attribute("", [pegrule("d" sub 1, "?" sub 1, a, 0, NT)])

function parts(a:attribute) seq.pegpart
if isempty.grammar.a then empty:seq.pegpart else parts.(grammar.a) sub 1

Function PEGparse(input:seq.word) seq.pegrule
{This grammar uses", dq" to find end of action since a rule such as <* block" Atom (E)" = let a = E, E2 *> has a comma in the middle of it. Note that this grammar would still not handle the case when E2 starts with a string literal.}
let r = parse(input, attribute("", empty:seq.pegrule)),
adjust(
 if subseq(input, 1, 1) = "function" then postprocess.r
 else
  assert status.r ∈ "Match" report
   let maxi = i.top.stk.r,
   "<* literal Error in PEG grammar *>
   /br:(subseq(input, 1, maxi - 1)) /br Unparsed Input: :(subseq(input, maxi, maxi + 8))",
  grammar.result.r
)

function flaglist seq.word
{flag fix is unused}
"/trace /error /notable /isWords /common /fix /wordsAttribute /nogrammar"

function postprocess(r:thisresult) seq.pegrule
for
 flags = empty:seq.pegpart
 , flags2 = empty:set.word
 , subs = empty:seq.pegpart
 , p ∈ parts.(grammar.result.r) sub 1
do
 if (part.p) sub 1 ∈ flaglist then next(flags + p, flags2 + (part.p) sub 1, subs)
 else next(flags, flags2, subs + p)
for flags3 = flags, e ∈ toseq(asset.flaglist \ flags2)
do flags3 + pegpart(%.e + "S2 Else /end", "$.0 $.2")
for lastpart = "", e ∈ flaglist do lastpart + "!" + e,
[
 rule("*", "S2", flags3 + pegpart("S", "$.0 $.1"))
 , rule("Else", [pegpart("/else S'", "$.1"), pegpart("", "")])
 , rule("*", "S'", [pegpart("S", "$.0 $.1")])
 , rule(
  "S"
  , subs
   + pegpart("//br", "")
   + {????} pegpart("$carrot", ":")
   + pegpart(lastpart + "! /end ! /else any", "$.1")
 )
]

function rule(kind:seq.word, left:seq.word, parts:seq.pegpart) pegrule
pegrule(kind sub 1, left sub 1, parts, 0, NT)

function rule(left:seq.word, parts:seq.pegpart) pegrule
pegrule("d" sub 1, left sub 1, parts, 0, NT)

type attribute is str:seq.word, grammar:seq.pegrule

function toAttribute(a:attribute, b:seq.word) attribute attribute(b, empty:seq.pegrule)

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
{wordmap: K"
/br" sub 1, dq dq sub 1, //" /" sub 1, //action" /action" sub 1," $" sub 1}
[
 "S [dq CodeFormat" = $.1
 , "/ function genPEG (FP FP') Type {Str3 B}"
 = toAttribute(parts.$.1 + parts.$.2 + parts.$.5)
 , "/ function genPEG (FP FP') Type" = toAttribute(parts.$.1 + parts.$.2)
 , "/ F1" = $.1
 , "* F1 ! // * any Part Part'"
 = attribute("", grammar.$.0 + rule("*", str.$.1, parts.$.2 + parts.$.3))
 , "/ ! //+any Part Part'"
 = attribute("", grammar.$.0 + rule("+", str.$.1, parts.$.2 + parts.$.3))
 , "/ ! // any Part Part'"
 = attribute("", grammar.$.0 + rule(str.$.1, parts.$.2 + parts.$.3))
 , "* Part' // Part" = toAttribute(parts.$.0 + parts.$.1)
 , "/ K" = $.0
 , "Part Str //action Str" = toAttribute.[pegpart(str.$.1, str.$.2)]
 , "* Str ! K ! // ! //action any" = /All
 , "* CodeFormat * any Part2 Part2'"
 = attribute("", grammar.$.0 + rule("*", str.$.1, parts.$.2 + parts.$.3))
 , "/+any Part2 Part2'"
 = attribute("", grammar.$.0 + rule("+", str.$.1, parts.$.2 + parts.$.3))
 , "/ any Part2 Part2'" = attribute("", grammar.$.0 + rule(str.$.1, parts.$.2 + parts.$.3))
 , "* Part2' // Part2" = toAttribute(parts.$.0 + parts.$.1)
 , "Part2 Str1 dq = Code', dq" = toAttribute.[pegpart(str.$.1, str.$.2)]
 , "/ Str1 dq = Code']" = toAttribute.[pegpart(str.$.1, str.$.2)]
 , "Code' Code" = /All
 , "* Str1 ! dq any" = /All
 , "* Code dq Str1 dq" = $.0
 , "/ (Code N2)" = $.0
 , "/ [Code N2]" = $.0
 , "/, ! dq" = $.0
 , "/ !, ! dq ! (!) ! [!] any" = $.0
 , "* N2, Code" = $.0
 , "Type any.Type" = toAttribute($.1, str.$.1 + "." + str.$.2)
 , "/ any" = $.1
 , "* FP', FP" = toAttribute(parts.$.0 + parts.$.1)
 , "FP any:Type" = FP(str.$.1, str.$.2)
 , "* B any: Str3" = toAttribute(parts.$.0 + parts.FP(str.$.1, str.$.2))
 , "* Str3 !} ! C any" = /All
 , "C any: " = $.0
]

<<<< Below is auto generated code >>>>

/br Non-terminals:B C Code Code' CodeFormat F1 FP FP' N2 Part Part' Part2 Part2' S Str Str1 Str3 Type
/br Terminals:() *+,.// //action:: = K [] any dq function genPEG {}
/br S ← [dq CodeFormat / function genPEG (FP FP') Type {Str3 B} / function genPEG (FP FP') Type / F1
/br * F1 ← ! // * any Part Part' / ! //+any Part Part' / ! // any Part Part'
/br * Part' ← // Part / K
/br Part ← Str //action Str
/br * Str ← ! K ! // ! //action any
/br * CodeFormat ← * any Part2 Part2' /+any Part2 Part2' / any Part2 Part2'
/br * Part2' ← // Part2
/br Part2 ← Str1 dq = Code', dq / Str1 dq = Code']
/br Code' ← Code
/br * Str1 ← ! dq any
/br * Code ← dq Str1 dq / (Code N2) / [Code N2] /, ! dq / !, ! dq ! (!) ! [!] any
/br * N2 ←, Code
/br Type ← any.Type / any
/br * FP' ←, FP
/br FP ← any:Type
/br * B ← any: Str3
/br * Str3 ← !} ! C any
/br C ← any: 

function action(partno:int, R:seq.attribute) attribute
if partno = 2 then R sub n.R
else if partno = 3 then toAttribute(parts.R sub (n.R - 4) + parts.R sub (n.R - 3) + parts.R sub n.R)
else if partno = 4 then toAttribute(parts.R sub (n.R - 2) + parts.R sub (n.R - 1))
else if partno = 5 then R sub n.R
else if partno = 6 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
   + rule("*", str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 7 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
   + rule("+", str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 8 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
   + rule(str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 9 then toAttribute(parts.R sub (n.R - 1) + parts.R sub n.R)
else if partno = 10 then R sub n.R
else if partno = 11 then toAttribute.[pegpart(str.R sub (n.R - 1), str.R sub n.R)]
else if partno = 13 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
   + rule("*", str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 14 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
   + rule("+", str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 15 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
   + rule(str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 16 then toAttribute(parts.R sub (n.R - 1) + parts.R sub n.R)
else if partno = 17 then toAttribute.[pegpart(str.R sub (n.R - 1), str.R sub n.R)]
else if partno = 18 then toAttribute.[pegpart(str.R sub (n.R - 1), str.R sub n.R)]
else if partno = 21 then R sub (n.R - 1)
else if partno = 22 then R sub (n.R - 2)
else if partno = 23 then R sub (n.R - 2)
else if partno = 24 then R sub n.R
else if partno = 25 then R sub (n.R - 1)
else if partno = 26 then R sub (n.R - 1)
else if partno = 27 then toAttribute(R sub (n.R - 1), str.R sub (n.R - 1) + "." + str.R sub n.R)
else if partno = 28 then R sub n.R
else if partno = 29 then toAttribute(parts.R sub (n.R - 1) + parts.R sub n.R)
else if partno = 30 then FP(str.R sub (n.R - 1), str.R sub n.R)
else if partno = 31 then toAttribute(parts.R sub (n.R - 2) + parts.FP(str.R sub (n.R - 1), str.R sub n.R))
else if partno = 33 then R sub (n.R - 1)
else R sub 1

function mytable seq.tableEntry
[
 {1} tableEntry(NT.T'.2, "?" sub 1, Match, Failure, "")
 , {2} tableEntry(T', "[" sub 1, T.3, T'.5, "")
 , {3} tableEntry(T, dq sub 1, NT.4, T'.5, "")
 , {4} tableEntry(NT.T'.48, "CodeFormat" sub 1, Reduce.2, T'.5, "")
 , {5} tableEntry(T', "function" sub 1, T'.6, NT.23, "")
 , {6} tableEntry(T', "genPEG" sub 1, T'.7, NT.23, "")
 , {7} tableEntry(T', "(" sub 1, NT.8, NT.23, "")
 , {8} tableEntry(NT.MatchAny.103, "FP" sub 1, NT.9, S'.NT.23, "")
 , {9} tableEntry(NT.T.101, "FP'" sub 1, T'.10, S'.NT.23, "")
 , {10} tableEntry(T', ")" sub 1, NT.11, T.21, "")
 , {11} tableEntry(NT.MatchAny.97, "Type" sub 1, T.12, S'.NT.23, "")
 , {12} tableEntry(T, "{" sub 1, NT.13, T'.16, "")
 , {13} tableEntry(NT.!T.109, "Str3" sub 1, NT.14, T'.16, "")
 , {14} tableEntry(NT.MatchAny.106, "B" sub 1, T.15, T'.16, "")
 , {15} tableEntry(T, "}" sub 1, Reduce.3, T'.16, "")
 , {16} tableEntry(T', "function" sub 1, T.17, NT.23, "")
 , {17} tableEntry(T, "genPEG" sub 1, T.18, NT.23, "")
 , {18} tableEntry(T, "(" sub 1, NT.19, NT.23, "")
 , {19} tableEntry(NT.MatchAny.103, "FP" sub 1, NT.20, NT.23, "")
 , {20} tableEntry(NT.T.101, "FP'" sub 1, T.21, NT.23, "")
 , {21} tableEntry(T, ")" sub 1, NT.22, NT.23, "")
 , {22} tableEntry(NT.MatchAny.97, "Type" sub 1, Reduce.4, NT.23, "")
 , {23} tableEntry(NT.!T.24, "F1" sub 1, Reduce.5, Fail, "")
 , {24} tableEntry(!T, "/" sub 1, !T.29, T.25, "")
 , {25} tableEntry(T, "*" sub 1, MatchAny.26, !T.29, "")
 , {26} tableEntry(MatchAny, "?" sub 1, NT.27, !T.29, "")
 , {27} tableEntry(NT.41, "Part" sub 1, NT.28, !T.29, "")
 , {28} tableEntry(NT.T'.38, "Part'" sub 1, Reduce*(6, !T.24), !T.29, "")
 , {29} tableEntry(!T, "/" sub 1, !T.34, T.30, "")
 , {30} tableEntry(T, "+" sub 1, MatchAny.31, !T.34, "")
 , {31} tableEntry(MatchAny, "?" sub 1, NT.32, !T.34, "")
 , {32} tableEntry(NT.41, "Part" sub 1, NT.33, !T.34, "")
 , {33} tableEntry(NT.T'.38, "Part'" sub 1, Reduce*(7, !T.24), !T.34, "")
 , {34} tableEntry(!T, "/" sub 1, Success*, MatchAny.35, "")
 , {35} tableEntry(MatchAny, "?" sub 1, NT.36, Success*, "")
 , {36} tableEntry(NT.41, "Part" sub 1, NT.37, Success*, "")
 , {37} tableEntry(NT.T'.38, "Part'" sub 1, Reduce*(8, !T.24), Success*, "")
 , {38} tableEntry(T', "/" sub 1, NT.39, T.40, "")
 , {39} tableEntry(NT.41, "Part" sub 1, Reduce*(9, T'.38), T.40, "")
 , {40} tableEntry(T, "/br" sub 1, Reduce*(10, T'.38), Success*, "")
 , {41} tableEntry(NT.!T.44, "Str" sub 1, T.42, Fail, "")
 , {42} tableEntry(T, "/action" sub 1, NT.43, Fail, "")
 , {43} tableEntry(NT.!T.44, "Str" sub 1, Reduce.11, Fail, "")
 , {44} tableEntry(!T, "/br" sub 1, All, !T.45, "")
 , {45} tableEntry(!T, "/" sub 1, All, !T.46, "")
 , {46} tableEntry(!T, "/action" sub 1, All, MatchAny.47, "")
 , {47} tableEntry(MatchAny, "?" sub 1, Discard*.!T.44, All, "")
 , {48} tableEntry(T', "*" sub 1, MatchAny.49, T'.52, "")
 , {49} tableEntry(MatchAny, "?" sub 1, NT.50, T'.52, "")
 , {50} tableEntry(NT.61, "Part2" sub 1, NT.51, T'.52, "")
 , {51} tableEntry(NT.T.59, "Part2'" sub 1, Reduce*(13, T'.48), T'.52, "")
 , {52} tableEntry(T', "+" sub 1, MatchAny.53, MatchAny.56, "")
 , {53} tableEntry(MatchAny, "?" sub 1, NT.54, MatchAny.56, "")
 , {54} tableEntry(NT.61, "Part2" sub 1, NT.55, MatchAny.56, "")
 , {55} tableEntry(NT.T.59, "Part2'" sub 1, Reduce*(14, T'.48), MatchAny.56, "")
 , {56} tableEntry(MatchAny, "?" sub 1, NT.57, Success*, "")
 , {57} tableEntry(NT.61, "Part2" sub 1, NT.58, Success*, "")
 , {58} tableEntry(NT.T.59, "Part2'" sub 1, Reduce*(15, T'.48), Success*, "")
 , {59} tableEntry(T, "/" sub 1, NT.60, Success*, "")
 , {60} tableEntry(NT.61, "Part2" sub 1, Reduce*(16, T.59), Success*, "")
 , {61} tableEntry(NT.!T.73, "Str1" sub 1, T'.62, Fail, "")
 , {62} tableEntry(T', dq sub 1, T'.63, T.68, "")
 , {63} tableEntry(T', "=" sub 1, NT.64, Fail, "")
 , {64} tableEntry(NT.72, "Code'" sub 1, T'.65, Fail, "")
 , {65} tableEntry(T', "," sub 1, T.66, T.71, "")
 , {66} tableEntry(T, dq sub 1, Reduce.17, NT.67, "")
 , {67} tableEntry(NT.!T.73, "Str1" sub 1, T.68, Fail, "")
 , {68} tableEntry(T, dq sub 1, T.69, Fail, "")
 , {69} tableEntry(T, "=" sub 1, NT.70, Fail, "")
 , {70} tableEntry(NT.72, "Code'" sub 1, T.71, Fail, "")
 , {71} tableEntry(T, "]" sub 1, Reduce.18, Fail, "")
 , {72} tableEntry(NT.T'.75, "Code" sub 1, All, Fail, "")
 , {73} tableEntry(!T, dq sub 1, All, MatchAny.74, "")
 , {74} tableEntry(MatchAny, "?" sub 1, Discard*.!T.73, All, "")
 , {75} tableEntry(T', dq sub 1, NT.76, T'.78, "")
 , {76} tableEntry(NT.!T.73, "Str1" sub 1, T.77, T'.78, "")
 , {77} tableEntry(T, dq sub 1, Reduce*(21, T'.75), T'.78, "")
 , {78} tableEntry(T', "(" sub 1, NT.79, T'.82, "")
 , {79} tableEntry(NT.T'.75, "Code" sub 1, NT.80, T'.82, "")
 , {80} tableEntry(NT.T.95, "N2" sub 1, T.81, T'.82, "")
 , {81} tableEntry(T, ")" sub 1, Reduce*(22, T'.75), T'.82, "")
 , {82} tableEntry(T', "[" sub 1, NT.83, T.86, "")
 , {83} tableEntry(NT.T'.75, "Code" sub 1, NT.84, T.86, "")
 , {84} tableEntry(NT.T.95, "N2" sub 1, T.85, T.86, "")
 , {85} tableEntry(T, "]" sub 1, Reduce*(23, T'.75), T.86, "")
 , {86} tableEntry(T, "," sub 1, !T.87, !T.88, "")
 , {87} tableEntry(!T, dq sub 1, !T.88, Reduce*(24, T'.75), "")
 , {88} tableEntry(!T, "," sub 1, Success*, !T.89, "")
 , {89} tableEntry(!T, dq sub 1, Success*, !T.90, "")
 , {90} tableEntry(!T, "(" sub 1, Success*, !T.91, "")
 , {91} tableEntry(!T, ")" sub 1, Success*, !T.92, "")
 , {92} tableEntry(!T, "[" sub 1, Success*, !T.93, "")
 , {93} tableEntry(!T, "]" sub 1, Success*, MatchAny.94, "")
 , {94} tableEntry(MatchAny, "?" sub 1, Reduce*(25, T'.75), Success*, "")
 , {95} tableEntry(T, "," sub 1, NT.96, Success*, "")
 , {96} tableEntry(NT.T'.75, "Code" sub 1, Reduce*(26, T.95), Success*, "")
 , {97} tableEntry(MatchAny, "?" sub 1, T.98, MatchAny.100, "")
 , {98} tableEntry(T, "." sub 1, NT.99, MatchAny.100, "")
 , {99} tableEntry(NT.MatchAny.97, "Type" sub 1, Reduce.27, MatchAny.100, "")
 , {100} tableEntry(MatchAny, "?" sub 1, Reduce.28, Fail, "")
 , {101} tableEntry(T, "," sub 1, NT.102, Success*, "")
 , {102} tableEntry(NT.MatchAny.103, "FP" sub 1, Reduce*(29, T.101), Success*, "")
 , {103} tableEntry(MatchAny, "?" sub 1, T.104, Fail, "")
 , {104} tableEntry(T, ":" sub 1, NT.105, Fail, "")
 , {105} tableEntry(NT.MatchAny.97, "Type" sub 1, Reduce.30, Fail, "")
 , {106} tableEntry(MatchAny, "?" sub 1, T.107, Success*, "")
 , {107} tableEntry(T, ": " sub 1, NT.108, Success*, "")
 , {108} tableEntry(NT.!T.109, "Str3" sub 1, Reduce*(31, MatchAny.106), Success*, "")
 , {109} tableEntry(!T, "}" sub 1, All, NT.110, "")
 , {110} tableEntry(NT.MatchAny.112, "C" sub 1, MatchAny.111, All, "")
 , {111} tableEntry(MatchAny, "?" sub 1, Discard*.!T.109, All, "")
 , {112} tableEntry(MatchAny, "?" sub 1, T.113, !Fail, "")
 , {113} tableEntry(T, ": " sub 1, !Reduce, !Fail, "")
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
else if place.a = {length of input} faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:thisresult) attribute
let t = result.top.stk.a,
t sub n.t

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
  if inputi ≠ match.te then {fail} next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then {fail} next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then {fail} next(stk, Fstate.te, i, inputi, result, faili, failresult)
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
