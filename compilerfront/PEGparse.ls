Module PEGparse

use PEGmachine

use PEGrules

use seq.attribute

use seq.pegpart

use seq.pegrule

use seq1.pegrule

use standard

use seq.word

use set.word

function endMark word encodeword.[char.254]

function toAttribute(a:seq.pegpart) attribute
attribute("", [pegrule("d" sub 1, "?" sub 1, a, 0, NT)])

function parts(a:attribute) seq.pegpart
if isempty.grammar.a then empty:seq.pegpart else parts.(grammar.a) sub 1

Function PEGparse(input:seq.word) seq.pegrule
{This grammar uses", dq"to find end of action since a rule such as <* block"Atom(E)"= let a = E, E2 *> has a comma in the middle of it. Note that this grammar would still not handle the case when E2 starts with a string literal.}
let r = parse(input, attribute("", empty:seq.pegrule))
assert status.r ∈ "Match" report
 let maxi = i.top.stk.r,
 red."Error in PEG grammar"
 + "/br:(subseq(input, 1, maxi - 1))/br Unparsed Input: :(subseq(input, maxi, maxi + 8))",
adjust.grammar.result.r

function rule(kind:seq.word, left:seq.word, parts:seq.pegpart) pegrule
pegrule(kind sub 1, left sub 1, parts, 0, NT)

function rule(left:seq.word, parts:seq.pegpart) pegrule
pegrule("d" sub 1, left sub 1, parts, 0, NT)

type attribute is str:seq.word, grammar:seq.pegrule

function toAttribute(a:attribute, b:seq.word) attribute attribute(b, empty:seq.pegrule)

function genPEG(
seqElementType:word
, attributeType:attribute
, resultType:thisresult
, place:int
) seq.boolean
{wordmap: K"/br
"sub 1, dq dq sub 1, //"/"sub 1, //action"/action"sub 1,"$"sub 1}
[
 "S[dq CodeFormat" = $.1
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
 , "/(Code N2)" = $.0
 , "/[Code N2]" = $.0
 , "/, ! dq" = $.0
 , "/ !, ! dq !(!)![!]any" = $.0
 , "* N2, Code" = $.0
]

<<<< Below is auto generated code >>>>

/br Non-terminals:Code Code' CodeFormat F1 N2 Part Part' Part2 Part2' S Str Str1 /br
Terminals:()*+, // //action = K[]any dq /br
S ←[dq CodeFormat / F1 /br
* F1 ← ! // * any Part Part' / ! //+any Part Part' / ! // any Part Part' /br
* Part' ← // Part / K /br
Part ← Str //action Str /br
* Str ← ! K ! // ! //action any /br
* CodeFormat ← * any Part2 Part2' /+any Part2 Part2' / any Part2 Part2' /br
* Part2' ← // Part2 /br
Part2 ← Str1 dq = Code', dq / Str1 dq = Code']/br
Code' ← Code /br
* Str1 ← ! dq any /br
* Code ← dq Str1 dq /(Code N2)/[Code N2]/, ! dq / !, ! dq !(!)![!]any /br
* N2 ←, Code

function action(partno:int, R:seq.attribute) attribute
if partno = 2 then R sub n.R
else if partno = 3 then R sub n.R
else if partno = 4 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
  + rule("*", str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 5 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
  + rule("+", str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 6 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
  + rule(str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 7 then toAttribute(parts.R sub (n.R - 1) + parts.R sub n.R)
else if partno = 8 then R sub n.R
else if partno = 9 then toAttribute.[pegpart(str.R sub (n.R - 1), str.R sub n.R)]
else if partno = 11 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
  + rule("*", str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 12 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
  + rule("+", str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 13 then
 attribute(
  ""
  , grammar.R sub (n.R - 3)
  + rule(str.R sub (n.R - 2), parts.R sub (n.R - 1) + parts.R sub n.R)
 )
else if partno = 14 then toAttribute(parts.R sub (n.R - 1) + parts.R sub n.R)
else if partno = 15 then toAttribute.[pegpart(str.R sub (n.R - 1), str.R sub n.R)]
else if partno = 16 then toAttribute.[pegpart(str.R sub (n.R - 1), str.R sub n.R)]
else if partno = 19 then R sub (n.R - 1)
else if partno = 20 then R sub (n.R - 2)
else if partno = 21 then R sub (n.R - 2)
else if partno = 22 then R sub n.R
else if partno = 23 then R sub (n.R - 1)
else if partno = 24 then R sub (n.R - 1)
else R sub 1

function mytable seq.tableEntry
[
 {1}tableEntry(NT.T'.2, "?" sub 1, Match, Failure, "")
 , {2}tableEntry(T', "[" sub 1, T.3, NT.5, "")
 , {3}tableEntry(T, dq sub 1, NT.4, NT.5, "")
 , {4}tableEntry(NT.T'.30, "CodeFormat" sub 1, Reduce.2, NT.5, "")
 , {5}tableEntry(NT.!T.6, "F1" sub 1, Reduce.3, Fail, "")
 , {6}tableEntry(!T, "/" sub 1, !T.11, T.7, "")
 , {7}tableEntry(T, "*" sub 1, MatchAny.8, !T.11, "")
 , {8}tableEntry(MatchAny, "?" sub 1, NT.9, !T.11, "")
 , {9}tableEntry(NT.23, "Part" sub 1, NT.10, !T.11, "")
 , {10}tableEntry(NT.T'.20, "Part'" sub 1, Reduce*(4, !T.6), !T.11, "")
 , {11}tableEntry(!T, "/" sub 1, !T.16, T.12, "")
 , {12}tableEntry(T, "+" sub 1, MatchAny.13, !T.16, "")
 , {13}tableEntry(MatchAny, "?" sub 1, NT.14, !T.16, "")
 , {14}tableEntry(NT.23, "Part" sub 1, NT.15, !T.16, "")
 , {15}tableEntry(NT.T'.20, "Part'" sub 1, Reduce*(5, !T.6), !T.16, "")
 , {16}tableEntry(!T, "/" sub 1, Success*, MatchAny.17, "")
 , {17}tableEntry(MatchAny, "?" sub 1, NT.18, Success*, "")
 , {18}tableEntry(NT.23, "Part" sub 1, NT.19, Success*, "")
 , {19}tableEntry(NT.T'.20, "Part'" sub 1, Reduce*(6, !T.6), Success*, "")
 , {20}tableEntry(T', "/" sub 1, NT.21, T.22, "")
 , {21}tableEntry(NT.23, "Part" sub 1, Reduce*(7, T'.20), T.22, "")
 , {22}tableEntry(T, "/br" sub 1, Reduce*(8, T'.20), Success*, "")
 , {23}tableEntry(NT.!T.26, "Str" sub 1, T.24, Fail, "")
 , {24}tableEntry(T, "/action" sub 1, NT.25, Fail, "")
 , {25}tableEntry(NT.!T.26, "Str" sub 1, Reduce.9, Fail, "")
 , {26}tableEntry(!T, "/br" sub 1, All, !T.27, "")
 , {27}tableEntry(!T, "/" sub 1, All, !T.28, "")
 , {28}tableEntry(!T, "/action" sub 1, All, MatchAny.29, "")
 , {29}tableEntry(MatchAny, "?" sub 1, Discard*.!T.26, All, "")
 , {30}tableEntry(T', "*" sub 1, MatchAny.31, T'.34, "")
 , {31}tableEntry(MatchAny, "?" sub 1, NT.32, T'.34, "")
 , {32}tableEntry(NT.43, "Part2" sub 1, NT.33, T'.34, "")
 , {33}tableEntry(NT.T.41, "Part2'" sub 1, Reduce*(11, T'.30), T'.34, "")
 , {34}tableEntry(T', "+" sub 1, MatchAny.35, MatchAny.38, "")
 , {35}tableEntry(MatchAny, "?" sub 1, NT.36, MatchAny.38, "")
 , {36}tableEntry(NT.43, "Part2" sub 1, NT.37, MatchAny.38, "")
 , {37}tableEntry(NT.T.41, "Part2'" sub 1, Reduce*(12, T'.30), MatchAny.38, "")
 , {38}tableEntry(MatchAny, "?" sub 1, NT.39, Success*, "")
 , {39}tableEntry(NT.43, "Part2" sub 1, NT.40, Success*, "")
 , {40}tableEntry(NT.T.41, "Part2'" sub 1, Reduce*(13, T'.30), Success*, "")
 , {41}tableEntry(T, "/" sub 1, NT.42, Success*, "")
 , {42}tableEntry(NT.43, "Part2" sub 1, Reduce*(14, T.41), Success*, "")
 , {43}tableEntry(NT.!T.55, "Str1" sub 1, T'.44, Fail, "")
 , {44}tableEntry(T', dq sub 1, T'.45, T.50, "")
 , {45}tableEntry(T', "=" sub 1, NT.46, Fail, "")
 , {46}tableEntry(NT.54, "Code'" sub 1, T'.47, Fail, "")
 , {47}tableEntry(T', "," sub 1, T.48, T.53, "")
 , {48}tableEntry(T, dq sub 1, Reduce.15, NT.49, "")
 , {49}tableEntry(NT.!T.55, "Str1" sub 1, T.50, Fail, "")
 , {50}tableEntry(T, dq sub 1, T.51, Fail, "")
 , {51}tableEntry(T, "=" sub 1, NT.52, Fail, "")
 , {52}tableEntry(NT.54, "Code'" sub 1, T.53, Fail, "")
 , {53}tableEntry(T, "]" sub 1, Reduce.16, Fail, "")
 , {54}tableEntry(NT.T'.57, "Code" sub 1, All, Fail, "")
 , {55}tableEntry(!T, dq sub 1, All, MatchAny.56, "")
 , {56}tableEntry(MatchAny, "?" sub 1, Discard*.!T.55, All, "")
 , {57}tableEntry(T', dq sub 1, NT.58, T'.60, "")
 , {58}tableEntry(NT.!T.55, "Str1" sub 1, T.59, T'.60, "")
 , {59}tableEntry(T, dq sub 1, Reduce*(19, T'.57), T'.60, "")
 , {60}tableEntry(T', "(" sub 1, NT.61, T'.64, "")
 , {61}tableEntry(NT.T'.57, "Code" sub 1, NT.62, T'.64, "")
 , {62}tableEntry(NT.T.77, "N2" sub 1, T.63, T'.64, "")
 , {63}tableEntry(T, ")" sub 1, Reduce*(20, T'.57), T'.64, "")
 , {64}tableEntry(T', "[" sub 1, NT.65, T.68, "")
 , {65}tableEntry(NT.T'.57, "Code" sub 1, NT.66, T.68, "")
 , {66}tableEntry(NT.T.77, "N2" sub 1, T.67, T.68, "")
 , {67}tableEntry(T, "]" sub 1, Reduce*(21, T'.57), T.68, "")
 , {68}tableEntry(T, "," sub 1, !T.69, !T.70, "")
 , {69}tableEntry(!T, dq sub 1, !T.70, Reduce*(22, T'.57), "")
 , {70}tableEntry(!T, "," sub 1, Success*, !T.71, "")
 , {71}tableEntry(!T, dq sub 1, Success*, !T.72, "")
 , {72}tableEntry(!T, "(" sub 1, Success*, !T.73, "")
 , {73}tableEntry(!T, ")" sub 1, Success*, !T.74, "")
 , {74}tableEntry(!T, "[" sub 1, Success*, !T.75, "")
 , {75}tableEntry(!T, "]" sub 1, Success*, MatchAny.76, "")
 , {76}tableEntry(MatchAny, "?" sub 1, Reduce*(23, T'.57), Success*, "")
 , {77}tableEntry(T, "," sub 1, NT.78, Success*, "")
 , {78}tableEntry(NT.T'.57, "Code" sub 1, Reduce*(24, T.77), Success*, "")
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
  if inputi ≠ match.te then{fail}next(stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then{fail}next(stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
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