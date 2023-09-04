Module symbolMode

use seq.boolean

use mytype

use otherseq.mytype

use set.mytype

use standard

use symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use seq.word

Function symbolparse(input:seq.word, types:set.mytype, modname:modref) attribute
let r = parse(input, mytable, attribute(empty:seq.mytype, ""), commonType(types, isAbstract.modname, input))
assert status.r ∉ "Failed" ∧ (1_input ∈ "function Function" ∨ i.top.stk.r = n.input + 1)
report errormessage("Syntax error", input, i.top.stk.r),
result.r

function addpara(common:commonType, name:seq.word, typ:attribute, place:int) attribute
attribute([resolvetype(text.typ, common, place)], name)

function resolvetype(text:seq.word, common:commonType, place:int) mytype
let a = resolvetype(types.common, text)
assert not.isempty.a
report errormessage("cannot resolve type^(text)", input.common, place),
1_a

function errormessage(mess:seq.word, input:seq.word, place:int) seq.word
subseq(input, 1, place) + "<* literal^(mess) *>" + input << place

function toAttribute(a:attribute, s:seq.word) attribute attribute(empty:seq.mytype, s)

type attribute is types:seq.mytype, text:seq.word

Export types(attribute) seq.mytype

Export text(attribute) seq.word

function createfunc(
 common:commonType
 , place:int
 , funcname:seq.word
 , nametype:attribute
 , PL:attribute
 , functypebind:attribute
) attribute
let paralist = types.PL
let returntype = resolvetype(text.functypebind, common, place),
if not.isempty.text.nametype then
attribute(
 [resolvetype(text.nametype, common, place)] + paralist + returntype
 , funcname + text.nametype
)
else attribute(paralist + returntype, funcname)

function createtype(common:commonType, name:attribute, PL:attribute, place:int) attribute
let typename = resolvetype(if isAbstract.common then text.name + ".T" else text.name, common, place),
attribute([typename] + types.PL, text.PL)

function null attribute attribute(empty:seq.mytype, "")

function /Discard attribute null

function +(a:attribute, b:attribute) attribute
attribute(types.a + types.b, text.a + text.b)

type commonType is types:set.mytype, isAbstract:boolean, input:seq.word

function endMark word encodeword.[char.254]

function PEGgen(
 error:boolean
 , seqElementType:word
 , attributeType:attribute
 , R:reduction
 , place:int
 , common:commonType
) seq.boolean
[
 "match2code any" = 1_"/1"
 , "S type id is FPL Comment" = createtype(common, 1_R, 2_R, place)
 , "/ any Header" = 2_R
 , "Header id (FPL) Type Comment" = createfunc(common, place, text.1_R, null, 2_R, 3_R)
 , "/ id Type Comment" = createfunc(common, place, text.1_R, null, null, 2_R)
 , "/ id:Type (FPL) Type Comment"
  = createfunc(common, place, text.1_R, 2_R, 3_R, 4_R)
 , "/ id:Type Type Comment" = createfunc(common, place, text.1_R, 2_R, null, 3_R)
 , "FPL FP FPL'" = 1_R + 2_R
 , "* FPL', FP" = 0_R + 1_R
 , "FP any:Type" = addpara(common, text.1_R, 2_R, place)
 , "/ Type" = addpara(common, ":", 1_R, place)
 , "Type id.Type" = toAttribute(1_R, text.1_R + "." + text.2_R)
 , "/ id" = 1_R
 , "id !, !] ! {! (!) !:!. any" = 1_R
 , "* Comment {N}" = /Discard
 , "* N {N}" = /Discard
 , "/ str1" = /Discard
 , "* str1 ! {!} any" = /Discard
]

<<<< Below is auto generated code >>>>

/br Non-terminals:Comment FP FPL FPL' Header N S Type id str1
/br Terminals:(),.. :] any is type {}
/br S ← type id is FPL Comment / any Header
/br Header ← id (FPL) Type Comment / id Type Comment
/br / id:Type (FPL) Type Comment
/br / id:Type Type Comment
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br Type ← id.Type / id
/br id ← !, !] ! {! (!) !:!. any
/br * Comment ← {N}
/br * N ← {N} / str1
/br * str1 ← ! {!} any

function action(
 partno:int
 , R:reduction
 , place:int
 , input:seq.word
 , common:commonType
 , parsestk:stack.frame
) attribute
if partno = 2 then
createtype(common, 1_R, 2_R, place)
else if partno = 3 then
2_R
else if partno = 4 then
createfunc(common, place, text.1_R, null, 2_R, 3_R)
else if partno = 5 then
createfunc(common, place, text.1_R, null, null, 2_R)
else if partno = 6 then
createfunc(common, place, text.1_R, 2_R, 3_R, 4_R)
else if partno = 7 then
createfunc(common, place, text.1_R, 2_R, null, 3_R)
else if partno = 8 then
1_R + 2_R
else if partno = 9 then
0_R + 1_R
else if partno = 10 then
addpara(common, text.1_R, 2_R, place)
else if partno = 11 then
addpara(common, ":", 1_R, place)
else if partno = 12 then
toAttribute(1_R, text.1_R + "." + text.2_R)
else if partno = 13 then
1_R
else if partno = 14 then
1_R
else 0_R

function mytable seq.tableEntry
[
 {1} tableEntry(MatchNT.Match.2, 1_"?", Reduce.1, Reduce, "")
 , {2} tableEntry(Match, 1_"type", S.3, MatchAny.7, "")
 , {3} tableEntry(MatchNT.!Match.43, 1_"?", Match.4, MatchAny.7, "")
 , {4} tableEntry(Match, 1_"is", S.5, MatchAny.7, "")
 , {5} tableEntry(MatchNT.S.31, 1_"?", S.6, MatchAny.7, "")
 , {6} tableEntry(MatchNT.Match.51, 1_"?", Reduce.2, MatchAny.7, "")
 , {7} tableEntry(MatchAny, 1_"?", S.8, Fail, "")
 , {8} tableEntry(MatchNT.S.9, 1_"?", Reduce.3, Fail, "")
 , {9} tableEntry(MatchNT.!Match.43, 1_"?", MatchNext.10, S.15, "")
 , {10} tableEntry(MatchNext, 1_"(", S.11, S.16, "")
 , {11} tableEntry(MatchNT.S.31, 1_"?", MatchNext.12, S.28, "")
 , {12} tableEntry(MatchNext, 1_")", S.13, S.29, "")
 , {13} tableEntry(MatchNT.S.39, 1_"?", S.14, S.15, "")
 , {14} tableEntry(MatchNT.Match.51, 1_"?", Reduce.4, S.15, "")
 , {15} tableEntry(MatchNT.!Match.43, 1_"?", S.16, S.18, "")
 , {16} tableEntry(MatchNT.S.39, 1_"?", S.17, S.18, "")
 , {17} tableEntry(MatchNT.Match.51, 1_"?", Reduce.5, S.18, "")
 , {18} tableEntry(MatchNT.!Match.43, 1_"?", Match.19, S.26, "")
 , {19} tableEntry(Match, 1_":", S.20, S.26, "")
 , {20} tableEntry(MatchNT.S.39, 1_"?", Match.21, S.26, "")
 , {21} tableEntry(Match, 1_"(", S.22, S.26, "")
 , {22} tableEntry(MatchNT.S.31, 1_"?", Match.23, S.26, "")
 , {23} tableEntry(Match, 1_")", S.24, S.26, "")
 , {24} tableEntry(MatchNT.S.39, 1_"?", S.25, S.26, "")
 , {25} tableEntry(MatchNT.Match.51, 1_"?", Reduce.6, S.26, "")
 , {26} tableEntry(MatchNT.!Match.43, 1_"?", Match.27, Fail, "")
 , {27} tableEntry(Match, 1_":", S.28, Fail, "")
 , {28} tableEntry(MatchNT.S.39, 1_"?", S.29, Fail, "")
 , {29} tableEntry(MatchNT.S.39, 1_"?", S.30, Fail, "")
 , {30} tableEntry(MatchNT.Match.51, 1_"?", Reduce.7, Fail, "")
 , {31} tableEntry(MatchNT.MatchAny.35, 1_"?", S.32, Fail, "")
 , {32} tableEntry(MatchNT.Match.33, 1_"?", Reduce.8, Fail, "")
 , {33} tableEntry(Match, 1_",", S.34, Success*, "")
 , {34} tableEntry(MatchNT.MatchAny.35, 1_"?", Reduce(9, Match.33), Success*, "")
 , {35} tableEntry(MatchAny, 1_"?", Match.36, S.38, "")
 , {36} tableEntry(Match, 1_":", S.37, S.38, "")
 , {37} tableEntry(MatchNT.S.39, 1_"?", Reduce.10, S.38, "")
 , {38} tableEntry(MatchNT.S.39, 1_"?", Reduce.11, Fail, "")
 , {39} tableEntry(MatchNT.!Match.43, 1_"?", MatchNext.40, S.42, "")
 , {40} tableEntry(MatchNext, 1_".", S.41, Reduce.13, "")
 , {41} tableEntry(MatchNT.S.39, 1_"?", Reduce.12, S.42, "")
 , {42} tableEntry(MatchNT.!Match.43, 1_"?", Reduce.13, Fail, "")
 , {43} tableEntry(!Match, 1_",", Fail, !Match.44, "")
 , {44} tableEntry(!Match, 1_"]", Fail, !Match.45, "")
 , {45} tableEntry(!Match, 1_"{", Fail, !Match.46, "")
 , {46} tableEntry(!Match, 1_"(", Fail, !Match.47, "")
 , {47} tableEntry(!Match, 1_")", Fail, !Match.48, "")
 , {48} tableEntry(!Match, 1_":", Fail, !Match.49, "")
 , {49} tableEntry(!Match, 1_". ", Fail, MatchAny.50, "")
 , {50} tableEntry(MatchAny, 1_"?", Reduce.14, Fail, "")
 , {51} tableEntry(Match, 1_"{", S.52, SuccessDiscard*, "")
 , {52} tableEntry(MatchNT.Match.54, 1_"?", Match.53, SuccessDiscard*, "")
 , {53} tableEntry(Match, 1_"}", Discard*.Match.51, SuccessDiscard*, "")
 , {54} tableEntry(Match, 1_"{", S.55, S.57, "")
 , {55} tableEntry(MatchNT.Match.54, 1_"?", Match.56, S.57, "")
 , {56} tableEntry(Match, 1_"}", Discard*.Match.54, S.57, "")
 , {57} tableEntry(MatchNT.!Match.58, 1_"?", Discard*.Match.54, SuccessDiscard*, "")
 , {58} tableEntry(!Match, 1_"{", SuccessDiscard*, !Match.59, "")
 , {59} tableEntry(!Match, 1_"}", SuccessDiscard*, MatchAny.60, "")
 , {60} tableEntry(MatchAny, 1_"?", Discard*.!Match.58, SuccessDiscard*, "")
]

function =(seq.word, attribute) boolean true

function =(seq.word, word) boolean true

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.attribute

use PEGrules

function _(i:int, R:reduction) attribute (i + 1)_toseq.R

type reduction is toseq:seq.attribute

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.attribute
, faili:int
, failresult:seq.attribute

type runresultType is stk:stack.frame

Function status(a:runresultType) word
if Sstate.top.stk.a ≠ Reduce.1 then
1_"Failed"
else if i.top.stk.a = {length of input} faili.top.stk.a then
1_"Match"
else 1_"MatchPrefix"

Function result(a:runresultType) attribute 1^result.top.stk.a

function parse(
 myinput0:seq.word
 , table:seq.tableEntry
 , initAttr:attribute
 , common:commonType
) runresultType
let myinput = packed(myinput0 + endMark)
let packedTable = packed.table
for
 maxi = 0
 , maxStk = empty:stack.frame
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = 1_myinput
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while not(state = Reduce.1 ∨ state = Reduce.0)
do
 let actionState = action.state,
  if actionState = Fail then
   {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
   let top = top.stk
   let newstk = pop.stk,
   next(
    maxi
    , maxStk
    , newstk
    , if is!.Sstate.top then Sstate.top else Fstate.top
    , faili.top
    , idxNB(myinput, faili.top)
    , failresult.top
    , faili.top
    , failresult.top
   )
  else if actionState = Success* then
   {goto Sstate.top.stk, pop.stk, keep result}
   let top = top.stk,
   next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top + result, faili.top, failresult.top)
  else if actionState = SuccessDiscard* then
   {goto Sstate.top.stk, pop.stk, keep result}
   let top = top.stk,
   next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top, faili.top, failresult.top)
  else if actionState = Discard* then
   let top = top.stk,
    if faili = i then
    next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top, faili.top, failresult.top)
    else
     let newmaxStk = if i ≥ maxi then stk else maxStk,
     next(max(maxi, i), newmaxStk, stk, nextState.state, i, inputi, result.top, i, result.top)
  else if actionState = All then
   let top = top.stk
   let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Reduce then
   {Reduce}
   if nextState.state ≠ S.0 then
    let att = [action(reduceNo.state, reduction.result, i, myinput, common, stk)]
    let top = top.stk
    let newmaxStk = if i ≥ maxi then stk else maxStk,
     if faili = i then
     next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
     else next(max(i, maxi), newmaxStk, stk, nextState.state, i, inputi, att, i, att)
   else
    let top = top.stk,
     if is!.Sstate.top then
      {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
      let newstk = pop.stk
      let newi = faili.top
      let ini = idxNB(myinput, newi),
      next(maxi, maxStk, newstk, Fstate.top, newi, ini, failresult.top, faili.top, failresult.top)
     else
      let att = [action(reduceNo.state, reduction.result, i, myinput, common, stk)],
       if i ≥ maxi then
       next(i, stk, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
       else next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Match then
   let te = idxNB(packedTable, index.state),
    if inputi ≠ match.te then
     {fail}
     next(maxi, maxStk, stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(maxi, maxStk, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else if actionState = !Match then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
     {fail}
     next(maxi, maxStk, stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(maxi, maxStk, stk, Fstate.te, i, inputi, result, faili, failresult)
  else if actionState = MatchAny then
   let te = idxNB(packedTable, index.state),
    if inputi = endMark then
    {fail} next(maxi, maxStk, stk, Fstate.te, i, inputi, result, faili, failresult)
    else
     let reslt =
      if action.Sstate.te = Discard* then
      result
      else result + toAttribute(1^result, [inputi])
     let ini = idxNB(myinput, i + 1),
     next(maxi, maxStk, stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
  else if actionState = MatchNext then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
    next(maxi, maxStk, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
    else next(maxi, maxStk, stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   {match non Terminal}
   let te = idxNB(packedTable, index.state)
   assert action.action.te = MatchNT report "PROBLEM PEG^(state)"
   let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
   let tmp = [toAttribute(1^result, empty:seq.word)],
   next(maxi, maxStk, newstk, nextState.action.te, i, inputi, tmp, i, tmp),
runresultType.push(maxStk, frame(state, state, maxi, result, n.myinput, result)) 