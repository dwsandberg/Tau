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

Function symbolparse(input:seq.word, types:set.mytype, modname:modref) attribute
let r = parse(input, mytable, attribute(empty:seq.mytype, ""), commonType(types, isAbstract.modname, input))
assert success.r ∧ (1_input ∈ "function Function" ∨ i.top.stk.r = n.input + 1)
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
 ,
  "/ id:Type (FPL) Type Comment"
  = createfunc(common, place, text.1_R, 2_R, 3_R, 4_R)
 , "/ id:Type Type Comment" = createfunc(common, place, text.1_R, 2_R, null, 3_R)
 , "FPL FP FPL'" = 1_R + 2_R
 , "* FPL', FP" = 0_R + 1_R
 , "FP any:Type" = addpara(common, text.1_R, 2_R, place)
 , "/ Type" = addpara(common, ":", 1_R, place)
 , "Type id.Type" = toAttribute(1_R, text.1_R + "." + text.2_R)
 , "/ id" = 1_R
 , "id !, !] ! {! (!) !:!. any" = 1_R
 , "* Comment C" = /Discard
 , "C {N}" = null
 , "* N C" = null
 , "/ str1" = null
 , "* str1 ! {!} any" = /Discard
]

<<<< Below is auto generated code >>>>

/br Non-termials:C Comment FP FPL FPL' Header N S Type id str1
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
/br * Comment ← C
/br C ← {N}
/br * N ← C / str1
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
else if partno = 16 then
null
else if partno = 17 then
null
else if partno = 18 then
null
else 0_R

function mytable seq.tblEle
[
 tblEle(S.2, 1_"S", Reduce.1, Fail)
 , tblEle(Match, 1_"type", S.3, S.7)
 , tblEle(S.44, 1_"id", S.4, S.7)
 , tblEle(Match, 1_"is", S.5, S.7)
 , tblEle(S.31, 1_"FPL", S.6, S.7)
 , tblEle(S.52, 1_"Comment", Reduce.2, S.7)
 , tblEle(MatchAny, 1_"any", S.8, Fail)
 , tblEle(S.9, 1_"Header", Reduce.3, Fail)
 , tblEle(S.44, 1_"id", S.10, S.15)
 , tblEle(MatchNext, 1_"(", S.11, S.16)
 , tblEle(S.31, 1_"FPL", S.12, S.15)
 , tblEle(Match, 1_")", S.13, S.15)
 , tblEle(S.40, 1_"Type", S.14, S.15)
 , tblEle(S.52, 1_"Comment", Reduce.4, S.15)
 , tblEle(S.44, 1_"id", S.16, S.18)
 , tblEle(S.40, 1_"Type", S.17, P.19)
 , tblEle(S.52, 1_"Comment", Reduce.5, S.18)
 , tblEle(S.44, 1_"id", S.19, S.26)
 , tblEle(MatchNext, 1_":", S.20, S.27)
 , tblEle(S.40, 1_"Type", S.21, P.28)
 , tblEle(MatchNext, 1_"(", S.22, S.29)
 , tblEle(S.31, 1_"FPL", S.23, S.26)
 , tblEle(Match, 1_")", S.24, S.26)
 , tblEle(S.40, 1_"Type", S.25, S.26)
 , tblEle(S.52, 1_"Comment", Reduce.6, S.26)
 , tblEle(S.44, 1_"id", S.27, Fail)
 , tblEle(Match, 1_":", S.28, Fail)
 , tblEle(S.40, 1_"Type", S.29, Fail)
 , tblEle(S.40, 1_"Type", S.30, Fail)
 , tblEle(S.52, 1_"Comment", Reduce.7, Fail)
 , tblEle(S.36, 1_"FP", S.32, Fail)
 , tblEle(S.33, 1_"FPL'", Reduce.8, Fail)
 , tblEle(Match, 1_",", S.34, Success*)
 , tblEle(S.36, 1_"FP", S.35, Success*)
 , tblEle(Reduce.9, 1_"?", S.33, S.0)
 , tblEle(MatchAny, 1_"any", S.37, S.39)
 , tblEle(Match, 1_":", S.38, S.39)
 , tblEle(S.40, 1_"Type", Reduce.10, S.39)
 , tblEle(S.40, 1_"Type", Reduce.11, Fail)
 , tblEle(S.44, 1_"id", S.41, S.43)
 , tblEle(MatchNext, 1_".", S.42, Reduce.13)
 , tblEle(S.40, 1_"Type", Reduce.12, S.43)
 , tblEle(S.44, 1_"id", Reduce.13, Fail)
 , tblEle(!Match, 1_",", S.45, Fail)
 , tblEle(!Match, 1_"]", S.46, Fail)
 , tblEle(!Match, 1_"{", S.47, Fail)
 , tblEle(!Match, 1_"(", S.48, Fail)
 , tblEle(!Match, 1_")", S.49, Fail)
 , tblEle(!Match, 1_":", S.50, Fail)
 , tblEle(!Match, 1_". ", S.51, Fail)
 , tblEle(MatchAny, 1_"any", Reduce.14, Fail)
 , tblEle(S.53, 1_"C", Discard*.52, Success*)
 , tblEle(Match, 1_"{", S.54, Fail)
 , tblEle(S.56, 1_"N", S.55, Fail)
 , tblEle(Match, 1_"}", Reduce.16, Fail)
 , tblEle(S.53, 1_"C", S.57, S.58)
 , tblEle(Reduce.17, 1_"?", S.56, S.0)
 , tblEle(S.60, 1_"str1", S.59, Success*)
 , tblEle(Reduce.18, 1_"?", S.56, S.0)
 , tblEle(!Match, 1_"{", S.61, Success*)
 , tblEle(!Match, 1_"}", S.62, Success*)
 , tblEle(MatchAny, 1_"any", Discard*.60, Success*)
]

function recoverTable seq.recoveryEntry
[
 recoveryEntry(Match, [1_"any", 1_"any", 1_":", 1_"any", 1_"any"], Reduce.1)
 , recoveryEntry(Match, [1_"type"], S.3)
 , recoveryEntry(Match, [1_"any"], S.4)
 , recoveryEntry(Match, [1_"is"], S.5)
 , recoveryEntry(Match, [1_"any"], S.6)
 , recoveryEntry(Match, "", Reduce.2)
 , recoveryEntry(Match, [1_"any"], S.8)
 , recoveryEntry(Match, [1_"any", 1_":", 1_"any", 1_"any"], Reduce.3)
 , recoveryEntry(Match, [1_"any"], S.10)
 , recoveryEntry(Match, [1_"("], S.11)
 , recoveryEntry(Match, [1_"any"], S.12)
 , recoveryEntry(Match, [1_")"], S.13)
 , recoveryEntry(Match, [1_"any"], S.14)
 , recoveryEntry(Match, "", Reduce.4)
 , recoveryEntry(Match, [1_"any"], S.16)
 , recoveryEntry(Match, [1_"any"], S.17)
 , recoveryEntry(Match, "", Reduce.5)
 , recoveryEntry(Match, [1_"any"], S.19)
 , recoveryEntry(Match, [1_":"], S.20)
 , recoveryEntry(Match, [1_"any"], S.21)
 , recoveryEntry(Match, [1_"("], S.22)
 , recoveryEntry(Match, [1_"any"], S.23)
 , recoveryEntry(Match, [1_")"], S.24)
 , recoveryEntry(Match, [1_"any"], S.25)
 , recoveryEntry(Match, "", Reduce.6)
 , recoveryEntry(Match, [1_"any"], S.27)
 , recoveryEntry(Match, [1_":"], S.28)
 , recoveryEntry(Match, [1_"any"], S.29)
 , recoveryEntry(Match, [1_"any"], S.30)
 , recoveryEntry(Match, "", Reduce.7)
 , recoveryEntry(Match, [1_"any"], S.32)
 , recoveryEntry(Match, "", Reduce.8)
 , recoveryEntry(Match, [1_","], S.34)
 , recoveryEntry(Match, [1_"any"], S.35)
 , recoveryEntry(Reduce.9, "", S.33)
 , recoveryEntry(Match, [1_"any"], S.37)
 , recoveryEntry(Match, [1_":"], S.38)
 , recoveryEntry(Match, [1_"any"], Reduce.10)
 , recoveryEntry(Match, [1_"any"], Reduce.11)
 , recoveryEntry(Match, [1_"any"], S.41)
 , recoveryEntry(Match, [1_"."], S.42)
 , recoveryEntry(Match, [1_"any"], Reduce.12)
 , recoveryEntry(Match, [1_"any"], Reduce.13)
 , recoveryEntry(!Match, "", S.45)
 , recoveryEntry(!Match, "", S.46)
 , recoveryEntry(!Match, "", S.47)
 , recoveryEntry(!Match, "", S.48)
 , recoveryEntry(!Match, "", S.49)
 , recoveryEntry(!Match, "", S.50)
 , recoveryEntry(!Match, "", S.51)
 , recoveryEntry(Match, [1_"any"], Reduce.14)
 , recoveryEntry(Match, [1_"{", 1_"}"], Discard*.52)
 , recoveryEntry(Match, [1_"{"], S.54)
 , recoveryEntry(Match, "", S.55)
 , recoveryEntry(Match, [1_"}"], Reduce.16)
 , recoveryEntry(Match, [1_"{", 1_"}"], S.57)
 , recoveryEntry(Reduce.17, "", S.56)
 , recoveryEntry(Match, "", S.59)
 , recoveryEntry(Reduce.18, "", S.56)
 , recoveryEntry(!Match, "", S.61)
 , recoveryEntry(!Match, "", S.62)
 , recoveryEntry(Match, [1_"any"], Discard*.60)
]

use seq.recoveryEntry

function recovery(state:state, stk:stack.frame, table:seq.recoveryEntry) seq.word
if isempty.stk then
""
else if action.state = S.0 then
 let te = (index.state)_table,
  if action.te = Match ∨ action.te = MatchNext ∨ action.te = MatchAny then
  match.te + recovery(Sstate.te, stk, table)
  else
   assert action.action.te = actionReduce report "Not handled 1^(action.te),",
   recovery(Sstate.top.stk, pop.stk, table)
else if action.state = actionReduce then
recovery(Sstate.top.stk, pop.stk, table)
else "Not handled 2^(state)"

function =(seq.word, attribute) boolean true

function =(seq.word, word) boolean true

use standard

use seq.tblEle

use otherseq.frame

use stack.frame

use otherseq.attribute

use PEGrules

function _(i:int, R:reduction) attribute (i + 1)_toseq.R

type tblEle is action:state, match:word, Sstate:state, Fstate:state

type reduction is toseq:seq.attribute

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.attribute
, faili:int
, failresult:seq.attribute

type runresult is stk:stack.frame

Function success(a:runresult) boolean Sstate.top.stk.a ≠ Fail

Function result(a:runresult) attribute 1^result.top.stk.a

function parse(
 myinput:seq.word
 , table:seq.tblEle
 , initAttr:attribute
 , common:commonType
) runresult
let packedTable = packed.table
for
 reduceLen = 0
 , maxStack = empty:stack.frame
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while not(
 index.state = 1 ∧ action.state = actionReduce
 ∨ action.state = Fail ∧ n.toseq.stk < 2
)
do
 let actionState = action.state,
  if actionState = Fail ∨ actionState = actionReduce ∧ not.isempty.stk ∧ is!.Sstate.top.stk then
   {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
   let top = top.stk
   let newstk = pop.stk,
    if action.Fstate.top = actionP then
    next(reduceLen, maxStack, newstk, S.index.Fstate.top, i.top, result.top, faili.top, failresult.top)
    else next(
     reduceLen
     , maxStack
     , newstk
     , if is!.Sstate.top ∧ state = Fail then Sstate.top else Fstate.top
     , faili.top
     , failresult.top
     , faili.top
     , failresult.top
    )
  else if actionState = Success* then
   {goto Sstate.top.stk, pop.stk, keep result}
   let top = top.stk,
   next(reduceLen, maxStack, pop.stk, Sstate.top, i, result.top + result, faili.top, failresult.top)
  else if actionState = actionDiscard* then
  next(reduceLen, maxStack, stk, S.index.state, i, result, i, result)
  else if actionState = All then
   let top = top.stk
   let reduction = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(reduceLen, maxStack, pop.stk, Sstate.top, i, result.top + reduction, faili.top, failresult.top)
  else if actionState = actionReduce then
   {actionReduce}
   let top = top.stk,
    if i ≥ reduceLen then
     let reduction = [action(index.state, reduction.result, i, myinput, common, stk)],
     next(
      {reduceLen} i
      , {maxStack} stk
      , pop.stk
      , Sstate.top
      , i
      , result.top + reduction
      , faili.top
      , failresult.top
     )
    else
     let reduction = [action(index.state, reduction.result,-reduceLen, myinput, common, maxStack)],
     next(reduceLen, maxStack, pop.stk, Sstate.top, i, result.top + reduction, faili.top, failresult.top)
  else
   let iz = index.state
   let te = idxNB(packedTable, iz)
   let actionTe = action.action.te,
    if actionTe = S.0 then
     {match non Terminal}
     let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
     let tmp = [toAttribute(1^result, empty:seq.word)],
     next(reduceLen, maxStack, newstk, action.te, i, tmp, i, tmp)
    else if actionTe = actionReduce then
     let reduction = [action(index.action.te, reduction.result, i, myinput, common, stk)]
     let top = top.stk
     let newreducelen = if i ≥ reduceLen then i else reduceLen
     let newMaxStack = if i ≥ reduceLen then stk else maxStack,
      if faili = i then
      next(
       newreducelen
       , newMaxStack
       , pop.stk
       , Sstate.top
       , i
       , result.top + reduction
       , faili.top
       , failresult.top
      )
      else next(newreducelen, newMaxStack, stk, Sstate.te, i, reduction, i, reduction)
    else if actionTe = Match then
     if i > n.myinput ∨ i_myinput ≠ match.te then
     {fail} next(reduceLen, maxStack, stk, Fstate.te, faili, failresult, faili, failresult)
     else next(reduceLen, maxStack, stk, Sstate.te, i + 1, result, faili, failresult)
    else if actionTe = MatchNext then
     if i > n.myinput ∨ i_myinput ≠ match.te then
     {fail} next(reduceLen, maxStack, stk, Fstate.te, i, result, faili, failresult)
     else next(reduceLen, maxStack, stk, Sstate.te, i + 1, result, faili, failresult)
    else if actionTe = !Match then
     if i ≤ n.myinput ∧ i_myinput = match.te then
     {fail} next(reduceLen, maxStack, stk, Fstate.te, faili, failresult, faili, failresult)
     else next(reduceLen, maxStack, stk, Sstate.te, i, result, faili, failresult)
    else
     assert actionTe = MatchAny report "PROBLEM PEG",
      if i > n.myinput then
      {fail} next(reduceLen, maxStack, stk, Fstate.te, i, result, faili, failresult)
      else
       let newresult =
        if action.Sstate.te = actionDiscard* then
        result
        else result + toAttribute(1^result, [i_myinput])
       ,
       next(reduceLen, maxStack, stk, Sstate.te, i + 1, newresult, faili, failresult)
,
runresult.push(maxStack, frame(state, state, reduceLen, result, i, result)) 