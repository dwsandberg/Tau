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
let r = parse(input, attribute(empty:seq.mytype, ""), commonType(types, isAbstract.modname, input))
assert
 status.r ∉ "Failed"
  ∧ (1#input ∈ "function Function" ∨ i.top.stk.r = n.input + 1)
report errormessage("Syntax error", input, i.top.stk.r),
result.r

function addpara(common:commonType, name:seq.word, typ:attribute, place:int) attribute
attribute([resolvetype(text.typ, common, place)], name)

function resolvetype(text:seq.word, common:commonType, place:int) mytype
let a = resolvetype(types.common, text)
assert not.isempty.a
report errormessage("cannot resolve type^(text)", input.common, place),
1#a

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

function +(a:attribute, b:attribute) attribute
attribute(types.a + types.b, text.a + text.b)

type commonType is types:set.mytype, isAbstract:boolean, input:seq.word

function endMark word encodeword.[char.254]

function PEGgen(
 error:boolean
 , seqElementType:word
 , attributeType:attribute
 , resultType:recoverInfo
 , place:int
 , common:commonType
 , rinfo:recoverInfo
) seq.boolean
{commonName = common wordmap = 1 1#" 1", 1#" $"}
[
 "SymbolMode type Id is FPL Comment" = createtype(common, $.1, $.2, place.rinfo)
 , "/ any Header" = $.2
 , "Header Id (FPL) Type Comment" = createfunc(common, place.rinfo, text.$.1, null, $.2, $.3)
 , "/ Id Type Comment" = createfunc(common, place.rinfo, text.$.1, null, null, $.2)
 , "/ Id:Type (FPL) Type Comment" = createfunc(common, place.rinfo, text.$.1, $.2, $.3, $.4)
 , "/ Id:Type Type Comment" = createfunc(common, place.rinfo, text.$.1, $.2, null, $.3)
 , "FPL FP FPL'" = $.1 + $.2
 , "* FPL', FP" = $.0 + $.1
 , "FP any:Type" = addpara(common, text.$.1, $.2, place.rinfo)
 , "/ Type" = addpara(common, ":", $.1, place.rinfo)
 , "Type Id.Type" = toAttribute($.1, text.$.1 + "." + text.$.2)
 , "/ Id" = $.1
 , "Id !, !] ! {! (!) !:!. any" = $.1
 , "* Comment {N}" = $.0
 , "* N {N}" = $.0
 , "/ ! {!} any" = $.0
]

<<<< Below is auto generated code >>>>

/br Non-terminals:Comment FP FPL FPL' Header Id N SymbolMode Type
/br Terminals:(),.. :] any is type {}
/br SymbolMode ← type Id is FPL Comment / any Header
/br Header ← Id (FPL) Type Comment / Id Type Comment / Id:Type (FPL) Type Comment / Id:Type Type
Comment
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br Type ← Id.Type / Id
/br Id ← !, !] ! {! (!) !:!. any
/br * Comment ← {N}
/br * N ← {N} / ! {!} any

function action(
 partno:int
 , R:seq.attribute
 , common:commonType
 , rinfo:recoverInfo
) attribute
if partno = 2 then
createtype(common, 3^R, 2^R, place.rinfo)
else if partno = 3 then
1^R
else if partno = 4 then
createfunc(common, place.rinfo, text.4^R, null, 3^R, 2^R)
else if partno = 5 then
createfunc(common, place.rinfo, text.3^R, null, null, 2^R)
else if partno = 6 then
createfunc(common, place.rinfo, text.5^R, 4^R, 3^R, 2^R)
else if partno = 7 then
createfunc(common, place.rinfo, text.4^R, 3^R, null, 2^R)
else if partno = 8 then
2^R + 1^R
else if partno = 9 then
2^R + 1^R
else if partno = 10 then
addpara(common, text.2^R, 1^R, place.rinfo)
else if partno = 11 then
addpara(common, ":", 1^R, place.rinfo)
else if partno = 12 then
toAttribute(2^R, text.2^R + "." + text.1^R)
else if partno = 13 then
1^R
else if partno = 14 then
1^R
else if partno = 15 then
2^R
else if partno = 16 then
2^R
else if partno = 17 then
2^R
else 1#R

function mytable seq.tableEntry
[
 {1} tableEntry(NT.T'.2, 1#"?", Match, Failure, "")
 , {2} tableEntry(T', 1#"type", NT.3, MatchAny.7, "type any is any")
 , {3} tableEntry(NT.!T.43, 1#"Id", T.4, MatchAny.7, "any is any")
 , {4} tableEntry(T, 1#"is", NT.5, MatchAny.7, "is any")
 , {5} tableEntry(NT.31, 1#"FPL", NT.6, MatchAny.7, "any")
 , {6} tableEntry(NT.T.51, 1#"Comment", Reduce.2, MatchAny.7, "")
 , {7} tableEntry(MatchAny, 1#"?", NT.8, Fail, "any any:any any")
 , {8} tableEntry(NT.9, 1#"Header", Reduce.3, Fail, "any:any any")
 , {9} tableEntry(NT.!T.43, 1#"Id", T'.10, Fail, "any (any) any")
 , {10} tableEntry(T', 1#"(", NT.11, NT.16, "(any) any")
 , {11} tableEntry(NT.31, 1#"FPL", T.12, NT.15, "any) any")
 , {12} tableEntry(T, 1#")", NT.13, NT.15, ") any")
 , {13} tableEntry(NT.39, 1#"Type", NT.14, NT.15, "any")
 , {14} tableEntry(NT.T.51, 1#"Comment", Reduce.4, NT.15, "")
 , {15} tableEntry(NT.!T.43, 1#"Id", NT.16, Fail, "any any")
 , {16} tableEntry(NT.39, 1#"Type", NT.17, NT.18, "any")
 , {17} tableEntry(NT.T.51, 1#"Comment", Reduce.5, NT.18, "")
 , {18} tableEntry(NT.!T.43, 1#"Id", T'.19, Fail, "any:any (any) any")
 , {19} tableEntry(T', 1#":", NT.20, T.27, ":any (any) any")
 , {20} tableEntry(NT.39, 1#"Type", T'.21, Fail, "any (any) any")
 , {21} tableEntry(T', 1#"(", NT.22, NT.29, "(any) any")
 , {22} tableEntry(NT.31, 1#"FPL", T.23, NT.26, "any) any")
 , {23} tableEntry(T, 1#")", NT.24, NT.26, ") any")
 , {24} tableEntry(NT.39, 1#"Type", NT.25, NT.26, "any")
 , {25} tableEntry(NT.T.51, 1#"Comment", Reduce.6, NT.26, "")
 , {26} tableEntry(NT.!T.43, 1#"Id", T.27, Fail, "any:any any")
 , {27} tableEntry(T, 1#":", NT.28, Fail, ":any any")
 , {28} tableEntry(NT.39, 1#"Type", NT.29, Fail, "any any")
 , {29} tableEntry(NT.39, 1#"Type", NT.30, Fail, "any")
 , {30} tableEntry(NT.T.51, 1#"Comment", Reduce.7, Fail, "")
 , {31} tableEntry(NT.MatchAny.35, 1#"FP", NT.32, Fail, "any")
 , {32} tableEntry(NT.T.33, 1#"FPL'", Reduce.8, Fail, "")
 , {33} tableEntry(T, 1#",", NT.34, Success*, ", any")
 , {34} tableEntry(NT.MatchAny.35, 1#"FP", Reduce*(9, T.33), Success*, "any")
 , {35} tableEntry(MatchAny, 1#"?", T.36, NT.38, "any:any")
 , {36} tableEntry(T, 1#":", NT.37, NT.38, ":any")
 , {37} tableEntry(NT.39, 1#"Type", Reduce.10, NT.38, "any")
 , {38} tableEntry(NT.39, 1#"Type", Reduce.11, Fail, "any")
 , {39} tableEntry(NT.!T.43, 1#"Id", T.40, Fail, "any.any")
 , {40} tableEntry(T, 1#".", NT.41, NT.42, ".any")
 , {41} tableEntry(NT.39, 1#"Type", Reduce.12, NT.42, "any")
 , {42} tableEntry(NT.!T.43, 1#"Id", Reduce.13, Fail, "any")
 , {43} tableEntry(!T, 1#",", Fail, !T.44, ", any")
 , {44} tableEntry(!T, 1#"]", Fail, !T.45, "] any")
 , {45} tableEntry(!T, 1#"{", Fail, !T.46, "{any")
 , {46} tableEntry(!T, 1#"(", Fail, !T.47, "(any")
 , {47} tableEntry(!T, 1#")", Fail, !T.48, ") any")
 , {48} tableEntry(!T, 1#":", Fail, !T.49, ":any")
 , {49} tableEntry(!T, 1#". ", Fail, MatchAny.50, ". any")
 , {50} tableEntry(MatchAny, 1#"?", Reduce.14, Fail, "any")
 , {51} tableEntry(T, 1#"{", NT.52, Success*, "{}")
 , {52} tableEntry(NT.T.54, 1#"N", T.53, Success*, "}")
 , {53} tableEntry(T, 1#"}", Reduce*(15, T.51), Success*, "}")
 , {54} tableEntry(T, 1#"{", NT.55, !T.57, "{}")
 , {55} tableEntry(NT.T.54, 1#"N", T.56, !T.57, "}")
 , {56} tableEntry(T, 1#"}", Reduce*(16, T.54), !T.57, "}")
 , {57} tableEntry(!T, 1#"{", Success*, !T.58, "{any")
 , {58} tableEntry(!T, 1#"}", Success*, MatchAny.59, "} any")
 , {59} tableEntry(MatchAny, 1#"?", Reduce*(17, T.54), Success*, "any")
]

function =(seq.word, attribute) boolean true

function $(int) attribute 1#empty:seq.attribute

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.attribute

use PEGrules

function recoveryEnding(rinfo:recoverInfo) seq.word
for acc = "", frame ∈ reverse.toseq.pop.stk.rinfo
do
 if action.Sstate.frame ∈ [T, NT] then
 acc + recover.(index.Sstate.frame)#mytable
 else acc,
acc

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.attribute
, faili:int
, failresult:seq.attribute

type recoverInfo is stk:stack.frame, input:seq.word, place:int

Function status(a:recoverInfo) word
if Sstate.top.stk.a ≠ Match then
1#"Failed"
else if place.a = {length of input} faili.top.stk.a then
1#"Match"
else 1#"MatchPrefix"

Function result(a:recoverInfo) attribute 1^result.top.stk.a

function parse(myinput0:seq.word, initAttr:attribute, common:commonType) recoverInfo
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 rinfo = recoverInfo(empty:stack.frame, myinput, 0)
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = 1#myinput
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
      rinfo
      , pop.stk
      , nextState.Fstate.top
      , newi
      , idxNB(myinput, newi)
      , result.top
      , faili.top
      , failresult.top
     )
    else next(
     rinfo
     , pop.stk
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
   next(rinfo, pop.stk, Sstate.top, i, inputi, result.top + result, faili.top, failresult.top)
  else if actionState = Discard* then
   let top = top.stk
   let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i) else rinfo,
   next(newrinfo, stk, nextState.state, i, inputi, result.top, i, result.top)
  else if actionState = All then
   let top = top.stk
   let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(rinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Lambda then
   let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i) else rinfo
   let att = [action(reduceNo.state, result, common, newrinfo)],
   next(newrinfo, stk, nextState2.state, i, inputi, result + att, faili, failresult)
  else if actionState = Reduce then
   let top = top.stk
   let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i) else rinfo
   let att = [action(reduceNo.state, result, common, newrinfo)],
   next(newrinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Reduce* then
   let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i) else rinfo
   let att = [action(reduceNo.state, result, common, newrinfo)]
   let top = top.stk,
   next(newrinfo, stk, nextState.state, i, inputi, att, i, att)
  else if actionState = !Reduce then
   let top = top.stk
   let ini = idxNB(myinput, faili.top),
   next(rinfo, pop.stk, Fstate.top, faili.top, ini, failresult.top, faili.top, failresult.top)
  else if actionState = !Fail then
   let top = top.stk
   let ini = idxNB(myinput, i.top),
   next(rinfo, pop.stk, Sstate.top, i.top, ini, result.top, faili.top, failresult.top)
  else if actionState = T then
   let te = idxNB(packedTable, index.state),
    if inputi ≠ match.te then
    {fail} next(rinfo, stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(rinfo, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else if actionState = !T then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
    {fail} next(rinfo, stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
  else if actionState = MatchAny then
   let te = idxNB(packedTable, index.state),
    if inputi = endMark then
    {fail} next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
    else
     let reslt = result + toAttribute(1^result, [inputi])
     let ini = idxNB(myinput, i + 1),
     next(rinfo, stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
  else if actionState = T' then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
    next(rinfo, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
    else next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   {match non Terminal}
   let te = idxNB(packedTable, index.state)
   assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG^(state)"
   let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
   let tmp = [toAttribute(1^result, empty:seq.word)],
   next(rinfo, newstk, nextState.action.te, i, inputi, tmp, i, tmp),
recoverInfo(
 push(stk.rinfo, frame(state, state, place.rinfo, result, n.myinput, result))
 , input.rinfo
 , place.rinfo
) 