Module functionHeader

use PEG

use UTF8

use seq.headerType

use standard

use seq.word

use set.word

Export type:headerType

Export header(headerType) seq.word

Export modname(headerType) seq.word

type headerType is header:seq.word, modname:seq.word, isEntry:boolean, srcParagraphNo:int

Function getHeaders(src:seq.seq.word, cmd:boolean) seq.headerType
for acc = empty:seq.headerType, modname = "", mods = empty:set.word, parano = 1, p ∈ src
do
 let newacc =
  if 1#p ∈ "type" ∧ not.cmd then acc + headerType(p, modname, false, parano)
  else if 1#p ∈ "Function Export Builtin builtin" then
   let r0 = parse(p, "")
   assert status.r0 ∉ "Failed" report "Fail xx^(p)",
   let play = headerType(subseq(p, 1, place.r0 - 1), modname, subseq(result.r0, 1, 1) = "ENTRY", parano),
   if not.cmd ∨ isEntry.play then acc + play else acc
  else acc,
 if 1#p ∈ "Module module" then next(newacc, p << 1, mods + 2#p, parano + 1)
 else next(newacc, modname, mods, parano + 1),
acc

function table PEGtable
{Descriptions end at first linebreak or paragraph, beginning of new block, or end of the block.}
maketable."* Options /strong any Description Discard!Block <* block Values *> /action $.0 //br $.1 $.2 <* block $.4 *>
/br / /strong any Description /action $.0 //br $.1 $.2
/br / DiscardAll /action $.0
/br * Description ! //br !
/p ! /strong ! <* ! *> !} any /action $.0 $.1
/br * Values /strong Description /action $.0 //br $.1
/br / DiscardAll /action $.0
/br DiscardAll <* block N *> /action
/br / <* ! block N *> /action
/br / ! /strong ! <* ! *> !} any /action
/br * Discard!Block <* ! block N *> /action
/br / ! /strong ! <* ! *> !} any /action
/br * N <* N *> /action
/br / ! <* ! *> !} any /action"

Function returnType(e:headerType) seq.word
assert isEntry.e report "returnType restricted to entry points"
let returnTypeEnd = findindex(header.e, 1#"{") - 1,
subseq(
 header.e
 , if (returnTypeEnd - 1)#header.e ∈ "." then returnTypeEnd - 2 else returnTypeEnd
 , returnTypeEnd
)

function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Function cmddesc(e:headerType) seq.word
let i = findindex(header.e, 1#"COMMAND")
let j = findindex(header.e, 1#"(")
let params =
 %.2#header.e
  + ":"
  + returnType.e
  + ","
  + subseq(
  header.e
  , min(i, findindex(header.e, 1#"(")) + 1
  , min(i, findindex(header.e, 1#")")) - 1
 )
let kk = run(table, header.e << i) << 1
for acc3 = "", options = empty:set.word, last = 1#"?", nest = 0, w ∈ kk
do
 if w ∈ "<*" then next(acc3 + w, options, w, nest + 1)
 else if w ∈ "*>" then
  if subseq(acc3, n.acc3 - 1, n.acc3) = "<* block" then next(acc3 >> 2, options, w, nest - 1)
  else next(acc3 + w, options, w, nest - 1)
 else if last ∈ "/br" ∧ nest = 0 then
  let k = findindex(params, w) + 1
  let kind =
   tokind(
    if (k + 2)#params ∈ "." then subseq(params, k + 1, k + 3)
    else subseq(params, k + 1, k + 1)
   ),
  next(acc3 + kind + w, options + w, w, nest)
 else next(acc3 + w, options, w, nest)
for undoc = "", para ∈ break(params, ",", false)
do
 if 1#para ∈ options ∨ 1#para ∈ "xo input" then undoc
 else undoc + "/br^(tokind(para << 2))^(1#para) Undocumented",
acc3 + undoc

function tokind(typ:seq.word) word
findindex(["boolean", "seq.word", "seq.file"], typ)#"flag words files ??"

function toAttribute(b:seq.word, a:seq.word) seq.word a

function endMark word encodeword.[char.254]

function checkReturn(typ:seq.word) seq.word
if typ ∉ ["seq.word", "seq.file"] then "~ENTRY" else ""

function PEGgen(seqElementType:word, attributeType:seq.word) seq.boolean
{wordmap: 1#" $"}
[
 "S Export type:Type C" = ""
 , "/ Any Any F C"
 = (if $.1 = "Function" ∧ 1#"~ENTRY" ∉ $.3 ∧ 1#"COMMAND" ∈ $.4 then "ENTRY" else "")
 , "F (FPL) Type" = $.1 + checkReturn.$.2
 , "/:Type (FPL) Type" = $.2 + checkReturn.$.3
 , "/:Type Type" = checkReturn.$.2
 , "/ Type" = checkReturn.$.1
 , "FPL FP FPL'" = $.1 + $.2
 , "* FPL', FP" = $.0 + $.1
 , "FP any:Type"
 = (if $.2 ∉ ["boolean", "seq.word", "seq.file"] then "~ENTRY" else "")
 , "/ Type" = ""
 , "Type any.Type" = /All
 , "/ !, !) ! (! {any" = /All
 , "Kind Function" = ""
 , "C {N}" = $.1
 , "/" = ""
 , "* N {N}" = /All
 , "/ !} Any" = /All
]

<<<< Below is auto generated code >>>>

/br Unused non-terminals:Kind
/br Non-terminals:C F FP FPL FPL' Kind N S Type
/br Terminals:(),.:Any Export Function any type {}
/br S ← Export type:Type C / Any Any F C
/br F ← (FPL) Type /:Type (FPL) Type /:Type Type / Type
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br Type ← any.Type / !, !) ! (! {any
/br Kind ← Function
/br C ← {N} /
/br * N ← {N} / !} Any

function action(partno:int, R:seq.seq.word) seq.word
if partno = 2 then ""
else if partno = 3 then
 if 4^R = "Function" ∧ 1#"~ENTRY" ∉ 2^R ∧ 1#"COMMAND" ∈ 1^R then "ENTRY"
 else ""
else if partno /in  [4,5] then 2^R + checkReturn.1^R
else if partno /in[ 6,7] then checkReturn.1^R
 else if partno /in [8,9] then 2^R + 1^R
else if partno = 10 then if 1^R ∉ ["boolean", "seq.word", "seq.file"] then "~ENTRY" else ""
else if partno /in [11,14,16] then ""
 else if partno = 15 then 1^R
 else 1#R

function mytable seq.tableEntry
[
 {1} tableEntry(NT.T'.2, 1#"?", Match, Failure, "")
 , {2} tableEntry(T', 1#"Export", T.3, MatchAny.7, "")
 , {3} tableEntry(T, 1#"type", T.4, MatchAny.7, "")
 , {4} tableEntry(T, 1#":", NT.5, MatchAny.7, "")
 , {5} tableEntry(NT.MatchAny.33, 1#"Type", NT.6, MatchAny.7, "")
 , {6} tableEntry(NT.T.42, 1#"C", Reduce.2, MatchAny.7, "")
 , {7} tableEntry(MatchAny, 1#"?", MatchAny.8, Fail, "")
 , {8} tableEntry(MatchAny, 1#"?", NT.9, Fail, "")
 , {9} tableEntry(NT.T'.11, 1#"F", NT.10, Fail, "")
 , {10} tableEntry(NT.T.42, 1#"C", Reduce.3, Fail, "")
 , {11} tableEntry(T', 1#"(", NT.12, T'.15, "")
 , {12} tableEntry(NT.25, 1#"FPL", T.13, T'.15, "")
 , {13} tableEntry(T, 1#")", NT.14, T'.15, "")
 , {14} tableEntry(NT.MatchAny.33, 1#"Type", Reduce.4, T'.15, "")
 , {15} tableEntry(T', 1#":", NT.16, NT.24, "")
 , {16} tableEntry(NT.MatchAny.33, 1#"Type", T'.17, S'.NT.24, "")
 , {17} tableEntry(T', 1#"(", NT.18, NT.23, "")
 , {18} tableEntry(NT.25, 1#"FPL", T.19, T'.21, "")
 , {19} tableEntry(T, 1#")", NT.20, T'.21, "")
 , {20} tableEntry(NT.MatchAny.33, 1#"Type", Reduce.5, T'.21, "")
 , {21} tableEntry(T', 1#":", NT.22, NT.24, "")
 , {22} tableEntry(NT.MatchAny.33, 1#"Type", NT.23, NT.24, "")
 , {23} tableEntry(NT.MatchAny.33, 1#"Type", Reduce.6, NT.24, "")
 , {24} tableEntry(NT.MatchAny.33, 1#"Type", Reduce.7, Fail, "")
 , {25} tableEntry(NT.MatchAny.29, 1#"FP", NT.26, Fail, "")
 , {26} tableEntry(NT.T.27, 1#"FPL'", Reduce.8, Fail, "")
 , {27} tableEntry(T, 1#",", NT.28, Success*, "")
 , {28} tableEntry(NT.MatchAny.29, 1#"FP", Reduce*(9, T.27), Success*, "")
 , {29} tableEntry(MatchAny, 1#"?", T.30, NT.32, "")
 , {30} tableEntry(T, 1#":", NT.31, NT.32, "")
 , {31} tableEntry(NT.MatchAny.33, 1#"Type", Reduce.10, NT.32, "")
 , {32} tableEntry(NT.MatchAny.33, 1#"Type", Reduce.11, Fail, "")
 , {33} tableEntry(MatchAny, 1#"?", T.34, !T.36, "")
 , {34} tableEntry(T, 1#".", NT.35, !T.36, "")
 , {35} tableEntry(NT.MatchAny.33, 1#"Type", All, !T.36, "")
 , {36} tableEntry(!T, 1#",", Fail, !T.37, "")
 , {37} tableEntry(!T, 1#")", Fail, !T.38, "")
 , {38} tableEntry(!T, 1#"(", Fail, !T.39, "")
 , {39} tableEntry(!T, 1#"{", Fail, MatchAny.40, "")
 , {40} tableEntry(MatchAny, 1#"?", All, Fail, "")
 , {41} tableEntry(T, 1#"Function", Reduce.14, Fail, "")
 , {42} tableEntry(T, 1#"{", NT.43, Reduce.16, "")
 , {43} tableEntry(NT.T.45, 1#"N", T.44, Reduce.16, "")
 , {44} tableEntry(T, 1#"}", Reduce.15, Reduce.16, "")
 , {45} tableEntry(T, 1#"{", NT.46, !T.48, "")
 , {46} tableEntry(NT.T.45, 1#"N", T.47, !T.48, "")
 , {47} tableEntry(T, 1#"}", Discard*.T.45, !T.48, "")
 , {48} tableEntry(!T, 1#"}", All, MatchAny.49, "")
 , {49} tableEntry(MatchAny, 1#"?", Discard*.T.45, All, "")
]

function $(int) seq.word 1#empty:seq.seq.word

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.seq.word

use PEGrules

function place(r:resultType) int i.top.stk.r

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.seq.word
, faili:int
, failresult:seq.seq.word

type resultType is stk:stack.frame

Function status(a:resultType) word
if Sstate.top.stk.a ≠ Match then 1#"Failed"
else if place.a = {length of input} faili.top.stk.a then 1#"Match"
else 1#"MatchPrefix"

Function result(a:resultType) seq.word 1^result.top.stk.a

function parse(myinput0:seq.word, initAttr:seq.word) resultType
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 stk = empty:stack.frame
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
  let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
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
   let reslt = result + toAttribute(1^result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG^(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(1^result, empty:seq.word)],
  next(newstk, nextState.action.te, i, inputi, tmp, i, tmp),
resultType.push(stk, frame(state, state, i, result, n.myinput, result)) 