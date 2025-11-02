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
  if p sub 1 ∈ "type" ∧ not.cmd then acc + headerType(p, modname, false, parano)
  else if p sub 1 ∈ "Function Export Builtin builtin" then
   let r0 = parse(p, "")
   assert status.r0 ∉ "Failed" report
    "<* literal Syntax Error in header *>
    /br:(p)",
   let play = headerType(subseq(p, 1, place.r0 - 1), modname, subseq(result.r0, 1, 1) = "ENTRY", parano),
   if not.cmd ∨ isEntry.play then acc + play else acc
  else acc,
 if p sub 1 ∈ "Module module" then next(newacc, p << 1, mods + p sub 2, parano + 1)
 else next(newacc, modname, mods, parano + 1),
acc

function cmddescTable PEGtable
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
let returnTypeEnd = findindex(header.e, "{" sub 1) - 1,
subseq(
 header.e
 , if (header.e) sub (returnTypeEnd - 1) ∈ "." then returnTypeEnd - 2 else returnTypeEnd
 , returnTypeEnd
)

function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Function cmddesc(e:headerType) seq.word
let i = findindex(header.e, "COMMAND" sub 1)
let j = findindex(header.e, "(" sub 1)
let params =
 %.(header.e) sub 2
  + ":"
  + returnType.e
  + ","
  + subseq(
  header.e
  , min(i, findindex(header.e, "(" sub 1)) + 1
  , min(i, findindex(header.e, ")" sub 1)) - 1
 )
let kk = run(cmddescTable, header.e << i) << 1
for acc3 = "", options = empty:set.word, last = "?" sub 1, nest = 0, w ∈ kk
do
 if w ∈ "<*" then next(acc3 + w, options, w, nest + 1)
 else if w ∈ "*>" then
  if subseq(acc3, n.acc3 - 1, n.acc3) = "<* block" then next(acc3 >> 2, options, w, nest - 1)
  else next(acc3 + w, options, w, nest - 1)
 else if last ∈ "/br" ∧ nest = 0 then
  let k = findindex(params, w) + 1
  let kind =
   tokind(
    if params sub (k + 2) ∈ "." then subseq(params, k + 1, k + 3)
    else subseq(params, k + 1, k + 1)
   ),
  next(acc3 + kind + w, options + w, w, nest)
 else next(acc3 + w, options, w, nest)
for undoc = "", para ∈ break(params, ",", false)
do
 if para sub 1 ∈ options ∨ para sub 1 ∈ "xo input" then undoc
 else undoc + "/br:(tokind(para << 2)):(para sub 1) Undocumented",
acc3 + undoc

function tokind(typ:seq.word) word
"flag words files ??" sub findindex(["boolean", "seq.word", "seq.file"], typ)

function toAttribute(b:seq.word, a:seq.word) seq.word a

function endMark word encodeword.[char.254]

function checkReturn(typ:seq.word) seq.word
{OPTION NOINLINE}
if typ ∉ ["seq.word", "seq.byte", "seq.UTF8", "seq.file"] then "~ENTRY"
else ""

function genPEG(seqElementType:word, attributeType:seq.word) seq.boolean
{wordmap: " $" sub 1}
[
 "S Export type:Type C" = ""
 , "/ Any Any F C"
 = (if $.1 = "Function" ∧ "~ENTRY" sub 1 ∉ $.3 ∧ "COMMAND" sub 1 ∈ $.4 then "ENTRY"
 else "")
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
 , "C {N}" = $.1
 , "/" = ""
 , "* N {N}" = /All
 , "/ !} Any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-terminals:C F FP FPL FPL' N S Type
/br Terminals:(),.:Any Export any type {}
/br S ← Export type:Type C / Any Any F C
/br F ← (FPL) Type /:Type (FPL) Type /:Type Type / Type
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br Type ← any.Type / !, !) ! (! {any
/br C ← {N} /
/br * N ← {N} / !} Any

function action(partno:int, R:seq.seq.word) seq.word
if partno = 2 then ""
else if partno = 3 then
 if R sub (n.R - 3) = "Function"
 ∧ "~ENTRY" sub 1 ∉ R sub (n.R - 1)
 ∧ "COMMAND" sub 1 ∈ R sub n.R then "ENTRY"
 else ""
else if partno = 4 then R sub (n.R - 1) + checkReturn.R sub n.R
else if partno = 5 then R sub (n.R - 1) + checkReturn.R sub n.R
else if partno = 6 then checkReturn.R sub n.R
else if partno = 7 then checkReturn.R sub n.R
else if partno = 8 then R sub (n.R - 1) + R sub n.R
else if partno = 9 then R sub (n.R - 1) + R sub n.R
else if partno = 10 then if R sub n.R ∉ ["boolean", "seq.word", "seq.file"] then "~ENTRY" else ""
else if partno = 11 then ""
else if partno = 14 then R sub n.R
else if partno = 15 then ""
else R sub 1

function mytable seq.tableEntry
[
 {1} tableEntry(NT.T'.2, "?" sub 1, Match, Failure, "")
 , {2} tableEntry(T', "Export" sub 1, T.3, MatchAny.7, "")
 , {3} tableEntry(T, "type" sub 1, T.4, MatchAny.7, "")
 , {4} tableEntry(T, ":" sub 1, NT.5, MatchAny.7, "")
 , {5} tableEntry(NT.MatchAny.33, "Type" sub 1, NT.6, MatchAny.7, "")
 , {6} tableEntry(NT.T.41, "C" sub 1, Reduce.2, MatchAny.7, "")
 , {7} tableEntry(MatchAny, "?" sub 1, MatchAny.8, Fail, "")
 , {8} tableEntry(MatchAny, "?" sub 1, NT.9, Fail, "")
 , {9} tableEntry(NT.T'.11, "F" sub 1, NT.10, Fail, "")
 , {10} tableEntry(NT.T.41, "C" sub 1, Reduce.3, Fail, "")
 , {11} tableEntry(T', "(" sub 1, NT.12, T'.15, "")
 , {12} tableEntry(NT.25, "FPL" sub 1, T.13, T'.15, "")
 , {13} tableEntry(T, ")" sub 1, NT.14, T'.15, "")
 , {14} tableEntry(NT.MatchAny.33, "Type" sub 1, Reduce.4, T'.15, "")
 , {15} tableEntry(T', ":" sub 1, NT.16, NT.24, "")
 , {16} tableEntry(NT.MatchAny.33, "Type" sub 1, T'.17, S'.NT.24, "")
 , {17} tableEntry(T', "(" sub 1, NT.18, NT.23, "")
 , {18} tableEntry(NT.25, "FPL" sub 1, T.19, T'.21, "")
 , {19} tableEntry(T, ")" sub 1, NT.20, T'.21, "")
 , {20} tableEntry(NT.MatchAny.33, "Type" sub 1, Reduce.5, T'.21, "")
 , {21} tableEntry(T', ":" sub 1, NT.22, NT.24, "")
 , {22} tableEntry(NT.MatchAny.33, "Type" sub 1, NT.23, NT.24, "")
 , {23} tableEntry(NT.MatchAny.33, "Type" sub 1, Reduce.6, NT.24, "")
 , {24} tableEntry(NT.MatchAny.33, "Type" sub 1, Reduce.7, Fail, "")
 , {25} tableEntry(NT.MatchAny.29, "FP" sub 1, NT.26, Fail, "")
 , {26} tableEntry(NT.T.27, "FPL'" sub 1, Reduce.8, Fail, "")
 , {27} tableEntry(T, "," sub 1, NT.28, Success*, "")
 , {28} tableEntry(NT.MatchAny.29, "FP" sub 1, Reduce*(9, T.27), Success*, "")
 , {29} tableEntry(MatchAny, "?" sub 1, T.30, NT.32, "")
 , {30} tableEntry(T, ":" sub 1, NT.31, NT.32, "")
 , {31} tableEntry(NT.MatchAny.33, "Type" sub 1, Reduce.10, NT.32, "")
 , {32} tableEntry(NT.MatchAny.33, "Type" sub 1, Reduce.11, Fail, "")
 , {33} tableEntry(MatchAny, "?" sub 1, T.34, !T.36, "")
 , {34} tableEntry(T, "." sub 1, NT.35, !T.36, "")
 , {35} tableEntry(NT.MatchAny.33, "Type" sub 1, All, !T.36, "")
 , {36} tableEntry(!T, "," sub 1, Fail, !T.37, "")
 , {37} tableEntry(!T, ")" sub 1, Fail, !T.38, "")
 , {38} tableEntry(!T, "(" sub 1, Fail, !T.39, "")
 , {39} tableEntry(!T, "{" sub 1, Fail, MatchAny.40, "")
 , {40} tableEntry(MatchAny, "?" sub 1, All, Fail, "")
 , {41} tableEntry(T, "{" sub 1, NT.42, Reduce.15, "")
 , {42} tableEntry(NT.T.44, "N" sub 1, T.43, Reduce.15, "")
 , {43} tableEntry(T, "}" sub 1, Reduce.14, Reduce.15, "")
 , {44} tableEntry(T, "{" sub 1, NT.45, !T.47, "")
 , {45} tableEntry(NT.T.44, "N" sub 1, T.46, !T.47, "")
 , {46} tableEntry(T, "}" sub 1, Discard*.T.44, !T.47, "")
 , {47} tableEntry(!T, "}" sub 1, All, MatchAny.48, "")
 , {48} tableEntry(MatchAny, "?" sub 1, Discard*.T.44, All, "")
]

function $(int) seq.word empty:seq.seq.word sub 1

use standard

use seq.tableEntry

use seq1.frame

use stack.frame

use seq1.seq.word

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
if Sstate.top.stk.a ≠ Match then 'Failed
else if place.a = {length of input} faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:resultType) seq.word
let t = result.top.stk.a,
t sub n.t

function parse(myinput0:seq.word, initAttr:seq.word) resultType
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
resultType.push(stk, frame(state, state, i, result, n.myinput, result)) 
