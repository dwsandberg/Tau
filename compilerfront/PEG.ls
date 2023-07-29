Module PEG

use PEGmachine

use UTF8

use file

use otherseq.frame

use otherseq.int

use seq.int

use seq.seq.int

use seq.pegrule

use standard

use otherseq.tableEntry

use seq.seq.tableEntry

use textio

use otherseq.word

use otherseq.seq.word

use seq.seq.word

use seq.seq.seq.word

use set.word

type PEGtable is entries:seq.tableEntry, replacements:machine

Export type:PEGtable

Function maketable(gin:seq.pegrule) PEGtable PEGtable(makeTbl.gin, makeInterperter.gin)

Function maketable(s:seq.word) PEGtable
let gin = PEGgrammar.s
let old = "dq // //action //br"
let new = "^(dq) / /action
 /br",
PEGtable(postprocess(makeTbl.gin, old, new), postprocess(makeInterperter.gin, old, new))

Function %(t:PEGtable) seq.word %table.entries.t

Export +(seq.int, seq.int) seq.int {From seq.int}

function toother(a:seq.tableEntry) seq.tblEle
for acc = empty:seq.tblEle, e ∈ a
do acc + tblEle(action.e, tomatch.match.e, Sstate.e, Fstate.e),
acc

Function toAttribute(b:attribute, a:seq.word) attribute attribute(M.b, a)

Function tomatch(e:word) word e

Function run2(tab:PEGtable, input:seq.word) seq.word
let r = parse(input, toother.entries.tab, attribute(replacements.tab, "")),
if success.r ∧ i.top.stk.r = n.input + 1 then
%.result.r
else "Fail^(subseq(input, 1, i.top.stk.r - 1))"

Function run(tab:PEGtable, input:seq.word) seq.word
let r = parse(input, toother.entries.tab, attribute(replacements.tab, ""))
assert success.r ∧ i.top.stk.r = n.input + 1
report "fail^(subseq(input, 1, i.top.stk.r - 1))",
words.result.r

Function matchPrefix(tab:PEGtable, input:seq.word) seq.word
let r = parse(input, toother.entries.tab, attribute(replacements.tab, "")),
if not.success.r then "Fail^(result.r)" else subseq(input, 1, i.top.stk.r - 1)

function %(a:attribute) seq.word words.a

function %(f:frame) seq.word %.Sstate.f + "-" + %.faili.f

function action(
 partno:int
 , R:reduction
 , i:int
 , input:seq.word
 , common:int
 , parsestk:stack.frame
) attribute
for acc = empty:seq.seq.word, e ∈ toseq.R do acc + words.e,
attribute(M.0_R, runMachine(partno, M.0_R, acc, ""))

type attribute is M:machine, words:seq.word

function PEGgen(
 error:boolean
 , seqElementType:word
 , attributeType:attribute
 , runresultType:runresult
 , K:int
) int
0

<<<< Below is auto generated code >>>>

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

function parse(myinput:seq.word, table:seq.tblEle, initAttr:attribute) runresult
let packedTable = packed.table
let common = 0
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