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

use seq.word

use otherseq.seq.word

use seq.seq.word

use seq.seq.seq.word

use set.word

type PEGtable is entries:seq.tableEntry, replacements:machine

Export type:PEGtable

Function maketable(gin:seq.pegrule) PEGtable
PEGtable(makeTbl(gin, false), makeInterperter.gin)

Function maketable(s:seq.word) PEGtable
let gin = PEGgrammar.s
let old = "dq // //action //br"
let new = "^(dq) / /action /br",
PEGtable(postprocess(makeTbl(gin, false), old, new), postprocess(makeInterperter.gin, old, new))

Function %(t:PEGtable) seq.word %table.entries.t

Export +(seq.int, seq.int) seq.int {From seq.int}

Function toAttribute(b:seq.word, a:seq.word) seq.word a

Function run(tab:PEGtable, input:seq.word) seq.word
{First word of result will be status word of Match, MatchPrefix or Failed}
let r = parse(input, entries.tab, "", replacements.tab),
[status.r]
 + if status.r ∈ "Failed" then subseq(input, 1, i.top.stk.r - 1) else result.r

function action(
 partno:int
 , R:reduction
 , place:int
 , input:seq.word
 , common:machine
 , parsestk:stack.frame
) seq.word
for acc = empty:seq.seq.word, e ∈ toseq.R do acc + e,
runMachine(partno, common, acc, "")

function endMark word encodeword.[char.254]

function PEGgen(
 error:boolean
 , seqElementType:word
 , attributeType:seq.word
 , runresultType:runresult
 , common:machine
) int
0

<<<< Below is auto generated code >>>>

function =(seq.word, word) boolean true

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.seq.word

use PEGrules

function _(i:int, R:reduction) seq.word (i + 1)_toseq.R

type reduction is toseq:seq.seq.word

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.seq.word
, faili:int
, failresult:seq.seq.word

type runresult is stk:stack.frame

Function status(a:runresult) word
if Sstate.top.stk.a ≠ Reduce.1 then
1_"Failed"
else if i.top.stk.a = {length of input} faili.top.stk.a then
1_"Match"
else 1_"MatchPrefix"

Function result(a:runresult) seq.word 1^result.top.stk.a

function parse(
 myinput0:seq.word
 , table:seq.tableEntry
 , initAttr:seq.word
 , common:machine
) runresult
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
runresult.push(maxStk, frame(state, state, maxi, result, n.myinput, result)) 