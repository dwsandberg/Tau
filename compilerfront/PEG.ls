Module PEG

use PEGmachine

use PEGparse

use UTF8

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

Export type:PEGtable

Function %(t:PEGtable) seq.word %table.entries.t

Export entries(PEGtable) seq.tableEntry

Export runMachine(int, PEGtable, seq.seq.word, seq.word) seq.word

Export maketable(gin:seq.pegrule, subs:seq.word) PEGtable

Export changeActions(gin:seq.pegrule, how:seq.word) seq.pegrule

Function maketable(s:seq.word) PEGtable
let gin = PEGparse.s,
maketable(gin, "dq^(dq), // /, //action /action, //br /br")

function toAttribute(b:seq.word, a:seq.word) seq.word a

Function run(tab:PEGtable, input:seq.word) seq.word
{First word of result will be status word of Match, MatchPrefix or Failed}
let r = parse(input, entries.tab, "", tab),
[status.r]
 + if status.r ∈ "Failed" then subseq(input, 1, i.top.stk.r - 1) else result.r

function action(partno:int, R:seq.seq.word, common:PEGtable, rinfo:runresult) seq.word
runMachine(partno, common, R, "")

function endMark word encodeword.[char.254]

function PEGgen(
 error:boolean
 , seqElementType:word
 , attributeType:seq.word
 , resultType:runresult
 , common:PEGtable
 , commonType:PEGtable
 , nogrammar:boolean
) int
{commonName = common}
0

<<<< Below is auto generated code >>>>

function $(int) seq.word 1#empty:seq.seq.word

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.seq.word

use PEGrules

function recoveryEnding(rinfo:runresult, mytable:seq.tableEntry) seq.word
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
, result:seq.seq.word
, faili:int
, failresult:seq.seq.word

type runresult is stk:stack.frame, input:seq.word, place:int

Function status(a:runresult) word
if Sstate.top.stk.a ≠ Match then
1#"Failed"
else if place.a = {length of input} faili.top.stk.a then
1#"Match"
else 1#"MatchPrefix"

Function result(a:runresult) seq.word 1^result.top.stk.a

function parse(
 myinput0:seq.word
 , table:seq.tableEntry
 , initAttr:seq.word
 , common:PEGtable
) runresult
let myinput = packed(myinput0 + endMark)
let packedTable = packed.table
for
 rinfo = runresult(empty:stack.frame, myinput, 0)
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
   let newrinfo = if i > place.rinfo then runresult(stk, myinput, i) else rinfo,
   next(newrinfo, stk, nextState.state, i, inputi, result.top, i, result.top)
  else if actionState = All then
   let top = top.stk
   let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(rinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Lambda then
   let newrinfo = if i > place.rinfo then runresult(stk, myinput, i) else rinfo
   let att = [action(reduceNo.state, result, common, newrinfo)],
   next(newrinfo, stk, nextState2.state, i, inputi, result + att, faili, failresult)
  else if actionState = Reduce then
   let top = top.stk
   let newrinfo = if i > place.rinfo then runresult(stk, myinput, i) else rinfo
   let att = [action(reduceNo.state, result, common, newrinfo)],
   next(newrinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Reduce* then
   let newrinfo = if i > place.rinfo then runresult(stk, myinput, i) else rinfo
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
runresult(
 push(stk.rinfo, frame(state, state, place.rinfo, result, n.myinput, result))
 , input.rinfo
 , place.rinfo
) 