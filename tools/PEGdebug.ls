Module PEGdebug

use PEG

use PEGparse

use file

use seq1.frame

use seq1.int

use seq.pegrule

use standard

use seq.seq.tableEntry

use seq1.tableEntry

use textio

use seq.word

use seq.seq.word

use seq.seq.seq.word

use seq1.seq.word

use seq1.word

use set.word

Function PEGdebug(input:seq.file, steps:seq.word, notable:boolean) seq.word
{COMMAND /strong PEGdebug displays trace of running a PEG. 
/br-/strong input Expected first paragraph of input to be input and second paragraph to be the grammar.
/br-/strong steps from to. Only display steps between from and to.
/br-/strong notable. Do not display parse table or grammar.}
let in = breakparagraph.input << 1
assert n.in > 1 report "Expected first paragraph of input to be input and second paragraph to be the grammar"
let gin = adjust.PEGparse.in sub 2
let tab =
 maketable(
  gin
  , "dq:(dq), // /, //action /action, //br
  /br"
  , true
 )
let inputtxt = in sub 1
let start = if isempty.steps then 1 else toint.steps sub 1
let end = if n.steps < 2 then start + 999 else toint.last.steps
let r = parse(inputtxt, entries.tab, "", tab, start, end),
[status.r]
 + (if status.r ∈ "Failed" then subseq(inputtxt, 1, i.top.stk.r - 1) + "RI (" + recoveryEnding(r, entries.tab) + ")"
else result.r)
 + trace.r
 + if notable then "" else "/p PEG parse table:(tab) /p:(%(3, gin))"

Function toAttribute(b:seq.word, a:seq.word) seq.word a

function %(f:frame) seq.word %.Sstate.f + "-" + %.faili.f

function action(partno:int, R:seq.seq.word, common:PEGtable, pinfo:recoverInfo) seq.word
runMachine(partno, common, R, "")

function endMark word encodeword.[char.254]

function genPEG(
error:boolean
, seqElementType:word
, attributeType:seq.word
, common:PEGtable
, trace:boolean
, commonType:PEGtable
, resultType:recoverInfo
, rinfo:recoverInfo
) int
{commonName: common nogrammar: }
0

<<<< Below is auto generated code >>>>

function $(int) seq.word empty:seq.seq.word sub 1

use standard

use seq.tableEntry

use seq1.frame

use stack.frame

use seq1.seq.word

use PEGrules

function recoveryEnding(rinfo:recoverInfo, mytable:seq.tableEntry) seq.word
for acc = "", frame ∈ reverse.toseq.stk.rinfo
do
 if action.Sstate.frame ∈ [T, T', NT] then acc + recover.mytable sub index.Sstate.frame
 else acc,
acc

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.seq.word
, faili:int
, failresult:seq.seq.word

type recoverInfo is
stk:stack.frame
, input:seq.word
, place:int
, faili:int
, trace:seq.word

Function status(a:recoverInfo) word
if Sstate.top.stk.a ≠ Match then 'Failed
else if place.a = {length of input} faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:recoverInfo) seq.word
let t = result.top.stk.a,
t sub n.t

function tracestart(trace:seq.word) seq.word
"Key to column labels S--step no; D--Depth of Stack F--on fail reset I to F; I--Location in input; Lower case are values on top of stack <* table
/row S /cell D /cell f /cell success /cell fail /cell result /cell Result /cell F /cell State /cell I /cell Remaining input:(trace) *>"

function trace(
stepno:int
, trace0:seq.word
, stk:stack.frame
, result:seq.seq.word
, faili:int
, state:state
, i:int
, input:seq.word
, recovery:seq.word
) seq.word
let stkdata =
 %.n.toseq.stk
  + if isempty.stk then "/cell /cell /cell /cell"
 else "/cell:(faili.top.stk) /cell:(Sstate.top.stk) /cell:(Fstate.top.stk) /cell:(last.result.top.stk)",
trace0
 + "/row:(stepno) /cell:(stkdata) /cell:(%("^", result) >> 1) /cell:(faili) /cell:(state) /cell:(i) /cell:(subseq(input, i, min(i + 20, n.input - 1))) /cell:(recovery)"

function parse(
myinput0:seq.word
, table:seq.tableEntry
, initAttr:seq.word
, common:PEGtable
, startStep:int
, endStep:int
) recoverInfo
let myinput = packed(myinput0 + endMark)
let packedTable = packed.table
for
 stepno = 1
 , trace0 = ""
 , rinfo = recoverInfo(empty:stack.frame, myinput, 0, 1, "")
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = myinput sub 1
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while toint.state > toint.Match ∧ stepno ≤ endStep
do
 let trace =
  if stepno < startStep then trace0
  else
   let tmp =
    if isempty.stk.rinfo then ""
    else ":(place.rinfo) /cell:(recoveryEnding(rinfo, table))",
   trace(stepno, trace0, stk, result, faili, state, i, myinput, tmp)
 let actionState = action.state,
 if actionState = Fail then
  {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
  let top = top.stk,
  if toint.action.Fstate.top ≥ toint.S' then
   let newi = i.top,
   next(
    stepno + 1
    , trace
    , rinfo
    , pop.stk
    , nextState.Fstate.top
    , newi
    , idxNB(myinput, newi)
    , result.top
    , faili.top
    , failresult.top
   )
  else
   next(
    stepno + 1
    , trace
    , rinfo
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
  next(
   stepno + 1
   , trace
   , rinfo
   , pop.stk
   , Sstate.top
   , i
   , inputi
   , result.top + result
   , faili.top
   , failresult.top
  )
 else if actionState = Discard* then
  let top = top.stk
  let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i, faili, trace) else rinfo,
  next(stepno + 1, trace, newrinfo, stk, nextState.state, i, inputi, result.top, i, result.top)
 else if actionState = All then
  let top = top.stk
  let att = [toAttribute(result sub n.result, subseq(myinput, i.top, i - 1))],
  next(
   stepno + 1
   , trace
   , rinfo
   , pop.stk
   , Sstate.top
   , i
   , inputi
   , result.top + att
   , faili.top
   , failresult.top
  )
 else if actionState = Lambda then
  let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i, faili, trace) else rinfo
  let att = [action(reduceNo.state, result, common, newrinfo)],
  next(
   stepno + 1
   , trace
   , newrinfo
   , stk
   , nextState2.state
   , i
   , inputi
   , result + att
   , faili
   , failresult
  )
 else if actionState = Reduce then
  let top = top.stk
  let newrinfo =
   if i > place.rinfo ∨ faili ≠ faili.rinfo then recoverInfo(stk, myinput, i, faili, trace)
   else rinfo,
  let att = [action(reduceNo.state, result, common, newrinfo)],
  next(
   stepno + 1
   , trace
   , newrinfo
   , pop.stk
   , Sstate.top
   , i
   , inputi
   , result.top + att
   , faili.top
   , failresult.top
  )
 else if actionState = Reduce* then
  let newrinfo =
   if i > place.rinfo ∨ faili ≠ faili.rinfo then recoverInfo(stk, myinput, i, faili, trace)
   else rinfo
  let att = [action(reduceNo.state, result, common, newrinfo)],
  let top = top.stk,
  next(stepno + 1, trace, newrinfo, stk, nextState.state, i, inputi, att, i, att)
 else if actionState = !Reduce then
  let top = top.stk
  let ini = idxNB(myinput, faili.top),
  next(
   stepno + 1
   , trace
   , rinfo
   , pop.stk
   , Fstate.top
   , faili.top
   , ini
   , failresult.top
   , faili.top
   , failresult.top
  )
 else if actionState = !Fail then
  let top = top.stk
  let ini = idxNB(myinput, i.top),
  next(
   stepno + 1
   , trace
   , rinfo
   , pop.stk
   , Sstate.top
   , i.top
   , ini
   , result.top
   , faili.top
   , failresult.top
  )
 else if actionState = T then
  let te = idxNB(packedTable, index.state),
  if inputi ≠ match.te then
   {fail}
   next(
    stepno + 1
    , trace
    , rinfo
    , stk
    , Fstate.te
    , faili
    , idxNB(myinput, faili)
    , failresult
    , faili
    , failresult
   )
  else
   next(
    stepno + 1
    , trace
    , rinfo
    , stk
    , Sstate.te
    , i + 1
    , idxNB(myinput, i + 1)
    , result
    , faili
    , failresult
   )
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then
   {fail}
   next(
    stepno + 1
    , trace
    , rinfo
    , stk
    , Sstate.te
    , faili
    , idxNB(myinput, faili)
    , failresult
    , faili
    , failresult
   )
  else next(stepno + 1, trace, rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then
   {fail}
   next(stepno + 1, trace, rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(result sub n.result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(stepno + 1, trace, rinfo, stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then
   next(
    stepno + 1
    , trace
    , rinfo
    , stk
    , Sstate.te
    , i + 1
    , idxNB(myinput, i + 1)
    , result
    , faili
    , failresult
   )
  else next(stepno + 1, trace, rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG:(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(result sub n.result, empty:seq.word)],
  next(stepno + 1, trace, rinfo, newstk, nextState.action.te, i, inputi, tmp, i, tmp),
recoverInfo(
 push(stk.rinfo, frame(state, state, place.rinfo, result, n.myinput, result))
 , input.rinfo
 , place.rinfo
 , faili.rinfo
 , tracestart.trace0
) 
