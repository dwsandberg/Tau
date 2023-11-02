Module PEGdebug

use PEG

use PEGparse

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

Function PEGdebug(input:seq.file, steps:seq.word, notable:boolean) seq.word
{COMMAND doc Displays trace of running a PEG. 
/br-/strong input Expected first paragraph of input to be input and second paragraph to be the
grammar
/br-/strong steps /em from:/em to. Only display steps between /em from to /em to.
/br-/strong notable. Do not display parse table or grammar.}
let in = breakparagraph.input
assert n.in > 1
report "Expected first paragraph of input to be input and second paragraph to be the grammar"
let gin = adjust.PEGparse.2#in
let tab = maketable(gin, "dq^(dq), // /, //action /action, //br /br")
let inputtxt = 1#in
let start = if isempty.steps then 1 else toint.1#steps
let end = if n.steps < 2 then start + 999 else toint.1^steps
let r = parse(inputtxt, entries.tab, "", tab, start, end),
[status.r]
 + (if status.r ∈ "Failed" then subseq(inputtxt, 1, i.top.stk.r - 1) else result.r)
 + trace.r
 + if notable then "" else "/p PEG parse table^(tab) /p^(%(3, gin))"

Function toAttribute(b:seq.word, a:seq.word) seq.word a

function %(f:frame) seq.word %.Sstate.f + "-" + %.faili.f

function action(partno:int, R:seq.seq.word, common:PEGtable, pinfo:resultType) seq.word
runMachine(partno, common, R, "")

function endMark word encodeword.[char.254]

function PEGgen(
 error:boolean
 , seqElementType:word
 , attributeType:seq.word
 , common:PEGtable
 , trace:boolean
 , commonType:PEGtable
) int
{commonName = common nogrammar =}
0

<<<< Below is auto generated code >>>>

function $(int) seq.word 1#empty:seq.seq.word

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.seq.word

use PEGrules

function recoveryEnding(rinfo:resultType, mytable:seq.tableEntry) seq.word
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

type resultType is stk:stack.frame, input:seq.word, place:int, trace:seq.word

Function status(a:resultType) word
if Sstate.top.stk.a ≠ Match then
1#"Failed"
else if place.a = {length of input} faili.top.stk.a then
1#"Match"
else 1#"MatchPrefix"

Function result(a:resultType) seq.word 1^result.top.stk.a

function tracestart(trace:seq.word) seq.word
"
/br Key to column labels S--step no; D--Depth of Stack F--on fail reset I to F; I--
Location in input; Lower case are values on top of stack <* table
/row S /cell D /cell f /cell success /cell fail /cell result /cell Result /cell F /cell State /cell
I /cell Remaining input^(trace) *>"

function trace(
 stepno:int
 , trace0:seq.word
 , stk:stack.frame
 , result:seq.seq.word
 , faili:int
 , state:state
 , i:int
 , input:seq.word
) seq.word
let stkdata =
 %.n.toseq.stk
  + 
  if isempty.stk then
  "/cell /cell /cell /cell"
  else "/cell^(faili.top.stk) /cell^(Sstate.top.stk) /cell^(Fstate.top.stk) /cell
  ^(1^result.top.stk)",
trace0
 + "
/row^(stepno) /cell^(stkdata) /cell^(%("^", result) >> 1) /cell^(faili) /cell
^(state) /cell^(i) /cell^(subseq(input, i, min(i + 20, n.input - 1)))"

function parse(
 myinput0:seq.word
 , table:seq.tableEntry
 , initAttr:seq.word
 , common:PEGtable
 , startStep:int
 , endStep:int
) resultType
let myinput = packed(myinput0 + endMark)
let packedTable = packed.table
for
 stepno = 1
 , trace0 = ""
 , rinfo = resultType(empty:stack.frame, myinput, 0, "")
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = 1#myinput
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while toint.state > toint.Match ∧ stepno ≤ endStep
do
 let trace =
  if stepno < startStep then
  trace0
  else trace(stepno, trace0, stk, result, faili, state, i, myinput)
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
    else next(
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
   let newrinfo = if i > place.rinfo then resultType(stk, myinput, i, trace) else rinfo,
   next(stepno + 1, trace, newrinfo, stk, nextState.state, i, inputi, result.top, i, result.top)
  else if actionState = All then
   let top = top.stk
   let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
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
   let newrinfo = if i > place.rinfo then resultType(stk, myinput, i, trace) else rinfo
   let att = [action(reduceNo.state, result, common, newrinfo)],
   next(stepno + 1, trace, newrinfo, stk, nextState2.state, i, inputi, result + att, faili, failresult)
  else if actionState = Reduce then
   let top = top.stk
   let newrinfo = if i > place.rinfo then resultType(stk, myinput, i, trace) else rinfo
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
   let newrinfo = if i > place.rinfo then resultType(stk, myinput, i, trace) else rinfo
   let att = [action(reduceNo.state, result, common, newrinfo)]
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
   next(stepno + 1, trace, rinfo, pop.stk, Sstate.top, i.top, ini, result.top, faili.top, failresult.top)
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
    else next(
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
    {fail} next(stepno + 1, trace, rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
    else
     let reslt = result + toAttribute(1^result, [inputi])
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
   assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG^(state)"
   let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
   let tmp = [toAttribute(1^result, empty:seq.word)],
   next(stepno + 1, trace, rinfo, newstk, nextState.action.te, i, inputi, tmp, i, tmp),
resultType(
 push(stk.rinfo, frame(state, state, place.rinfo, result, n.myinput, result))
 , input.rinfo
 , place.rinfo
 , tracestart.trace0
) 