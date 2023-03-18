Module PEGnew

use UTF8

use file

use otherseq.int

use seq.int

use seq.seq.int

use standard

use otherseq.tableEntry

use seq.seq.tableEntry

use textio

use otherseq.word

use otherseq.seq.word

use seq.seq.word

use seq.seq.seq.word

use set.word

use seq.pegrule

type PEGtable is entries:seq.tableEntry, replacements:machine

Export type:PEGtable


Function maketable(s:seq.word) PEGtable maketable.PEGgrammar.s

Function maketable(gin:seq.pegrule) PEGtable
PEGtable(makeTbl.gin, makeInterperter.gin)

Function %(t:PEGtable) seq.word %table.entries.t

Export +(seq.int, seq.int) seq.int

function toother(a:seq.tableEntry) seq.tblEle
for acc = empty:seq.tblEle, e ∈ a do
 acc + tblEle(action.e, tomatch.match.e, Sstate.e, Fstate.e)
/do acc


Function initializeAttribute seq.word ""

Function addany(result:seq.seq.word, w:word) seq.seq.word result + [w]

Function tomatch(e:word) word e

Function run2(tab:PEGtable, input:seq.word) seq.word
let r = parse(input ,replacements.tab,toother.entries.tab
,initializeAttribute)
,
if  success.r  then 
 %.result.r else "Fail"

Function run(tab:PEGtable, input:seq.word) seq.word
let r = parse(input ,replacements.tab,toother.entries.tab
,initializeAttribute)
,
assert success.r report "fail"  
 %.result.r

if success.r then {"success"+%(length.input-maxlength.r)+} %.result.r  else "fail" + trace.r

function action(top:frame,partno:int
 , R:reduction
   , i:int
 , faili:int
 , input:staticType) seq.word
 let t=if not.isempty.result.top then last.result.top else "" 
 runMachine(partno,replacements.input, toseq.R,t)
 
<<<< Below is auto generated code >>>>

use standard

use seq.tblEle

use otherseq.frame

use stack.frame

use otherseq.seq.word

use PEGrules

function parse(myinput:seq.word, replacements:machine, table:seq.tblEle, initAttr:seq.word) runresult
next(staticType(myinput,replacements)
 , packed.table
 , empty:stack.frame
 , startstate
 , 1
 , [initAttr]
 , 1
 , [initAttr])

function _(R:reduction, i:int) seq.word (toseq.R)_(i + 1)

type staticType is input:seq.word, replacements:machine

function length(s:staticType) int length.input.s

function _(s:staticType, i:int) word (input.s)_i

type tblEle is action:state, match:word, Sstate:state, Fstate:state

type reduction is toseq:seq.seq.word

type frame is Sstate:state
 , Fstate:state
 , i:int
 , result:seq.seq.word
 , faili:int
 , failresult:seq.seq.word

type runresult is maxlength:int, success:boolean, result:seq.word

Export maxlength(runresult) int

Export success(runresult) boolean

Export result(runresult) seq.word

function tracestart(trace:seq.word) seq.word
"<* table /row stk top.stk /cell top.stk /row depth S F /cell result /cell result /cell Fail / State /cell
 idx / remaining input $(trace) *>"

function trace(trace0:seq.word
 , stk:stack.frame
 , result:seq.seq.word
 , faili:int
 , state:state
 , i:int
 , input:staticType) seq.word
let stkdata = 
 %.length.toseq.stk
 + if isempty.stk then
  "/cell"
 else
  "$(faili.top.stk) $(Sstate.top.stk) $(Fstate.top.stk) /cell $(last.result.top.stk)"
,
trace0
+ "/row $(stkdata) /cell $(%("^", result) >> 1) /cell $(faili) $(state) /cell $(i)
 $(subseq(input.input, i, i + 20))"

function next(input:staticType
 , table:seq.tblEle
 , stk:stack.frame
 , state:state
 , i:int
 , result:seq.seq.word
 , faili:int
 , failresult:seq.seq.word) runresult
if state = Fail then
 {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
 let top = top.stk
 let newstk = pop.stk,
 if isempty.newstk then
  runresult(i, false, initializeAttribute)
 else
  next(input, table, newstk, Fstate.top, faili.top, result.top, faili.top, failresult.top)
else if state = Success* then
 {goto Sstate.top.stk, pop.stk, keep result}
 let top = top.stk,
 next(input, table, pop.stk, Sstate.top, i, result.top + result, faili.top, failresult.top)
else if state = Success*! then
 {goto Sstate.top, i = faili.tp, pop.stk, discard result}
 let top = top.stk,
 next(input
  , table
  , pop.stk
  , Sstate.top
  , faili
  , result.top + failresult
  , faili.top
  , failresult.top)
else if state = New! then
 {goto Sstate.top.stk, pop.stk, keep result}
 let top = top.stk,
 next(input, table, pop.stk, Sstate.top, faili.top, failresult.top, faili.top, failresult.top)
else if action.state = actionReduce then
 if index.state = 1 then
  runresult(i, true, last.result)
 else
  {actionReduce}
  let top = top.stk,
  let reduction = [action(top,index.state, reduction.result, i, faili, input)]
  next(input
   , table
   , pop.stk
   , Sstate.top
   , i
   , result.top + reduction
   , faili.top
   , failresult.top)
else
 let te = table_(index.state),
 if action.te = Match then
  if i > length.input ∨ input_i ≠ match.te then
   {fail} next(input, table, stk, Fstate.te, faili, failresult, faili, failresult)
  else
   next(input, table, stk, Sstate.te, i + 1, result, faili, failresult)
 else if action.te = !Match then
  if i ≤ length.input ∧ input_i = match.te then
   {fail} next(input, table, stk, Fstate.te, faili, failresult, faili, failresult)
  else
   next(input, table, stk, Sstate.te, i, result, faili, failresult)
 else if action.te = MatchAny then
  if i > length.input then
   {fail} next(input, table, stk, Fstate.te, i, result, faili, failresult)
  else
   next(input, table, stk, Sstate.te, i + 1, addany(result, input_i), faili, failresult)
 else if action.action.te = actionReduce then
  if index.action.te = 1 then
   runresult(i, true, last.result)
  else
   {actionReduce}
   let top = top.stk,
   let reduction = [action(top,index.action.te, reduction.result, i, faili, input)]
   if funny.Sstate.te ∨ faili = i then
    next(input
     , table
     , pop.stk
     , Sstate.top
     , i
     , result.top + reduction
     , faili.top
     , failresult.top)
   else
    next(input, table, stk, Sstate.te, i, reduction, i, reduction)
 else
  {match non Terminal}
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  next(input, table, newstk, action.te, i, [initializeAttribute], i, [initializeAttribute])

 