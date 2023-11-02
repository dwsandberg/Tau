Module PEGgenNoTable

use PEGrules

use otherseq.int

use set.int

use standard

use seq.arc.state

use graph.state

use otherseq.state

use set.state

use seq.tableEntry

type convertInfo is
table:seq.tableEntry
, start:state
, newStates:set.state
, actions:seq.seq.word
, wordmap:seq.word

function cvt(a:convertInfo, s:seq.state) seq.int
for acc = empty:seq.int, e ∈ s do acc + cvt(a, e, 1),
acc

Function cvt(a:convertInfo, s:state, place:int) int
let kk = if s = start.a then 2 else findindex(newStates.a, s) + 2
assert kk > 1
report "FFF^(place)^(s) /br newStates:^(toseq.newStates.a)^(%table.table.a)",
kk

use set.arc.state

function normalize(s:state, table:seq.tableEntry) state
let tmp = action.action.(index.s)#table,
if tmp = NT then
NT.index.s
else if tmp = T' then
T'.index.s
else if tmp = NT then
NT.index.s
else if tmp = !T then
!T.index.s
else assert tmp = T report "DFDS" + %.tmp, T.index.s

function fixit(r:seq.word, noNT:int) seq.word
if n.r < 3 then
r
else
 let none = merge.".."
 for acc = "", l2 = none, l1 = none, e ∈ r + ".."
 do
  if l1 ∈ "." ∧ l2 ∈ "$" then
  next(acc + "(^(noNT - toint.e)^R)", none, none)
  else next(if l2 = none then acc else acc + l2, l1, e),
 acc

Function notable(grammar:seq.pegrule, table:seq.tableEntry, wordmap:seq.word) seq.seq.word
for begins = empty:set.state, actions = ["unused"], r ∈ grammar
do
 for actions1 = actions, count = 1, p ∈ parts.r
 do next(
  actions1
   + "{^(if kind.r ∈ "*+" then [kind.r] else "")^(leftside.r)^(count)}
  ^(fixit(replacement.p, NTcount(p, grammar) + 1))"
  , count + 1
 ),
 next(begins + normalize(begin.r, table), actions1)
for toprocess = begins, g = newgraph.empty:seq.arc.state
while not.isempty.toprocess
do
 for arcs = empty:seq.arc.state, i ∈ toseq.toprocess
 do
  let tmp = action.i,
   if tmp ∈ [Success*, Fail, Reduce, All] then
   arcs
   else if tmp ∈ [Reduce*, Discard*] then
   arcs + arc(i, nextState.i)
   else
    assert tmp ∈ [T, NT, T', S', !T, MatchAny] report "HHH^(i)"
    let te = (index.i)#table,
     arcs
      + arc(i, Sstate.te)
      + arc(i, Fstate.te)
      + (
      if action.action.te ∈ [NT, NT*] then
      [arc(i, nextState.action.te)]
      else empty:seq.arc.state
     )
      + 
      if action.Sstate.te ∈ [Discard*, Reduce*] then
      [arc(i, nextState.Sstate.te)]
      else empty:seq.arc.state
 let newg = g + arcs,
 next(nodes.newg \ (nodes.g ∪ toprocess), newg)
for stacked = empty:set.state, e ∈ table
do if action.action.e ∈ [NT, NT*] then stacked + Fstate.e + Sstate.e else stacked
let start = T'.2
for newStates = empty:set.state, e ∈ toseq.nodes.g
do
 let in = indegree(g, e),
  if in = 1 ∧ e ∉ stacked ∧ e ∉ begins ∨ in = 0 ∨ e = start then
  newStates
  else newStates + e
let info = convertInfo(table, start, newStates, actions, wordmap)
for code = "", j ∈ [start] + toseq.newStates
do
 code
  + (
  if j ≠ 1^toseq.newStates then
  "if state = {^(j)}^(cvt(info, j, 2)) then"
  else "assert state = {^(j)}^(cvt(info, j, 3)) report^(dq."???")"
 )
  + build(0, info, j, "stk", "i", "inputi", "result", "faili", "failini", "failresult")
  + "else",
[
 "/wordsAttribute /else function = (seq.word, attributeType) boolean true /end"
 , "function $ (int) attributeType 0#empty:seq.attributeType"
 , "type frame is Sstate:int, Fstate:int, i:int, result:seq.attributeType, faili:int,
 failini:seqElementType, failresult:seq.attributeType"
 , "type resultType is stk:stack.frame /trace, trace:seq.word /end"
 , "Function result (a:resultType) attributeType 1^result.top.stk.a"
 , "function parse (myinput0:seq.seqElementType, initAttr:attributeType /common, common:
 commonType /end) resultType
 /br let myinput = packed (myinput0+endMark)
 /br let initresult = [initAttr] let initstk = push (empty:stack.frame, frame (1, 0, 1,
 initresult, 1, 1#myinput, initresult))
 /br for /trace stepno = 1, trace0 =^(dq.""), /end stk = initstk, state = 2, i = 1, inputi = 1#myinput, result = initresult, faili = 1,
 failini = 1#myinput, failresult = initresult
 /br while state > toint.Match do /trace let trace = trace0 /end
 ^(code >> 1)
 /br resultType (push (stk, frame (state, state, i, result, n.myinput, inputi, result)
 ) /trace, trace0 /end)"
]

function replaceWords2(a:word, b:seq.word) seq.word
if a ∈ "break" then
"break"
else if a ∈ "ec" then
"escapeformat"
else let kk = replaceWords([a], b) assert not.isempty.kk report "KK", kk

function build(
 level:int
 , info:convertInfo
 , state:state
 , stk:seq.word
 , i:seq.word
 , inputi:seq.word
 , result:seq.word
 , faili:seq.word
 , failini:seq.word
 , failresult:seq.word
) seq.word
let next = "next (/trace stepno+1, trace, /end",
if level > 0 ∧ (state ∈ newStates.info ∨ state = start.info) then
"^(next)^(stk),^(cvt(info, state, 4)),^(i),^(inputi),^(result),^(faili),
^(failini),^(failresult))"
else if action.state = Fail then
"let top = top.stk, if Fstate.top /ge toint.S' then let newi = i.top,^(next) pop.
^(stk), Fstate.top, newi, idxNB (myinput, newi), result.top, faili.top, failini.top,
failresult.top) else^(next) pop.^(stk), Fstate.top, faili.top, failini.top, failresult.top, faili.top, failini.top,
failresult.top)"
else if action.state = Success* then
"let top = top.stk,^(next) pop.^(stk), Sstate.top,^(i),^(inputi), result.top+
^(result), faili.top, failini.top, failresult.top)"
else if action.state = Discard* then
"let top = top.stk,^(next)^(stk),^(cvt(info, nextState.state, 5)),^(i),^(inputi), result.top, i,
^(inputi), result.top)"
else if action.state = Reduce* then
"let R =^(result) let att = [^((reduceNo.state)#actions.info)]^(next)^(stk),
^(cvt(info, nextState.state, 6)),^(i),^(inputi), att,^(i),^(inputi), att)"
else if action.state = Reduce then
"let top = top.stk let R =^(result) let att = [^((reduceNo.state)#actions.info)]^(next) pop.
^(stk), Sstate.top,^(i),^(inputi), result.top+att, faili.top, failini.top, failresult.top)"
else if action.state = All then
"let top = top.stk let att = [toAttribute (1^^(result), subseq (myinput, i.top,^(i)-1))],
^(next) pop.^(stk), Sstate.top,^(i),^(inputi), result.top+att, faili.top, failini.top, failresult.top)"
else
 let te = (index.state)#table.info
 let teaction = action.action.te
 let ns = nextState.action.te,
  if teaction ∈ [NT, NT*] then
   "let newstk = push (^(stk), frame (^(cvt(info, Sstate.te, 7)),^(cvt(info, Fstate.te, 8)),
   ^(i),^(result), faili, failini, failresult)) let tmp = [toAttribute (1^^(result), empty:seq.seqElementType)],"
    + 
    if ns ∈ newStates.info then
    "^(next) newstk,^(cvt(info, ns, 9)),^(i),^(inputi), tmp,^(i),^(inputi), tmp)"
    else build(level + 1, info, ns, "newstk", i, inputi, "tmp", i, inputi, "tmp")
  else if teaction = T' then
   let newi = merge."i^(level)"
   let newinputi = merge."inputi^(level)"
   let KK =
    if Sstate.te ∈ newStates.info ∨ action.Sstate.te = Reduce then
    build(
     level + 1
     , info
     , Sstate.te
     , stk
     , i + "+1"
     , "idxNB (myinput,^(i)+1)"
     , result
     , faili
     , failini
     , failresult
    )
    else "let^(newi) =^(i)+1, let^(newinputi) = idxNB (myinput,^(i)+1)
    ^(build(level + 1, info, Sstate.te, stk, [newi], [newinputi], result, faili, failini, failresult))",
   "if {T'}^(inputi) =^(replaceWords2(match.te, wordmap.info)) then^(KK) else
   ^(build(level + 1, info, Fstate.te, stk, i, inputi, result, faili, failini, failresult))"
  else if teaction = !T then
   let newinputi = merge."ini^(level)",
   "if {!T}^(inputi) =^(replaceWords2(match.te, wordmap.info)) then
   ^(build(level + 1, info, Sstate.te, stk, faili, failini, failresult, faili, failini, failresult)) else
   ^(build(level + 1, info, Fstate.te, stk, i, inputi, result, faili, failini, failresult))"
  else if teaction = T then
   let newi = merge."i^(level)"
   let newinputi = merge."inputi^(level)",
   "if {T}^(inputi) ≠^(replaceWords2(match.te, wordmap.info)) then let^(newi) = idxNB (myinput, faili)
   ^(build(level + 1, info, Fstate.te, stk, "faili", [newi], result, faili, failini, failresult)) else let
   ^(newi) =^(i)+1, let^(newinputi) = idxNB (myinput,^(i)+1)
   ^(build(level + 1, info, Sstate.te, stk, [newi], [newinputi], result, faili, failini, failresult))"
  else if teaction = MatchAny then
   let newinputi = merge."inputi^(level)"
   let newi = merge."i^(level)"
   let newresult = merge."result^(level)",
   "if {Match Any}^(inputi) = endMark then
   ^(build(level + 1, info, Fstate.te, stk, i, inputi, result, faili, failini, failresult)) else let
   ^(newresult) =^(result)+toAttribute (1^^(result), [^(inputi)]) let^(newi) =^(i)+1 let
   ^(newinputi) = idxNB (myinput,^(i)+1),
   ^(build(
    level + 1
    , info
    , Sstate.te
    , stk
    , [newi]
    , [newinputi]
    , [newresult]
    , faili
    , failini
    , failresult
   ))"
  else "????.^(teaction)"
 