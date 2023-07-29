Module PEGrules

use bits

use seq.pegpart

use otherseq.pegrule

use seq.pegrule

use set.pegrule

use seq.recoveryEntry

use standard

use seq.state

use seq.t5

use set.t5

use seq.tableEntry

use otherseq.seq.word

use set.word

Function PEGgrammar(s:seq.word) seq.pegrule
for
 rules = empty:seq.pegrule
 , parts = empty:seq.pegpart
 , lasthead = ""
 , begin = startstate + 1
 , e1 ∈ break(s, "/br /", true) + ["./action"]
do
 if isempty.e1 ∨ e1 ∈ ["/br"] then
 next(rules, parts, lasthead, begin)
 else
  let z = break(e1, "/action", false)
  assert n.z ∈ [2]
  report "PEGgrammar: expected one /action in^(e1)
   /br^(s)"
  let part1 = if 1_1_z ∈ "/br" then 1_z << 1 else 1_z
  let replacement = 1^z
  let thiskind = if 1_part1 ∈ "/ *" then 1_part1 else 1_"d"
  let thispart = pegpart(if n.z = 3 then 2_z else if thiskind ∈ "*" then part1 << 2 else part1 << 1, replacement),
   if thiskind ∈ "/" then
   next(rules, parts + thispart, lasthead, begin)
   else
    let thishead = if thiskind ∈ "* !" then subseq(part1, 1, 2) else [1_part1],
     if isempty.lasthead then
     next(rules, [thispart], thishead, begin)
     else
      let newrule = rule(if 1_lasthead ∈ "* !" then 1_lasthead else 1_"d", (n.lasthead)_lasthead, parts, begin),
      next(rules + newrule, [thispart], thishead, begin + nostates.newrule)
,
rules

Function smallest(costs:set.t5, w:word) seq.word
let l = lookup(costs, t5(w, "")),
if isempty.l then [w] else right.1_l

function smallest(rules:seq.pegrule) set.t5
let gram = removelambda(rules, "")
let t = BB(gram, t5.gram) ∪ t5.rules
assert true
report "here^(for txt = "", t5 ∈ toseq.t do txt + "/br" + N.t5 + right.t5, txt)",
t

function BB(gram:seq.pegrule, costsin:set.t5) set.t5
for acc = empty:seq.pegrule, costs = costsin, r ∈ gram
do
 let p =
  for minpart = "", min = 10, p ∈ parts.r
  do
   let R =
    for R = "X", w ∈ part.p
    while not.isempty.R
    do
     let l = lookup(costs, t5(w, "")),
     if isempty.l then R + w else if isempty.right.1_l then "" else R + right.1_l
    ,
    R << 1
   ,
   if isempty.R then next(minpart, min(n.part.p, min)) else next(R, min)
  ,
  if between(n.minpart, 1, min) then minpart else ""
 ,
  if isempty.p then
  next(acc + r, costs)
  else next(acc, asset.[t5(leftside.r, p)] ∪ costs)
,
if n.gram = n.acc then
assert isempty.acc report "PROBLEM BB^(acc)", costs
else BB(acc, costs)

type t5 is N:word, right:seq.word

function >1(a:t5, b:t5) ordering N.a >1 N.b

function t5(a:seq.pegrule) set.t5
for acc = empty:seq.t5, r ∈ a do acc + t5(leftside.r, ""),
asset.acc

function removelambda(gram:seq.pegrule, lambdain:seq.word) seq.pegrule
for acc = empty:seq.pegrule, lambda = lambdain, r ∈ gram
do
 if kind.r ∈ "*" then
 next(acc, lambda + leftside.r)
 else
  let rnew = clean(r, lambda)
  let nolambda = for nolambda = true, p ∈ parts.rnew while nolambda do not.isempty.part.p, nolambda,
  if nolambda then next(acc + rnew, lambda) else next(acc, lambda + leftside.rnew)
,
if n.gram = n.acc ∧ lambdain = lambda then acc else removelambda(acc, lambda)

function clean(r:pegrule, lambda:seq.word) pegrule
for acc2 = empty:seq.pegpart, p ∈ parts.r
do
 for acc = "", last = 1_"?", w ∈ part.p
 do
  if w ∈ "!" then
  next(acc, w)
  else if last ∈ "!" ∨ w ∈ lambda then
  next(acc, w)
  else next(acc + w, w)
 ,
 acc2 + pegpart(acc, "")
,
pegrule(kind.r, leftside.r, acc2, nostates.r, begin.r)

function %(r:pegrule) seq.word
[kind.r, leftside.r] + for acc = "", e ∈ parts.r do acc + "/" + part.e, acc + "/br"

function match(has!:boolean, e:word, g:seq.pegrule) state
for acc = startstate + goallength, match = Match, r ∈ g
while match = Match
do
 if e = leftside.r ∧ not.has! then
 next(acc, MatchNT.acc)
 else next(acc + nostates.r, match)
,
match

type pegrule is kind:word, leftside:word, parts:seq.pegpart, nostates:int, begin:state

Export kind(pegrule) word

Export leftside(pegrule) word

Export type:pegpart

Export parts(pegrule) seq.pegpart

Export part(pegpart) seq.word

Export replacement(pegpart) seq.word

type pegpart is part:seq.word, replacement:seq.word

type tableEntry is action:state, match:word, Sstate:state, Fstate:state

Export type:pegrule

Export type:tableEntry

Export Fstate(tableEntry) state

Export Sstate(tableEntry) state

Export match(tableEntry) word

Export action(tableEntry) state

Function textGrammar(g:seq.pegrule) seq.word
for acc = "", Non = empty:set.word, rightsides = "", message = "", r ∈ g
do
 let parts =
  for parts = "", p ∈ parts.r
  do parts + "^(if n.parts < 10 then "" else "/br") /^(part.p)",
  parts << 1
 ,
 next(
  acc + "/br^(if kind.r ∈ "*" then [kind.r] else "")^(leftside.r) ←^(parts)"
  , Non + leftside.r
  , rightsides + parts
  ,
   if leftside.r ∈ Non then
    message
    + "Duplicate non-terminal: ^(leftside.r)
     /br"
   else message
 )
let terms = asset.rightsides \ Non \ asset."/ ! /br"
let unusedNon = toseq(Non \ asset.rightsides - leftside.1_g),
"^(message)^(if isempty.unusedNon then "" else "/br Unused non-termials:^(unusedNon)")
 /br Non-termials:^(alphasort.toseq.Non)
 /br Terminals:^(alphasort.toseq.terms)^(acc)"

function nostates2(a:pegpart, kind:word, parts:seq.pegpart) int
if isempty.part.a then
1
else
 let extrastate =
  if kind ∈ "*" then
   if n.parts = 1 ∧ replacement.1_parts = "/All" ∨ replacement.a = "/Discard" then
   0
   else 1
  else 0
 for acc = extrastate, e ∈ part.a do if e ∈ "!" then acc else acc + 1,
 acc

function goallength int 1

function rule(kind:word, leftside:word, p:seq.pegpart, begin:state) pegrule
for acc = 0, e ∈ p do acc + nostates2(e, kind, p),
pegrule(kind, leftside, p, acc, begin)

function >1(a:pegrule, b:pegrule) ordering leftside.a >1 leftside.b

Function makeTbl(gin:seq.pegrule) seq.tableEntry
let gset = asset.gin
for table = [tableEntry(S.2, leftside.1_gin, Reduce.1, Fail)], reduce0 = 2, s ∈ gin
do
 for
  nextstate2 = begin.s
  , ruletableentries = empty:seq.tableEntry
  , reduce = reduce0
  , remainingparts = n.parts.s
  , p ∈ parts.s
 do
  let nextpart = nextstate2 + nostates2(p, kind.s, parts.s)
  let failmatch =
   if remainingparts > 1 then
   nextpart
   else if kind.s ∈ "*" then
   if replacement.1_parts.s = "/All" then All else Success*
   else Fail
  ,
   if isempty.part.p then
   next(
    nextpart
    , ruletableentries + tableEntry(Reduce.reduce, 1_"?", state.0, state.0)
    , reduce + 1
    , remainingparts - 1
   )
   else
    for
     parttableentries = empty:seq.tableEntry
     , thisstate = nextstate2
     , last = 1_"?"
     , count = 1
     , e ∈ part.p
    do
     if e ∈ "!" then
     next(parttableentries, thisstate, e, count + 1)
     else
      let successmatch =
       if count = n.part.p then
        if kind.s ∈ "*" then
         if replacement.p ∈ ["/Discard"] ∨ failmatch = All then
         Discard*.index.begin.s
         else thisstate + 1
        else if replacement.p ∈ ["/All"] then
        All
        else Reduce.reduce
       else thisstate + 1
      let C =
       if e ∈ "any" then
       tableEntry(MatchAny, e, successmatch, failmatch)
       else
        let look = lookup(gset, pegrule(1_"?", e, empty:seq.pegpart, 0, S.0)),
         if isempty.look then
          if last ∈ "!" then
          tableEntry(!Match, e, successmatch, failmatch)
          else
           {On failure do not reparse common prefix between this part and next part}
           let followpart = nextpart(s, remainingparts)
           let len = n.parttableentries,
            if len > 0 ∧ subseq(part.p, 1, len) = subseq(part.followpart, 1, len) then
             if n.part.followpart = len then
              let tmp =
               if kind.s ∈ "*" then
               nextpart + nostates2(followpart, 1_"X", empty:seq.pegpart)
               else Reduce(reduce + 1)
              ,
              tableEntry(MatchNext, e, successmatch, tmp)
             else tableEntry(MatchNext, e, successmatch, nextpart + n.parttableentries)
            else tableEntry(Match, e, successmatch, failmatch)
         else if last ∈ "!" then
          assert kind.1_look ∉ "*" report "NNN" + e,
          tableEntry(MatchNT.begin.1_look, e, !.successmatch, failmatch)
         else
          let followpart = nextpart(s, remainingparts)
          let len = n.parttableentries,
           if
            len > 0
            ∧ subseq(part.p, 1, len) = subseq(part.followpart, 1, len)
            ∧ len ≠ n.part.followpart
           then
           tableEntry(MatchNT.begin.1_look, e, successmatch, P.index(nextpart + n.parttableentries))
           else tableEntry(MatchNT.begin.1_look, e, successmatch, failmatch)
      ,
      next(parttableentries + C, thisstate + 1, e, count + 1)
    ,
    next(
     nextpart
     ,
      if Sstate.1^parttableentries = thisstate then
      ruletableentries + parttableentries + tableEntry(Reduce.reduce, 1_"?", begin.s, state.0)
      else ruletableentries + parttableentries
     , reduce + 1
     , remainingparts - 1
    )
 ,
 next(table + ruletableentries, reduce0 + if kind.s ∈ "!" then 0 else n.parts.s)
,
table

type recoveryEntry is action:state, match:seq.word, Sstate:state

Export type:recoveryEntry

Export action(recoveryEntry) state

Export Sstate(recoveryEntry) state

Export match(recoveryEntry) seq.word

Export recoveryEntry(action:state, match:seq.word, Sstate:state) recoveryEntry

Function recover(table:seq.tableEntry, gin:seq.pegrule) seq.recoveryEntry
let small = smallest.gin
for acc = empty:seq.recoveryEntry, te ∈ table
do
 if action.te = Match ∨ action.te = MatchNext ∨ action.te = MatchAny then
 acc + recoveryEntry(Match, [match.te], Sstate.te)
 else if action.action.te = S.0 then
 acc + recoveryEntry(Match, smallest(small, match.te), Sstate.te)
 else acc + recoveryEntry(action.te, "", Sstate.te)
,
acc

function nextpart(s:pegrule, remainingparts:int) pegpart
if remainingparts < 2 then
pegpart("", "")
else (n.parts.s - remainingparts + 2)_parts.s

Function postprocess(table:seq.tableEntry, old:seq.word, new:seq.word) seq.tableEntry
if isempty.old then
table
else
 assert n.old = n.new report "PEG:^(dq.old) must be same length as^(dq.new)"
 for newtable = empty:seq.tableEntry, e ∈ table
 do
  newtable
  + 
   if action.e = Match ∨ action.e = !Match then
    let i = findindex(old, match.e),
    if i > n.old then e else tableEntry(action.e, i_new, Sstate.e, Fstate.e)
   else e
 ,
 newtable

Function wordReplace(s:seq.word, old:seq.word, new:seq.word) seq.word
if isempty.old then
s
else for acc = "", w ∈ s do let i = findindex(old, w), acc + if i > n.old then w else i_new, acc

Function NonTerminals(p:pegpart, gin:seq.pegrule) seq.word
for Ncount = "/0", last = 1_"?", e ∈ part.p
do
 if e ∈ "!" ∨ last ∈ "!" ∨ e ∉ "any" ∧ match(last ∈ "!", e, gin) = Match then
 next(Ncount, e)
 else next(Ncount + merge."/^(n.Ncount)", e)
,
Ncount

Function %table(t:seq.tableEntry) seq.word
for acc = "", rowno = 1, a ∈ t
do next(
 acc
 + 
  if action.action.a = actionReduce then
  "/row^(rowno)^(action.a) /cell^(Fstate.a) /cell^(Sstate.a) /cell"
  else "/row^(rowno)^(action.a) /cell^(match.a) /cell^(Sstate.a) /cell^(Fstate.a)"
 , rowno + 1
),
"<* table^(acc) *>"

function >1(a:state, b:state) ordering toint.a >1 toint.b

Function %(s:state) seq.word
let list = "S !Match MatchAny Match MatchNext Fail P Success* Reduce Unused Discard* All"
let actionName = (toint.action.s + 1)_list,
(if is!.s then "!." else "")
 + 
 if actionName ∈ "S Reduce Discard* P" then
 "^(actionName).^(index.s)"
 else [actionName]

type state is toint:int

Export type:state

Export state(int) state

Export ∈(state, seq.state) boolean {From seq.state}

function shift int 32

Function index(i:state) int toint.i / shift

Function =(a:state, b:state) boolean toint.a = toint.b

function MatchNT(state:state) state state

Function S(i:int) state state(i * shift)

Function P(i:int) state state(i * shift + toint.actionP)

Function Reduce(partno:int) state state(partno * shift + toint.actionReduce)

Function Discard*(Sstate:int) state state(Sstate * shift + toint.actionDiscard*)

function actionReduce*(partno:int) state state.partno

function +(s:state, i:int) state state(toint.s + i * shift)

Function action(s:state) state state.toint(bits.toint.s ∧ 0xF)

Function !(s:state) state state.toint(bits.toint.s ∨ 0x10)

Function is!(s:state) boolean (bits.toint.s ∧ 0x10) = 0x10

Function !Match state {T} state.1

Function MatchAny state {T} state.2

Function Match state {T} state.3

Function MatchNext state {T} state.4

Function Fail state {NT} state.5

Function actionP state state.6

Function Success* state {NT} state.7

Function actionReduce state {NT} state.8

Function actionDiscard* state {NT} state.10

Function All state {NT} state.11

/Function actionMatchNT state state.0

Function startstate state state.shift 