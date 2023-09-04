Module PEGrules

use bits

use otherseq.pegpart

use seq.pegpart

use otherseq.pegrule

use seq.pegrule

use set.pegrule

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
 , Non = empty:set.word
 , e1 ∈ break(s, "/br /", true) + ["./action"]
do
 if isempty.e1 ∨ e1 ∈ ["/br"] then
 next(rules, parts, lasthead, begin, Non)
 else
  let z = break(e1, "/action", false)
  assert n.z ∈ [2] report "PEGgrammar: expected one /action in^(e1) /br^(s)"
  let part1 = if 1_1_z ∈ "/br" then 1_z << 1 else 1_z
  let replacement = 1^z
  let thiskind = if 1_part1 ∈ "/ *" then 1_part1 else 1_"d"
  let thispart = pegpart(if n.z = 3 then 2_z else if thiskind ∈ "*" then part1 << 2 else part1 << 1, replacement),
   if thiskind ∈ "/" then
   next(rules, parts + thispart, lasthead, begin, Non)
   else
    let thishead = if thiskind ∈ "* !" then subseq(part1, 1, 2) else [1_part1],
     if isempty.lasthead then
     next(rules, [thispart], thishead, begin, Non)
     else
      let newrule = rule(if 1_lasthead ∈ "* !" then 1_lasthead else 1_"d", (n.lasthead)_lasthead, parts, begin)
      assert leftside.newrule ∉ Non report "Duplicate Non-Terminal:^(leftside.newrule)",
      next(rules + newrule, [thispart], thishead, begin + nostates.newrule, Non + leftside.newrule),
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
     if isempty.l then R + w else if isempty.right.1_l then "" else R + right.1_l,
    R << 1,
   if isempty.R then next(minpart, min(n.part.p, min)) else next(R, min),
  if between(n.minpart, 1, min) then minpart else "",
  if isempty.p then
  next(acc + r, costs)
  else next(acc, asset.[t5(leftside.r, p)] ∪ costs),
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
  if nolambda then next(acc + rnew, lambda) else next(acc, lambda + leftside.rnew),
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
  else next(acc + w, w),
 acc2 + pegpart(acc, ""),
pegrule(kind.r, leftside.r, acc2, nostates.r, begin.r)

function %(r:pegrule) seq.word
[kind.r, leftside.r] + for acc = "", e ∈ parts.r do acc + "/" + part.e, acc + "/br"

function match(has!:boolean, e:word, g:seq.pegrule) state
for acc = startstate + goallength, match = Match, r ∈ g
while match = Match
do
 if e = leftside.r ∧ not.has! then
 next(acc, MatchNT.acc)
 else next(acc + nostates.r, match),
match

type pegrule is kind:word, leftside:word, parts:seq.pegpart, nostates:int, begin:state

Export kind(pegrule) word

Export leftside(pegrule) word

Export type:pegpart

Export parts(pegrule) seq.pegpart

Export part(pegpart) seq.word

Export replacement(pegpart) seq.word

Export begin(pegrule) state

type pegpart is part:seq.word, replacement:seq.word

type tableEntry is
action:state
, match:word
, Sstate:state
, Fstate:state
, recover:seq.word

Export tableEntry(
 action:state
 , match:word
 , Sstate:state
 , Fstate:state
 , recover:seq.word
) tableEntry

Export type:pegrule

Export type:tableEntry

Export Fstate(tableEntry) state

Export Sstate(tableEntry) state

Export action(tableEntry) state

Export match(tableEntry) word

Export recover(tableEntry) seq.word

Function textGrammar(g:seq.pegrule) seq.word
for acc = "", Non = empty:set.word, rightsides = "", message = "", r ∈ g
do
 let parts =
  for parts = "", p ∈ parts.r
  do parts + "^(if n.parts < 10 then "" else "/br") /^(part.p)",
  parts << 1,
 next(
  acc + "/br^(if kind.r ∈ "*" then [kind.r] else "")^(leftside.r) ←^(parts)"
  , Non + leftside.r
  , rightsides + parts
  , if leftside.r ∈ Non then
   message + "Duplicate non-terminal: ^(leftside.r) /br"
   else message
 )
let terms = asset.rightsides \ Non \ asset."/ ! /br"
let unusedNon = toseq(Non \ asset.rightsides - leftside.1_g),
"^(message)^(if isempty.unusedNon then "" else "/br Unused non-terminals:^(unusedNon)")
 /br Non-terminals:
 ^(alphasort.toseq.Non)
 /br Terminals:^(alphasort.toseq.terms)^(acc)"

function nostates(a:pegpart) int
for acc = 0, e ∈ part.a do if e ∈ "!" then acc else acc + 1,
acc

function goallength int 1

function rule(kind:word, leftside:word, p:seq.pegpart, begin:state) pegrule
for acc = 0, e ∈ p do acc + nostates.e,
pegrule(kind, leftside, p, acc, begin)

function >1(a:pegrule, b:pegrule) ordering leftside.a >1 leftside.b

function failmatch(s:pegrule, partno:int, nextpart:state, reduce:int) state
if n.parts.s > partno then
if isempty.part.(partno + 1)_parts.s then Reduce(reduce + 1) else nextpart
else if kind.s ∈ "*" then
 let replacement = replacement.partno_parts.s,
  if replacement = "/All" then
  All
  else if replacement = "/Discard" then
  SuccessDiscard*
  else Success*
else Fail

function =(a:tableEntry, b:tableEntry) boolean
action.a = action.b ∧ Fstate.a = Fstate.b ∧ Fstate.a = Fstate.b

Function makeTbl(gin:seq.pegrule, recover:boolean) seq.tableEntry
let small = if recover then smallest.gin else empty:set.t5
let gset = asset.gin
for table = [tableEntry(MatchNT.S.2, 1_"?", Reduce.1, Reduce.0, "")], reduce0 = 2, s ∈ gin
do
 for
  lastnextstate2 = S.0
  , nextstate2 = begin.s
  , ruletableentries = empty:seq.tableEntry
  , partno = 1
  , p ∈ parts.s
 do
  let reduce = partno + reduce0 - 1
  let nextpart = nextstate2 + nostates.p
  for
   parttableentries = ruletableentries
   , thisstate = nextstate2
   , last = 1_"?"
   , count = 1
   , e ∈ part.p
  do
   if e ∈ "!" then
   next(parttableentries, thisstate, e, count + 1)
   else
    let success1 =
     if count = n.part.p then
      if kind.s ∈ "*" then
       if replacement.p ∈ ["/Discard", "/All"] then
       Discard*.begin.s
       else Reduce(reduce, begin.s)
      else if replacement.p ∈ ["/All"] then
      All
      else Reduce.reduce
     else thisstate + 1
    let fail1 = failmatch(s, partno, nextpart, reduce)
    for RecoverEnding = "", last0 = 1_"?", w ∈ if recover then part.p << (count - 1) else ""
    do next(if w ∈ "!" ∨ last0 ∈ "!" then RecoverEnding else RecoverEnding + smallest(small, w), w)
    let C =
     if e ∈ "any" then
     tableEntry(MatchAny, 1_"?", success1, fail1, RecoverEnding)
     else
      let look = lookup(gset, pegrule(1_"?", e, empty:seq.pegpart, 0, S.0)),
       if isempty.look then
        if last ∈ "!" then
        tableEntry(!Match, e, fail1, success1, RecoverEnding)
        else tableEntry(Match, e, success1, fail1, RecoverEnding)
       else
        let success2 = if last ∈ "!" then !.success1 else success1,
        tableEntry(MatchNT.begin.1_look, 1_"?", success2, fail1, RecoverEnding)
    let newpt =
     if
      partno > 1
      ∧ count > 0
      ∧ subseq(part.(partno - 1)_parts.s, 1, count) = subseq(part.p, 1, count)
     then
      {part shares prefix with previous part so avoid backtracking. }
      let zidx = 2 + (index.thisstate - index.nextstate2)
      let z = zidx_parttableentries,
       if action.z = Match then
       replace(parttableentries, zidx, tableEntry(MatchNext, match.z, Sstate.z, Sstate.C, recover.z))
       else if action.action.z ∈ [MatchNT, !Match, MatchAny] then
       replace(parttableentries, zidx, tableEntry(action.z, match.z, Sstate.z, Sstate.C, recover.z))
       else
        assert action.action.z ∈ [MatchAny, MatchNext]
        report "Pegrules^(action.z) Sstate:^(Sstate.C)::^(action.Sstate.C)" + part.p,
        parttableentries
     else parttableentries,
    next(newpt + C, thisstate + 1, e, count + 1),
  next(nextstate2, nextpart, parttableentries, partno + 1),
 next(table + ruletableentries, reduce0 + if kind.s ∈ "!" then 0 else n.parts.s),
stateX.table

function stateX(tbl:seq.tableEntry) seq.tableEntry
for acc = empty:seq.tableEntry, e ∈ tbl
do
 acc
 + tableEntry(stateX(action.e, tbl), match.e, stateX(Sstate.e, tbl), stateX(Fstate.e, tbl), recover.e),
acc

function stateX(s:state, tbl:seq.tableEntry) state
if index.s = 0 then
s
else
 let tblaction = action.action.(index.s)_tbl,
  if tblaction = MatchNT then
  s
  else
   let action =
    if tblaction = Match then
    Match.index.s
    else if tblaction = MatchAny then
    MatchAny.index.s
    else if tblaction = MatchNext then
    MatchNext.index.s
    else assert tblaction = !Match report "XX genPEGY", !Match.index.s,
    if action.s = S then
    action
    else if action.s = Discard* then
    Discard*.action
    else if action.s = MatchNT then
    MatchNT.action
    else
     assert action.s = Reduce report "XX genPEGX^(%.s)^(tblaction)^(%table.tbl)",
     Reduce(reduceNo.s, action)

use otherseq.tableEntry

function %(p:pegpart) seq.word "/br^(part.p)"

Function postprocess(table:seq.tableEntry, old:seq.word, new:seq.word) seq.tableEntry
if isempty.old then
table
else
 assert n.old = n.new report "PEG:^(dq.old) must be same length as^(dq.new)"
 for newtable = empty:seq.tableEntry, e ∈ table
 do
  newtable
  + 
   if action.e ∈ [Match, !Match, MatchNext] then
    let i = findindex(old, match.e),
    if i > n.old then e else tableEntry(action.e, i_new, Sstate.e, Fstate.e, "")
   else e,
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
 else next(Ncount + merge."/^(n.Ncount)", e),
Ncount

function esc(w:word) seq.word
if w ∈ "/cell /row <* *> /em /strong /p" then
"^(escapeformat)^(w)^(escapeformat)"
else [w]

use UTF8

Function %table(t:seq.tableEntry) seq.word
for acc = "", rowno = 1, a ∈ t
do next(
 acc
 + 
  if action.action.a = Reduce then
  "/row^(rowno)^(action.a) /cell^(Fstate.a) /cell^(Sstate.a) /cell"
  else "/row^(rowno)^(action.a) /cell^(match.a) /cell^(Sstate.a) /cell^(Fstate.a)"
 , rowno + 1
),
"<* table^(acc) *>"

function >1(a:state, b:state) ordering toint.a >1 toint.b

Function %(s:state) seq.word
let actionName = 1^decode.action.s,
if bits.toint.s >> (actionBits - 1) = 0x0 then
[actionName]
else
 (if is!.s then "!." else "")
 + 
  if actionName ∈ "Reduce" then
   let idx = nextState.s,
   if idx = S.0 then "Reduce.^(reduceNo.s)" else "Reduce (^(reduceNo.s),^(idx))"
  else if actionName ∈ "Discard* MatchNT" then
  "^(actionName).^(nextState.s)"
  else "^(actionName).^(index.s)"

Export ∈(state, seq.state) boolean {From seq.state}

function mask(nobits:int) bits {move to bits????} tobits.-1 >> (64 - nobits)

function actionBits int 5

function reduceBits int 15

function shiftIndex int actionBits + reduceBits + actionBits

function state(action:state, tblidx:int, reduceNo:int, tblaction:state) state
{OPTION INLINE}
state.toint(
 tobits.tblidx << (reduceBits + 2 * actionBits)
 ∨ tobits.toint.action.tblaction << (reduceBits + actionBits)
 ∨ tobits.reduceNo << actionBits
 ∨ tobits.toint.action.action
)

function state(action:state, tblidx:int) state
state.toint(tobits.tblidx << (reduceBits + 2 * actionBits) ∨ tobits.toint.action.action)

Function index(s:state) int toint(tobits.toint.s >> shiftIndex)

Function reduceNo(s:state) int toint(tobits.toint.s >> actionBits ∧ mask.reduceBits)

Function action(s:state) state state.toint(bits.toint.s ∧ mask(actionBits - 1))

Function MatchNT(state:state) state state(MatchNT, index.state, 0, action.state)

Function S(i:int) state state(S, i)

Function Match(i:int) state state(Match, i)

Function MatchNext(i:int) state state(MatchNext, i)

Function MatchAny(i:int) state state(MatchAny, i)

Function !Match(i:int) state state(!Match, i)

Function Reduce(partno:int) state state(Reduce, 0, partno, S.0)

Function Reduce(partno:int, state:state) state
state(Reduce, index.state, partno, action.state)

Function nextState(s:state) state
state.toint(
 tobits.toint.s >> (actionBits + reduceBits) ∧ mask(actionBits - 1)
 ∨ tobits.toint.s >> shiftIndex << shiftIndex
)

Function Discard*(state:state) state state(Discard*, index.state, 0, action.state)

function +(s:state, i:int) state state(toint.s + toint(tobits.i << shiftIndex))

Function !(s:state) state state.toint(bits.toint.s ∨ 0x10)

Function is!(s:state) boolean (bits.toint.s ∧ 0x10) = 0x10

Function startstate state S.1

The state MatchNext is like Match but does not rollback result on failure.Similarly actionP but does
not rollback result on failure.

function genEnum seq.seq.word
["newType = state values = S !Match MatchAny Match MatchNext Fail ? Success* Reduce Discard* All
 SuccessDiscard* MatchNT"]

<<<< Below is auto generated code >>>>

type state is toint:int

Export toint(state) int

Export state(i:int) state

Export type:state

Function =(a:state, b:state) boolean toint.a = toint.b

Function S state state.0

Function !Match state state.1

Function MatchAny state state.2

Function Match state state.3

Function MatchNext state state.4

Function Fail state state.5

Function Success* state state.7

Function Reduce state state.8

Function Discard* state state.9

Function All state state.10

Function SuccessDiscard* state state.11

Function MatchNT state state.12

Function decode(code:state) seq.word
let discard = [
 S
 , !Match
 , MatchAny
 , Match
 , MatchNext
 , Fail
 , Success*
 , Reduce
 , Discard*
 , All
 , SuccessDiscard*
 , MatchNT
]
let i = toint.code,
if between(i + 1, 1, 13) then
 let r = [
  (i + 1)
  _"S !Match MatchAny Match MatchNext Fail ? Success* Reduce Discard* All SuccessDiscard* MatchNT"
 ],
 if r ≠ "?" then r else "state." + toword.i
else "state." + toword.i 