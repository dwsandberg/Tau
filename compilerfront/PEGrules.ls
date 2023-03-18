Module PEGrules

???? handle" * R a; b; c; d; any" so final string is only created at end.

make PEGbyte.ls handle blanklines at beginning.

???? for statement fails some times because generated locals are not unique. 

???? handle" S a b c d sp / a b c e" so first part is not scanned twice.

???? further test of ! operator. 

???? optimize PEGbyte.ls

???? add error recovery

use standard

use seq.pegpart

use seq.pegrule

use seq.tableEntry

Function pattern2code(pattern:seq.word) seq.word
 for acc = "", last = "", w ∈ pattern + dq
 do
  if last ≠ "^" then
  next(acc + last, [w])
  else if checkinteger.w ∈ "INTEGER" then
  next(acc + dq."+R_$([w])+", "")
  else next(acc + last, [w])
 /do dq.acc

Function PEGgrammar(s:seq.word) seq.pegrule
 for
  rules = empty:seq.pegrule
  , parts = empty:seq.pegpart
  , lasthead = ""
  , e1 ∈ break(s, "/br /", true) + ["./action"]
 do
  if isempty.e1 ∨ e1 ∈ ["/br"] then
  next(rules, parts, lasthead)
  else
   let z = break(e1, "/action", false)
    assert length.z ∈ [2, 3] report "PEGgrammar ??" + lasthead + e1 + "/br" + s
    let part1 = if first.z_1 ∈ "/br" then z_1 << 1 else z_1
    let replacement = last.z
    let thiskind = if first.part1 ∈ "/ * !" then first.part1 else "d"_1
    let thispart = pegpart(
     if length.z = 3 then z_2 else if thiskind ∈ "* !" then part1 << 2 else part1 << 1
     , replacement
    ),
    if thiskind ∈ "/" then
    next(rules, parts + thispart, lasthead)
    else
     let thishead = if thiskind ∈ "* !" then subseq(part1, 1, 2) else [first.part1]
     let newrules =
      if isempty.lasthead then
      rules
      else rules + rule(first.if first.lasthead ∈ "* !" then lasthead else "d", last.lasthead, parts)
     ,
     next(newrules, [thispart], thishead)
 /do rules

use otherseq.pegrule

function match(has!:boolean, e:word, g:seq.pegrule) state
 for acc = startstate + goallength, match = Match, r ∈ g
 while match = Match
 do
  if e = leftside.r ∧ has! = kind.r ∈ "!" then
  next(acc, MatchNT.acc)
  else next(acc + nostates.r, match)
 /do match

type pegrule is kind:word, leftside:word, parts:seq.pegpart, nostates:int

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

function nostates2(a:pegpart, kind:word, parts:seq.pegpart) int
 if isempty.part.a then
 1
 else
  let extrastate =
   if kind ∈ "*" then
    if length.parts = 1 ∧ replacement.first.parts = "\All" ∨ replacement.a = "\Discard" then
    0
    else 1
   else 0
  ,
  for acc = extrastate, e ∈ part.a do if e ∈ "!" then acc else acc + 1 /do acc

function goallength int 1

function rule(kind:word, leftside:word, p:seq.pegpart) pegrule
for acc = 0, e ∈ p do acc + nostates2(e, kind, p) /do pegrule(kind, leftside, p, acc)

use otherseq.seq.word

use otherseq.word

function =(a:pegpart, b:pegpart) boolean
let t = part.a = part.b assert t report "XX" + part.a + part.b, t

function =(a:pegrule, b:pegrule) boolean
 let t = kind.a = kind.b ∧ leftside.a = leftside.b ∧ parts.a = parts.b
 assert t report "XX" + leftside.a + leftside.b + kind.a + kind.b,
 t

function replacement(kind:seq.word, r:pegpart) seq.word
 if kind = "code" then
 replacement.r
 else if kind = "first" then
 "R_0"
 else assert kind = "words" report "unknown replacement type:" + kind, pattern2code.replacement.r

Function makeAction(kind:seq.word, gin:seq.pegrule) seq.word
 for acc = "", partno = 2, r ∈ gin
 do
  let x =
   for partno0 = partno, acc0 = acc, p ∈ parts.r
   do
    let tmp =
     if replacement.p ∈ ["\All", "\Discard"] then
     ""
     else "if partno = $(partno0) then $(replacement(kind, p)) else"
    ,
    next(partno0 + 1, acc0 + tmp)
   /do acc0
  ,
  next(x, partno + length.parts.r)
 /do "$(acc >> 1) else R_0"

Function makeTbl(gin:seq.pegrule) seq.tableEntry
 let g = [rule("d"_1, "G"_1, [pegpart([leftside.first.gin], "")])] + gin,
  for nextstate = startstate, table = empty:seq.tableEntry, reduce0 = 1, s ∈ g
  do
   let begin = nextstate
   let ruletableentries =
    for
     nextstate2 = nextstate
     , acc = empty:seq.tableEntry
     , reduce = reduce0
     , remainingparts = length.parts.s
     , p ∈ parts.s
    do
     let nextpart = nextstate2 + nostates2(p, kind.s, parts.s)
      let failmatch =
       if remainingparts > 1 then
       nextpart
       else if kind.s ∈ "*" then
       if length.parts.s = 1 ∧ replacement.first.parts.s = "\All" then All else Success*
       else if kind.s ∈ "!" then
       New!
       else Fail
      let parttableentries =
       for acc2 = empty:seq.tableEntry, thisstate = nextstate2, last = "?"_1, e ∈ part.p
       do
        if e ∈ "!" then
        next(acc2, thisstate, e)
        else
         let ee = match(last ∈ "!", e, gin)
          let action = if e ∈ "any" then MatchAny else if last ∈ "!" ∧ ee = Match then !Match else ee
          let C = tableEntry(action, e, thisstate + 1, failmatch),
         next(acc2 + C, thisstate + 1, e)
       /do
        if isempty.acc2 then
         assert kind.s ∉ "* !" report "PEG grammar problem",
         [tableEntry(Reduce.reduce, "?"_1, state.0, state.0)]
        else if kind.s ∈ "*" then
         if replacement.p ∈ ["\Discard"] ∨ failmatch = All then
          let final = last.acc2,
          acc2 >> 1 + tableEntry(action.final, match.final, Discard*.index.begin, Fstate.final)
         else acc2 + tableEntry(Reduce.reduce, "?"_1, begin, state.0)
        else
         let final = last.acc2,
          if kind.s ∈ "!" then
          acc2 >> 1 + tableEntry(action.final, match.final, Fail, New!)
          else acc2 >> 1 + tableEntry(action.final, match.final, Reduce.reduce, Fstate.final)
      ,
     next(nextpart, acc + parttableentries, reduce + 1, remainingparts - 1)
    /do acc
   ,
   next(
    nextstate + length.ruletableentries
    , table + ruletableentries
    , reduce0 + if kind.s ∈ "!" then 0 else length.parts.s
   )
  /do table

Function postprocess(table:seq.tableEntry, old:seq.word, new:seq.word) seq.tableEntry
 if isempty.old then
 table
 else
  assert length.old = length.new report "PEG:$(dq.old) must be same length as $(dq.new)",
   for newtable = empty:seq.tableEntry, e ∈ table
   do
    newtable
    + 
     if action.e = Match ∨ action.e = !Match then
      let i = findindex(old, match.e),
      if i > length.old then e else tableEntry(action.e, new_i, Sstate.e, Fstate.e)
     else e
   /do newtable

Function wordReplace(s:seq.word, old:seq.word, new:seq.word) seq.word
 if isempty.old then
 s
 else
  for acc = "", w ∈ s
  do let i = findindex(old, w), acc + if i > length.old then w else new_i
  /do acc

Function NonTerminals(p:pegpart, gin:seq.pegrule) seq.word
 for Ncount = "/0", last = "?"_1, e ∈ part.p
 do
  if e ∈ "!" ∨ last ∈ "!" ∨ e ∉ "any" ∧ match(last ∈ "!", e, gin) = Match then
  next(Ncount, e)
  else next(Ncount + merge."/ $(length.Ncount)", e)
 /do Ncount

use otherseq.int

Function %table(t:seq.tableEntry) seq.word
 for acc = "", rowno = 1, a ∈ t
 do next(
  acc
  + 
   if action.action.a = actionReduce then
   "/row $(rowno) $(action.a) /cell $(Fstate.a) /cell $(Sstate.a) /cell"
   else "/row $(rowno) $(action.a) /cell $(match.a) /cell $(Sstate.a) /cell $(Fstate.a)"
  , rowno + 1
 )
 /do "<* table $(acc) *>"

function more(t:seq.tableEntry) seq.word
 for acc2 = empty:set.g5, unprocessed = empty:set.state, e ∈ t
 do
  if match.e ∈ "?" ∨ action.e ∈ [Match, !Match, MatchAny] then
  next(acc2, unprocessed)
  else
   let t6 = t6({action.e,} action.e, t),
   if isempty.t6 then next(acc2, unprocessed + action.e) else next(acc2 ∪ t6, unprocessed)
 /do let tt = t8(toseq.unprocessed, acc2, t), %.cardinality.tt + %.toseq.tt

use set.g5

use otherseq.state

use otherseq.g5

function >1(a:g5, b:g5) ordering toint.left.a >1 toint.left.b

function %(g:g5) seq.word "/br $(left.g) $(right.g)"

type g5 is left:state, right:seq.word

use set.state

function >1(a:state, b:state) ordering toint.a >1 toint.b

Function t8(s:seq.state, processed:set.g5, table:seq.tableEntry) set.g5
 for acc = processed, acc2 = empty:seq.state, e ∈ s
 do
  let t = t7(e, processed, table),
  if isempty.t then next(acc, acc2 + e) else next(acc ∪ t, acc2)
 /do
  if length.acc2 < length.s then
  t8(acc2, acc, table)
  else assert length.s = 0 report %.s, acc

Function t6(state:state, table:seq.tableEntry) set.g5
 let t5 = t5(state, state, table),
  if not.isempty.t5 then
  t5
  else
   for acc = empty:seq.word, last = S.0, e ∈ table << (index.state - 1)
   while action.e ∈ [Match, !Match, MatchAny] ∧ last = S.0
   do next(if action.e ∈ [Match, MatchAny] then acc + match.e else acc, action.Sstate.e)
   /do
    {assert state /ne S.206 report" XX"+%.last+%table.[e]}
    if last = actionReduce then asset.[g5(state, acc)] else empty:set.g5

Function t5(org:state, state:state, table:seq.tableEntry) set.g5
 assert action.state = S.0 report "???"
 assert between(index.state, 1, length.table) report "???2" let te = table_(index.state),
  if Fstate.te ∈ [Success*, S.0] then
  asset.[g5(org, "")]
  else if action.Fstate.te = S.0 then
  t5(org, Fstate.te, table)
  else empty:set.g5

Function t7(state:state, processed:set.g5, table:seq.tableEntry) set.g5
 for
  parts = empty:seq.seq.word
  , acc = empty:seq.word
  , skip = false
  , done = false
  , skipsize = 100
  , e ∈ table << (index.state - 1)
 while not.done
 do
  let X =
   if action.e ∈ [Match, MatchAny] then
   [[match.e]]
   else
    let l = lookup(processed, g5(action.e, "")),
    if not.isempty.l then [right.l_1] else empty:seq.seq.word
   {if isempty.X /and action.e /ne state then next (empty:seq.seq.word,"", true, true, skipsize) else}
   let newskip = action.e = state ∨ skip ∨ isempty.X
   let k = %.action.e + match.e + %.Sstate.e,
   if action.Sstate.e = actionReduce then
    {at end of part}
     let newpart = if not.isempty.X then acc + first.X else acc,
     {assert state /ne S.154 /or cardinality.processed /ne 24 /or k /in [" Match) Reduce.54"] report" LL"+%.k+" LL"+%.X+%.skipsize+newpart+if newskip then" newskip" else"" /if}
     if newskip then
     next(parts, "", false, Fstate.e = Fail, min(skipsize, length.newpart))
     else next(
      if length.newpart > skipsize then parts else parts + newpart
      , ""
      , false
      , Fstate.e = Fail
      , skipsize
     )
   else next(
    parts
    , acc + if newskip then if action.e = state then "X" else "" else first.X
    , newskip
    , false
    , skipsize
   )
 /do
  if isempty.parts then
  empty:set.g5
  else
   for shortest = first.parts, p ∈ parts << 1
   do if length.p < length.shortest then p else shortest
   /do asset.[g5(state, shortest)]

use set.seq.word

use seq.state

Function %(s:state) seq.word
 let list = "S !Match MatchAny Match Fail Success*! Success* Reduce New! Discard* All"
 let actionName = list_(toint.action.s + 1),
 if actionName ∈ "S Reduce Discard*" then "$(actionName).$(index.s)" else [actionName]

type state is toint:int

Export type:state

Export state(int) state

function shift int 16

Function index(i:state) int toint.i / shift

Function =(a:state, b:state) boolean toint.a = toint.b

function MatchNT(state:state) state state

Function S(i:int) state state(i * shift)

Function Reduce(partno:int) state state(partno * shift + toint.actionReduce)

Function Discard*(Sstate:int) state state(Sstate * shift + toint.actionDiscard*)

function actionReduce*(partno:int) state state.partno

function +(s:state, i:int) state state(toint.s + i * shift)

use bits

Function action(s:state) state state.toint(bits.toint.s ∧ 0xF)

Function !Match state {T} state.1

Function MatchAny state {T} state.2

Function Match state {T} state.3

Function NoTable(s:state) boolean toint.s > 3

Function Fail state {NT} state.4

Function Success*! state {NT} state.5

Function Success* state {NT} state.6

Function actionReduce state {NT} state.7

Function New! state {NT} state.8

Function actionDiscard* state {NT} state.9

Function All state {NT} state.10

/Function actionMatchNT state state.0

Function startstate state state.shift

Function funny(s:state) boolean toint.s = 0

 