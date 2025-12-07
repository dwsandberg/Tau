Module PEGrules

use UTF8

use bits

use seq.int

use seq1.oneRule

use set.oneRule

use seq1.pegpart

use seq.pegpart

use seq1.pegrule

use set.pegrule

use standard

use seq.state

use seq1.tableEntry

use seq1.word

use set.word

use sort.word

Export state(i:int) state

Export type:pegpart

Export part(pegpart) seq.word

Export replacement(pegpart) seq.word

Export pegpart(part:seq.word, replacement:seq.word) pegpart

Export type:pegrule

Export begin(pegrule) state

Export kind(pegrule) word

Export leftside(pegrule) word

Export parts(pegrule) seq.pegpart

Export pegrule(word, word, seq.pegpart, int, state) pegrule

Export type:state

Export toint(state) int

Export type:tableEntry

Export Fstate(tableEntry) state

Export Sstate(tableEntry) state

Export action(tableEntry) state

Export match(tableEntry) word

Export recover(tableEntry) seq.word

Export tableEntry(
action:state
, match:word
, Sstate:state
, Fstate:state
, recover:seq.word
) tableEntry

Export ∈(state, seq.state) boolean{From seq.state}

Function adjust(g:seq.pegrule) seq.pegrule
for
 rZ = empty:set.word
 , r!Z = empty:set.word
 , NonT = empty:set.word
 , NonT* = empty:set.word
 , begin = state(Idx, 2)
 , newg1 = empty:seq.pegrule
 , r ∈ g
do
 for pZ = "", p!Z = "", p ∈ parts.r
 do
  for eZ = pZ, e!Z = p!Z, last = "?" sub 1, e ∈ part.p
  do
   if e ∈ "!" then next(eZ, e!Z, e)
   else if last ∈ "!" then next(eZ, e!Z + e, e)
   else next(eZ + e, e!Z, e),
  next(eZ, e!Z)
 assert leftside.r ∉ NonT ∪ NonT* report "Duplicate Non-Terminal::(leftside.r):(%(2, g))"
 let noStates = n.pZ + n.p!Z,
 let newg = newg1 + pegrule(kind.r, leftside.r, parts.r, noStates, begin),
 if kind.r ∈ "*+" then next(rZ ∪ asset.pZ, r!Z ∪ asset.p!Z, NonT, NonT* + leftside.r, begin + noStates, newg)
 else next(rZ ∪ asset.pZ, r!Z ∪ asset.p!Z, NonT + leftside.r, NonT*, begin + noStates, newg)
assert isempty(r!Z ∩ NonT*) report "cannot use ! on * Non-terminal"
let NonT! = NonT ∩ r!Z
let NonTAdd = NonT! ∩ rZ
let NonTchange = NonT! \ NonTAdd
for acc = empty:seq.pegrule, add = empty:seq.pegrule, r ∈ newg1
do
 if leftside.r ∈ NonTchange then next(acc + pegrule("!" sub 1, leftside.r, parts.r, nostates.r, begin.r), add)
 else if leftside.r ∈ NonTAdd then next(acc, add + r)
 else next(acc + r, add)
assert isempty.add report
 "PEG grammar not implemented using same non-terminal with ! and without ! /br
 NonT!:(toseq.NonT!)/br NonTAdd:(toseq.NonTAdd)",
acc

-----------

function smallest(costs:set.oneRule, w:word) seq.word
let l = lookup(costs, oneRule(w, "", false)),
if isempty.l then [w] else right.l sub 1

function smallest(rules:seq.pegrule) set.oneRule
for nonTerminals = empty:set.word, r ∈ rules do nonTerminals + leftside.r
for acc1 = empty:set.oneRule, r ∈ rules
do
 if kind.r ∈ "*" then acc1 + oneRule(leftside.r, "", true)
 else
  for acc2 = acc1, p ∈ parts.r
  do
   for right = "", last = "?" sub 1, w ∈ part.p
   do if w ∈ "!" ∨ last ∈ "!" then next(right, w) else next(right + w, w),
   acc2 + oneRule(leftside.r, right, isempty(asset.part.p ∩ nonTerminals)),
  acc2
for s = acc1, continue = true
while continue
do
 let f = substitute(s, s sub 1)
 for acc = [f], last = f, changed = right.f ≠ right.s sub 1, e0 ∈ toseq.s << 1
 do
  let e = substitute(s, e0)
  let newchanged = changed ∨ right.e ≠ right.e0,
  if left.last = left.e ∧ allTerminals.last then if allTerminals.e then next(acc, last, true) else next(acc + e, last, newchanged)
  else next(acc + e, e, newchanged),
 next(asset.acc, changed),
s

type oneRule is left:word, right:seq.word, allTerminals:boolean

function >1(a:oneRule, b:oneRule) ordering left.a >1 left.b ∧ right.a >1 right.b

function >2(a:oneRule, b:oneRule) ordering left.a >1 left.b

function substitute(z:set.oneRule, e:oneRule) oneRule
if allTerminals.e then e
else
 for rightNew = "", all = true, w ∈ right.e
 do
  let find = findelement2(z, oneRule(w, [w], false)),
  if n.find = 1 then next(rightNew + right.find sub 1, all ∧ allTerminals.find sub 1)
  else next(rightNew + w, all ∧ n.find = 0),
 oneRule(left.e, rightNew, all)

-------------

function %(r:pegrule) seq.word
[kind.r, leftside.r]
 + for acc = "", e ∈ parts.r do acc + "/" + part.e,
acc + "/br"

type pegrule is kind:word, leftside:word, parts:seq.pegpart, nostates:int, begin:state

type pegpart is part:seq.word, replacement:seq.word

type tableEntry is
action:state
, match:word
, Sstate:state
, Fstate:state
, recover:seq.word

Function textGrammar(g:seq.pegrule) seq.word
for Non = empty:set.word, rightsides = "", r ∈ g
do
 for parts = "", e ∈ parts.r do parts + part.e,
 next(Non + leftside.r, rightsides + parts)
let terms =
 asset.rightsides
 \ Non
 \ asset."/ ! /br
 "
let unusedNon = toseq(Non \ asset.rightsides - leftside.g sub 1),
checkrules.g
 + (if isempty.unusedNon then "" else "/br Unused non-terminals::(unusedNon)")
 + "/br Non-terminals::(sort>alpha.toseq.Non)/br Terminals::(sort>alpha.toseq.terms)"
 + %(5, g)

Function %(format:int, newg:seq.pegrule) seq.word
{1 as string 2-as table 3-as table with action 4-as txt 6-as code}
let action = ["/action", "", "/br", "", "", dq + "="] sub format
let part = ["/br /", "/br", "/br", "/", "/", "/br,:(dq)/"] sub format
let rule =
 [
  "/br"
  , "/td /tr"
  , "/td /tr"
  , "/br:(escapeformat)/br:(escapeformat)"
  , "/br"
  , "/br,:(dq)"
 ]
 sub format
let arrow = ["", "/td", "/td", "←", "←", ""] sub format
for txt0 = "", r ∈ newg
do
 for txt1 = "", e ∈ parts.r
 do txt1 + (part.e + action + (if isempty.action then "" else replacement.e) + part),
 txt0 >> n.part
 + (rule + (if kind.r ∈ "*+" then [kind.r] else "") + %.leftside.r + arrow + txt1),
if format ∈ [2, 3] then "left /th right /th action /th /tr:(txt0)/table"
else if format = 4 then "function genPEG(attributeType:word)seq.boolean[:(subseq(txt0, 3, n.txt0 - 3))]"
else txt0 >> 1

function checkrules(g:seq.pegrule) seq.word
let small = smallest.g
for acc = "", r ∈ g
do
 if kind.r ∉ "*+" then ""
 else
  for message = "", p ∈ parts.r
  do
   for isempty = true, last = "?" sub 1, e ∈ part.p
   while isempty
   do
    if last ∈ "!" then next(true, e)
    else
     let t = lookup(small, oneRule(e, "", true)),
     if isempty.t then next(false, e) else next(isempty.right.t sub 1, e),
   if isempty then message + "illegal rule *:(leftside.r):(part.p)/br" else message,
  acc + message,
acc

function >1(a:pegrule, b:pegrule) ordering
leftside.a >1 leftside.b ∧ kind.a ∈ "!" >1 kind.a ∈ "!"

function =(a:tableEntry, b:tableEntry) boolean
action.a = action.b ∧ Fstate.a = Fstate.b ∧ Fstate.a = Fstate.b

Function makeTbl(gin:seq.pegrule, recover:boolean) seq.tableEntry
let small = if recover then smallest.gin else empty:set.oneRule
let gset = asset.gin
for lambdas = "", r ∈ gin
do if isempty.part.(parts.r) sub 1 then lambdas + leftside.r else lambdas
for table = [tableEntry(NT.2, "?" sub 1, Match, Failure, "")], reduce0 = 2, s ∈ gin
do
 for isAll* = kind.s ∈ "*+", p ∈ parts.s while isAll* do replacement.p = "/All"
 for
  lastnextstate2 = NT
  , nextstate2 = begin.s
  , ruletable = table
  , partno = 1
  , lastpart = (parts.s) sub 1
  , p ∈ parts.s
 do
  let reduce = partno + reduce0 - 1
  for nextpart = nextstate2, e ∈ part.p do if e ∈ "!" then nextpart else nextpart + 1,
  for parttable = ruletable, thisstate = nextstate2, last = "?" sub 1, count = 1, e ∈ part.p
  do
   if e ∈ "!" then next(parttable, thisstate, e, count + 1)
   else
    let success1 =
     if count = n.part.p then
      if kind.s ∈ "!" then !Reduce
      else if replacement.p = "/All" then if kind.s ∈ "*+" then if isAll* then Discard*.begin.s else All* else All
      else if kind.s ∈ "*+" then Reduce*(reduce, begin.s)
      else Reduce.reduce
     else
      let tmp = (part.p) sub (count + 1),
      if tmp ∈ lambdas then
       for x = 2, r ∈ gin while leftside.r ≠ tmp do x + n.parts.r,
       Lambda(x, if count + 2 ≤ n.part.p then thisstate + 2 else Reduce.reduce)
      else thisstate + 1
    let failmatch =
     if n.parts.s = partno then
      if kind.s ∈ "!" then !Fail
      else if isAll* then All
      else if kind.s ∈ "*+" then Success*
      else Fail
     else if isempty.part.(parts.s) sub (partno + 1) then Reduce(reduce + 1)
     else nextpart
    for
     RecoverEnding = ""
     , last0 = "?" sub 1
     , w ∈ if recover then part.p << (count - 1) else ""
    do
     next(
      if w ∈ "!" ∨ last0 ∈ "!" then RecoverEnding
      else RecoverEnding + smallest(small, w)
      , w
     )
    let C =
     if e ∈ "any Any" then tableEntry(MatchAny, "?" sub 1, success1, failmatch, RecoverEnding)
     else
      let look = lookup(gset, pegrule(last, e, empty:seq.pegpart, 0, NT)),
      if isempty.look then
       if last ∈ "!" then tableEntry(!T, e, failmatch, success1, RecoverEnding)
       else tableEntry(T, e, success1, failmatch, RecoverEnding)
      else
       tableEntry(
        if kind.look sub 1 ∈ "*+" then NT*.begin.look sub 1 else NT.begin.look sub 1
        , leftside.look sub 1
        , success1
        , failmatch
        , RecoverEnding
       ),
    let newpt =
     if partno = 1 ∨ subseq(part.lastpart, 1, count - 1) ≠ subseq(part.p, 1, count - 1) then parttable
     else
      {look for first rule that shared prefix with current rule}
      for
       accT = empty:seq.int
       , kidx2 = index.thisstate
       , pt ∈ reverse.subseq(parts.s, 1, partno - 1)
      while subseq(part.pt, 1, count) = subseq(part.p, 1, count)
      do
       let newk = kidx2 - n.part.pt,
       next(accT + newk, newk)
      {part shares prefix with previous part so avoid backtracking. }
      if isempty.accT then
       let zidx = index.thisstate - n.part.lastpart
       let z = parttable sub zidx,
       if action.z = T then replace(parttable, zidx, tableEntry(T', match.z, Sstate.z, thisstate, recover.z))
       else if action.action.z ∈ [NT, NT*] ∧ index.action.z = index.action.C then
        let look = lookup(gset, pegrule(last, match.z, empty:seq.pegpart, 0, NT)),
        replace(parttable, zidx, tableEntry(action.z, match.z, Sstate.z, thisstate, recover.z))
       else parttable
      else if action.action.C ∉ [T, NT, NT*] then parttable
      else
       let kidx = accT sub n.accT
       let z = parttable sub kidx,
       if action.z = T then
        replace(
         parttable
         , kidx
         , if count = 1 ∨ action.action.parttable sub (kidx - 1) ∉ [NT, NT*] then tableEntry(T', match.z, Sstate.z, Fstate.C, recover.z)
         else tableEntry(T', match.z, Sstate.z, thisstate, recover.z)
        )
       else if count = n.part.p ∧ e ∈ lambdas then
        for newtbl1 = parttable, l ∈ accT
        do
         let tidx = l + 1
         let z3 = parttable sub tidx,
         replace(newtbl1, tidx, tableEntry(action.z3, match.z3, Sstate.z3, Sstate.C, recover.z3)),
        newtbl1
       else
        {action.action.z = NT}
        let newFstate = if action.Fstate.C ∈ [Idx, NT, NT*] then S'.Fstate.C else Fstate.C
        for newtbl1 = parttable, l ∈ accT
        do
         let e2 = parttable sub l,
         if index.Fstate.z = index.Fstate.e2 ∧ action.Fstate.e2 ∉ [Fail] then
          assert action.Fstate.e2 ∈ [Idx, NT, NT*, S'] report "ProBLEM:(Fstate.e2)",
          replace(
           newtbl1
           , l
           , tableEntry(
            action.e2
            , match.e2
            , Sstate.e2
            , if action.Fstate.C ∈ [Idx, NT, NT*] then S'.Fstate.C else Fstate.C
            , recover.e2
           )
          )
         else newtbl1,
        newtbl1,
    next(newpt + C, thisstate + 1, e, count + 1),
  next(nextstate2, nextpart, parttable, partno + 1, p),
 next(ruletable, reduce0 + (if kind.s ∈ "!" then 0 else n.parts.s))
for table1 = table, r ∈ gin
do
 if kind.r ∈ "+" then
  let thisrule = subseq(table1, index.begin.r, index.begin.r + nostates.r - 1),
  fixPlus(
   subseq(table1, 1, index.begin.r - 1)
   , thisrule
   , table1 << (index.begin.r + n.thisrule - 1)
  )
 else table1,
removeIdx.table1

function fixPlus(
table0:seq.tableEntry
, thisrule:seq.tableEntry
, table1:seq.tableEntry
) seq.tableEntry
{Change rule in table to handle first match and adds states to table handle following parts}
let adjust = n.thisrule + n.table1
let low = n.table0 + 1
let high = n.table0 + n.thisrule
for firstPart = table0, afterPart = table1, e ∈ thisrule
do
 let S = Sstate.e
 let newS =
  if S ∈ [Success*, All] then Fail
  else if action.S = Reduce* then Reduce*(reduceNo.S, nextState.S + adjust)
  else if action.S = Discard* then Discard*(nextState.S + adjust)
  else S
 let F = Fstate.e
 let newF = if F ∈ [Success*, All] then Fail else F
 let afterS = adjust(S, adjust, low, high),
 let afterF = adjust(F, adjust, low, high),
 next(
  firstPart + tableEntry(action.e, match.e, newS, newF, recover.e)
  , afterPart + tableEntry(action.e, match.e, afterS, afterF, recover.e)
 ),
firstPart + afterPart

function adjust(s:state, adjust:int, low:int, high:int) state
if between(index.s, low, high) then
 if action.s = Idx then s + adjust
 else if action.s = Reduce* then Reduce*(reduceNo.s, nextState.s + adjust)
 else if action.s = Discard* then Discard*(nextState.s + adjust)
 else s
else s

function removeIdx(tbl:seq.tableEntry) seq.tableEntry
for acc = empty:seq.tableEntry, e ∈ tbl
do
 acc
 + tableEntry(
  removeIdx(action.e, tbl)
  , match.e
  , removeIdx(Sstate.e, tbl)
  , removeIdx(Fstate.e, tbl)
  , recover.e
 ),
acc

function removeIdx(s:state, tbl:seq.tableEntry) state
{Remove Idx from table. The action of tableEntries will be !T T T' NT NT* or MatchAny.If Idx instruction points to the ith element in the table, it will be changed to !T.i, T.i, T'.i, NT.i, NT*.i to include the kind of the table element.The instruction S', Idx, Discard*, NT, Reduce*, also contains a pointer into the table so they also will be updated. }
if index.s = 0 ∨ action.s ∉ [S', Idx, Discard*, NT, NT*, Reduce*, Lambda] then s
else
 let tblaction = action.action.tbl sub index.s
 let action =
  if tblaction = NT then NT.index.s
  else if tblaction = NT* then NT*.index.s
  else if tblaction = T then T.index.s
  else if tblaction = MatchAny then MatchAny.index.s
  else if tblaction = T' then T'.index.s
  else
   assert tblaction = !T report "RemoveIdx Problem: Unexpected action in PEG table",
   !T.index.s,
 if action.s ∈ [S'] then if tblaction = T' then action else S'.action
 else if action.s ∈ [Idx] then if tblaction = NT then NT.action else if tblaction = NT* then NT*.action else action
 else if action.s = Discard* then Discard*.action
 else if action.s = NT then NT.action
 else if action.s = NT* then NT*.action
 else if action.s = Reduce* then Reduce*(reduceNo.s, action)
 else if action.nextState2.Lambda = Reduce then s
 else Lambda(reduceNo.s, action)

function %(p:pegpart) seq.word "/br:(part.p)"

Function replaceWords(str:seq.word, subs:seq.word) seq.word
{subs is of format w1 r1, w2 r2,... , wn rn where w1 is a word and r1 is zero or more words./br
Any occurrence of wi in str is replaced with ri /br
Note that commas cannot occur in ri /br
If wn rn contains /1 then any word w in str not eq to one of w1.. w(n-i)is replace with wn rn with the /1 replaced by w. }
for d1 = 0, d2 = 0, w ∈ reverse.subs
while w ∉ ","
do next(d1 + 1, if w ∈ "/1 $" then d1 else d2)
let z = subs << (n.subs - d1)
let zidx = d1 - d2
let subs0 = if d2 = 0 then subs + "," else subs >> d1
for acc = "", w ∈ str
do
 for w2 = [w], replace = "", matched = false, e ∈ subs0
 while not.matched
 do
  if e ∈ "," then
   if subseq(replace, 1, 1) = [w] then next(replace << 1, "", true)
   else next(w2, if isempty.replace then "," else "", false)
  else next(w2, replace + e, false),
 acc + if d2 = 0 ∨ matched then w2 else replace(z, zidx, w),
acc

Function postprocess(table:seq.tableEntry, subs:seq.word) seq.tableEntry
if isempty.subs then table
else
 for newtable = empty:seq.tableEntry, e ∈ table
 do
  newtable
  + if action.e ∈ [T, !T, T'] then
   let m = replaceWords([match.e], subs),
   if m = [match.e] then e
   else tableEntry(action.e, m sub 1, Sstate.e, Fstate.e, recover.e)
  else e,
 newtable

Function isNonTerminal(e:word, g:seq.pegrule) boolean
for isT = e ∉ "any Any" ∨ e ∈ "!", r ∈ g while isT do e ≠ leftside.r,
not.isT

Function NTcount(p:pegpart, gin:seq.pegrule) int
for count = 0, e ∈ part.p do if isNonTerminal(e, gin) then count + 1 else count,
count

Function %table(t:seq.tableEntry) seq.word
for acc = "", rowno = 1, a ∈ t
do
 next(
  acc
  + (if action.action.a = Reduce then "/br:(rowno):(action.a)/td:(Sstate.a)/td:(Fstate.a)/td:(recover.a)/td /tr"
  else "/br:(rowno):(action.a)/td:(escapeformat):([match.a]):(escapeformat)/td:(Sstate.a)/td:(Fstate.a)/td:(recover.a)/td /tr")
  , rowno + 1
 ),
 "PEG Rules:(acc)/table"

Function >1(a:state, b:state) ordering toint.a >1 toint.b

Function %(s:state) seq.word
let action = action.s,
if s = Match then "Match"
else if action = Reduce then "Reduce.:(reduceNo.s)"
else if action = Reduce* then "Reduce*(:(reduceNo.s),:(nextState.s))"
else if action = Lambda then "Lambda(:(reduceNo.s),:(nextState2.s))"
else if action = NT ∧ action.nextState.s = NT then "NT.:(index.nextState.s)"
else if action ∈ [Discard*, NT, S'] then decode.action + "." + %.nextState.s
else if index.s = 0 then decode.action
else decode.action + "." + %.index.s

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

Function action(s:state) state state.toint(bits.toint.s ∧ mask.actionBits)

Function NT(state:state) state state(NT, index.state, 0, action.state)

Function NT(index:int) state state(NT, index, 0, NT)

Function NT*(index:int) state state(NT, index, 0, NT)

Function NT*(state:state) state state(NT, index.state, 0, action.state)

Function S'(state:state) state state(S', index.state, 0, action.state)

Function T(i:int) state state(T, i)

Function T'(i:int) state state(T', i, 0, T')

Function MatchAny(i:int) state state(MatchAny, i)

Function !T(i:int) state state(!T, i)

Function Reduce(partno:int) state state(Reduce, 0, partno, state.0)

Function Reduce*(partno:int, state:state) state
state(Reduce*, index.state, partno, action.state)

Function Lambda(partno:int, state:state) state
if action.state = Reduce then state(Lambda, reduceNo.state, partno, action.state)
else state(Lambda, index.state, partno, action.state)

Function nextState(s:state) state
let k = actionBits + reduceBits,
state.toint(tobits.toint.s >> k ∧ mask.actionBits ∨ tobits.toint.s ∧ mask.k << k)

Function nextState2(s:state) state
let t = nextState.s,
if action.t = Reduce then Reduce.index.s else t

Function Discard*(state:state) state state(Discard*, index.state, 0, action.state)

function +(s:state, i:int) state state(toint.s + toint(tobits.i << shiftIndex))

Function startstate state NT.1

Function Match state Reduce

Function /All seq.word "/All"

The state T' is like T but does not rollback result on failure. Similarly actionP but does not rollback result on failure.

function genEnum seq.seq.word
["newType: state names: Failure Reduce Idx MatchAny T Fail Success* !T Discard* All Discard NT !Reduce !Fail Reduce* Lambda All* NT* S' T'"]

<<<< Below is auto generated code >>>>

type state is toint:int

Export toint(state) int

Export state(i:int) state

Export type:state

Function =(a:state, b:state) boolean toint.a = toint.b

Function Failure state state.0

Function Reduce state state.1

Function Idx state state.2

Function MatchAny state state.3

Function T state state.4

Function Fail state state.5

Function Success* state state.6

Function !T state state.7

Function Discard* state state.8

Function All state state.9

Function Discard state state.10

Function NT state state.11

Function !Reduce state state.12

Function !Fail state state.13

Function Reduce* state state.14

Function Lambda state state.15

Function All* state state.16

Function NT* state state.17

Function S' state state.18

Function T' state state.19

Function decode(code:state) seq.word
let discard =
 [
  Failure
  , Reduce
  , Idx
  , MatchAny
  , T
  , Fail
  , Success*
  , !T
  , Discard*
  , All
  , Discard
  , NT
  , !Reduce
  , !Fail
  , Reduce*
  , Lambda
  , All*
  , NT*
  , S'
  , T'
 ]
let i = toint.code,
if between(i, 0, 19) then
 let r =
  [
   "Failure Reduce Idx MatchAny T Fail Success* !T Discard* All Discard NT !Reduce !Fail Reduce* Lambda All* NT* S' T'"
   sub (i + 1)
  ],
 if r ≠ "?" then r else "state." + toword.i
else "state." + toword.i 