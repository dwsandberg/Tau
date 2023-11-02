Module PEGrules

use UTF8

use bits

use otherseq.int

use seq.int

use otherseq.pegpart

use seq.pegpart

use otherseq.pegrule

use seq.pegrule

use set.pegrule

use standard

use seq.state

use seq.t5

use set.t5

use otherseq.tableEntry

use seq.tableEntry

use otherseq.word

use otherseq.seq.word

use set.word

Export pegrule(word, word, seq.pegpart, int, state) pegrule

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
  for eZ = pZ, e!Z = p!Z, last = 1#"?", e ∈ part.p
  do
   if e ∈ "!" then
   next(eZ, e!Z, e)
   else if last ∈ "!" then
   next(eZ, e!Z + e, e)
   else next(eZ + e, e!Z, e),
  next(eZ, e!Z)
 assert leftside.r ∉ NonT ∪ NonT*
 report "Duplicate Non-Terminal:^(leftside.r)^(%(2, g))"
 let noStates = n.pZ + n.p!Z
 let newg = newg1 + pegrule(kind.r, leftside.r, parts.r, noStates, begin),
  if kind.r ∈ "*+" then
  next(rZ ∪ asset.pZ, r!Z ∪ asset.p!Z, NonT, NonT* + leftside.r, begin + noStates, newg)
  else next(rZ ∪ asset.pZ, r!Z ∪ asset.p!Z, NonT + leftside.r, NonT*, begin + noStates, newg)
assert isempty(r!Z ∩ NonT*) report "cannot use ! on * Non-terminal"
let NonT! = NonT ∩ r!Z
let NonTAdd = NonT! ∩ rZ
let NonTchange = NonT! \ NonTAdd
for acc = empty:seq.pegrule, add = empty:seq.pegrule, r ∈ newg1
do
 if leftside.r ∈ NonTchange then
 next(acc + pegrule(1#"!", leftside.r, parts.r, nostates.r, begin.r), add)
 else if leftside.r ∈ NonTAdd then
 next(acc, add + r)
 else next(acc + r, add)
assert isempty.add
report "???? PEG grammar not implemented using same non-terminal with ! and without !",
acc

Function smallest(costs:set.t5, w:word) seq.word
let l = lookup(costs, t5(w, "")),
if isempty.l then [w] else right.1#l

function smallest(rules:seq.pegrule) set.t5
let gram = removelambda(rules, "")
for t1 = empty:set.t5, r ∈ gram do t1 + t5(leftside.r, "")
for t2 = BB(gram, t1), r ∈ rules do t2 + t5(leftside.r, ""),
t2

function BB(gram:seq.pegrule, costsin:set.t5) set.t5
for acc = empty:seq.pegrule, costs = costsin, r ∈ gram
do
 let p =
  for minpart = "", min = {????} 10, p ∈ parts.r
  do
   for R = "X", w ∈ part.p
   while not.isempty.R
   do
    let l = lookup(costs, t5(w, "")),
    if isempty.l then R + w else if isempty.right.1#l then "" else R + right.1#l,
   if isempty(R << 1) then next(minpart, min(n.part.p, min)) else next(R << 1, min),
  if between(n.minpart, 1, min) then minpart else "",
  if isempty.p then
  next(acc + r, costs)
  else next(acc, asset.[t5(leftside.r, p)] ∪ costs),
if n.gram = n.acc then
assert isempty.acc report "PROBLEM BB^(acc)", costs
else BB(acc, costs)

type t5 is N:word, right:seq.word

function >1(a:t5, b:t5) ordering N.a >1 N.b

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
 for acc = "", last = 1#"?", w ∈ part.p
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

type pegrule is kind:word, leftside:word, parts:seq.pegpart, nostates:int, begin:state

Function changeParts(r:pegrule, parts:seq.pegpart) pegrule
pegrule(kind.r, leftside.r, parts, nostates.r, begin.r)

Export kind(pegrule) word

Export leftside(pegrule) word

Export type:pegpart

Export parts(pegrule) seq.pegpart

Export part(pegpart) seq.word

Export replacement(pegpart) seq.word

Export begin(pegrule) state

Export pegpart(part:seq.word, replacement:seq.word) pegpart

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
for Non = empty:set.word, rightsides = "", r ∈ g
do for parts = "", e ∈ parts.r do parts + part.e, next(Non + leftside.r, rightsides + parts)
let terms = asset.rightsides \ Non \ asset."/ ! /br"
let unusedNon = toseq(Non \ asset.rightsides - leftside.1#g),
checkrules.g
 + (if isempty.unusedNon then "" else "/br Unused non-terminals:^(unusedNon)")
 + "/br Non-terminals:^(alphasort.toseq.Non) /br Terminals:^(alphasort.toseq.terms)"
 + %(5, g)

Function %(format:int, newg:seq.pegrule) seq.word
{1 as string 2-as table 3-as table with action 4-as txt 6-as code}
let action = format#["/action", "", "/cell", "", "", dq + "="]
let part = format#["/br /", "/row /cell", "/row /cell", "/", "/", "/br,^(dq) /"]
let rule =
 format
 #[
  "/br"
  , "/row"
  , "/row"
  , "/br^(escapeformat) /br^(escapeformat)"
  , "/br"
  , "/br,^(dq)"
 ]
let arrow = format#["", "/cell", "/cell", "←", "←", ""]
for txt0 = "", r ∈ newg
do
 for txt1 = "", e ∈ parts.r
 do txt1 + (part.e + action + (if isempty.action then "" else replacement.e) + part),
  txt0 >> n.part
   + (rule + (if kind.r ∈ "*+" then [kind.r] else "") + %.leftside.r + arrow + txt1),
if format ∈ [2, 3] then
"<* table /row left /cell right /cell action^(txt0) *>"
else if format = 4 then
"function genPEG (attributeType:word) seq.boolean [^(subseq(txt0, 3, n.txt0 - 3))]"
else txt0 >> 1

function checkrules(g:seq.pegrule) seq.word
let small = smallest.g
for acc = "", r ∈ g
do
 if kind.r ∉ "*+" then
 ""
 else
  for message = "", p ∈ parts.r
  do
   for isempty = true, last = 1#"?", e ∈ part.p
   while isempty
   do
    if last ∈ "!" then
    next(true, e)
    else
     let t = lookup(small, t5(e, "")),
     if isempty.t then next(false, e) else next(isempty.right.1#t, e),
   if isempty then message + "illegal rule *^(leftside.r)^(part.p) /br" else message,
  acc + message,
acc

function goallength int 1

function >1(a:pegrule, b:pegrule) ordering
leftside.a >1 leftside.b ∧ kind.a ∈ "!" >1 kind.a ∈ "!"

function =(a:tableEntry, b:tableEntry) boolean
action.a = action.b ∧ Fstate.a = Fstate.b ∧ Fstate.a = Fstate.b

Function makeTbl(gin:seq.pegrule, recover:boolean) seq.tableEntry
let small = if recover then smallest.gin else empty:set.t5
let gset = asset.gin
for lambdas = "", r ∈ gin do if isempty.part.1#parts.r then lambdas + leftside.r else lambdas
for table = [tableEntry(NT.2, 1#"?", Match, Failure, "")], reduce0 = 2, s ∈ gin
do
 for isAll* = kind.s ∈ "*+", p ∈ parts.s while isAll* do replacement.p = "/All"
 for
  lastnextstate2 = NT
  , nextstate2 = begin.s
  , ruletable = table
  , partno = 1
  , lastpart = 1#parts.s
  , p ∈ parts.s
 do
  let reduce = partno + reduce0 - 1
  for nextpart = nextstate2, e ∈ part.p do if e ∈ "!" then nextpart else nextpart + 1
  for parttable = ruletable, thisstate = nextstate2, last = 1#"?", count = 1, e ∈ part.p
  do
   if e ∈ "!" then
   next(parttable, thisstate, e, count + 1)
   else
    let success1 =
     if count = n.part.p then
      if kind.s ∈ "!" then
      !Reduce
      else if replacement.p = "/All" then
      if kind.s ∈ "*+" then if isAll* then Discard*.begin.s else All* else All
      else if kind.s ∈ "*+" then
      Reduce*(reduce, begin.s)
      else Reduce.reduce
     else
      let tmp = (count + 1)#part.p,
       if tmp ∈ lambdas then
        for x = 2, r ∈ gin while leftside.r ≠ tmp do x + n.parts.r,
        Lambda(x, if count + 2 ≤ n.part.p then thisstate + 2 else Reduce.reduce)
       else thisstate + 1
    let failmatch =
     if n.parts.s = partno then
      if kind.s ∈ "!" then
      !Fail
      else if isAll* then
      All
      else if kind.s ∈ "*+" then
      Success*
      else Fail
     else if isempty.part.(partno + 1)#parts.s then
     Reduce(reduce + 1)
     else nextpart
    for RecoverEnding = "", last0 = 1#"?", w ∈ if recover then part.p << (count - 1) else ""
    do next(
     if w ∈ "!" ∨ last0 ∈ "!" then RecoverEnding else RecoverEnding + smallest(small, w)
     , w
    )
    let C =
     if e ∈ "any Any" then
     tableEntry(MatchAny, 1#"?", success1, failmatch, RecoverEnding)
     else
      let look = lookup(gset, pegrule(last, e, empty:seq.pegpart, 0, NT)),
       if isempty.look then
        if last ∈ "!" then
        tableEntry(!T, e, failmatch, success1, RecoverEnding)
        else tableEntry(T, e, success1, failmatch, RecoverEnding)
       else tableEntry(
        if kind.1#look ∈ "*+" then NT*.begin.1#look else NT.begin.1#look
        , leftside.1#look
        , success1
        , failmatch
        , RecoverEnding
       )
    let newpt =
     if partno = 1 ∨ subseq(part.lastpart, 1, count - 1) ≠ subseq(part.p, 1, count - 1) then
     parttable
     else
      {look for first rule that shared prefix with current rule}
      for accT = empty:seq.int, kidx2 = index.thisstate, pt ∈ reverse.subseq(parts.s, 1, partno - 1)
      while subseq(part.pt, 1, count) = subseq(part.p, 1, count)
      do let newk = kidx2 - n.part.pt, next(accT + newk, newk)
      {part shares prefix with previous part so avoid backtracking. }
       if isempty.accT then
        let zidx = index.thisstate - n.part.lastpart
        let z = zidx#parttable,
         if action.z = T then
         replace(parttable, zidx, tableEntry(T', match.z, Sstate.z, thisstate, recover.z))
         else if action.action.z ∈ [NT, NT*] ∧ index.action.z = index.action.C then
          let look = lookup(gset, pegrule(last, match.z, empty:seq.pegpart, 0, NT))
          assert not.isempty.look ∧ kind.1#look ∈ "d" report "SDF HHHH" + match.z,
          replace(parttable, zidx, tableEntry(action.z, match.z, Sstate.z, thisstate, recover.z))
         else parttable
       else if action.action.C ∉ [T, NT, NT*] then
       parttable
       else
        let kidx = 1^accT
        let z = kidx#parttable,
         if action.z = T then
         replace(
          parttable
          , kidx
          , if count = 1 ∨ action.action.(kidx - 1)#parttable ∉ [NT, NT*] then
           tableEntry(T', match.z, Sstate.z, Fstate.C, recover.z)
           else tableEntry(T', match.z, Sstate.z, thisstate, recover.z)
         )
         else if count = n.part.p ∧ e ∈ lambdas then
          for newtbl1 = parttable, l ∈ accT
          do
           let tidx = l + 1
           let z3 = tidx#parttable,
           replace(newtbl1, tidx, tableEntry(action.z3, match.z3, Sstate.z3, Sstate.C, recover.z3)),
          newtbl1
         else
          {action.action.z = NT}
          let newFstate = if action.Fstate.C ∈ [Idx, NT, NT*] then S'.Fstate.C else Fstate.C
          for newtbl1 = parttable, l ∈ accT
          do
           let e2 = l#parttable,
            if index.Fstate.z = index.Fstate.e2 ∧ action.Fstate.e2 ∉ [Fail] then
             assert action.Fstate.e2 ∈ [Idx, NT, NT*, S'] report "ProBLEM^(Fstate.e2)",
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
 next(ruletable, reduce0 + if kind.s ∈ "!" then 0 else n.parts.s)
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
debug(removeIdx.table1, gin)

function debug(table2:seq.tableEntry, gin:seq.pegrule) seq.tableEntry
assert true ∨ leftside.1#gin ∉ "Parser"
report
 for begin* = empty:set.range, r ∈ gin
 do
  if kind.r ∈ "*+" then
  begin* + range(leftside.r, index.begin.r, index.begin.r + nostates.r - 1)
  else begin*
 for all = "", place = 1, e ∈ table2
 do next(
  all
   + "/row^(place)"
   + check(action.e, begin*, place)
   + check(Sstate.e, begin*, place)
   + check(Fstate.e, begin*, place)
  , place + 1
 ),
 %.toseq.begin* + "<* table^(all) *>",
table2

type range is left:word, start:int, stop:int

function >1(a:range, b:range) ordering start.a >1 start.b

use set.range

use otherseq.range

function %(a:range) seq.word %.left.a + %.start.a + %.stop.a

function check(e:state, begin*:set.range, place:int) seq.word
let n = lookup(begin*, range(1#"?", index.e, 0)),
"/cell^(e)^(if isempty.n ∨ between(place, start.1#n, stop.1#n) then "" else "%")"

use otherseq.state

use set.state

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
  if S ∈ [Success*, All] then
  Fail
  else if action.S = Reduce* then
  Reduce*(reduceNo.S, nextState.S + adjust)
  else if action.S = Discard* then
  Discard*(nextState.S + adjust)
  else S
 let F = Fstate.e
 let newF = if F ∈ [Success*, All] then Fail else F
 let afterS = adjust(S, adjust, low, high)
 let afterF = adjust(F, adjust, low, high),
 next(
  firstPart + tableEntry(action.e, match.e, newS, newF, recover.e)
  , afterPart + tableEntry(action.e, match.e, afterS, afterF, recover.e)
 ),
firstPart + afterPart

function adjust(s:state, adjust:int, low:int, high:int) state
if between(index.s, low, high) then
 if action.s = Idx then
 s + adjust
 else if action.s = Reduce* then
 Reduce*(reduceNo.s, nextState.s + adjust)
 else if action.s = Discard* then
 Discard*(nextState.s + adjust)
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
{Remove Idx from table. The action of tableEntries will be !T T T' NT NT* or MatchAny.If Idx
instruction points to the ith element in the table, it will be changed to !T.i, T.i, T'.i
, NT.i, NT*.i to include the kind of the table element.The instruction S', Idx, Discard*,
NT, Reduce*, also contains a pointer into the table so they also will be updated. }
if index.s = 0 ∨ action.s ∉ [S', Idx, Discard*, NT, NT*, Reduce*, Lambda] then
s
else
 let tblaction = action.action.(index.s)#tbl
 let action =
  if tblaction = NT then
  NT.index.s
  else if tblaction = NT* then
  NT*.index.s
  else if tblaction = T then
  T.index.s
  else if tblaction = MatchAny then
  MatchAny.index.s
  else if tblaction = T' then
  T'.index.s
  else
   assert tblaction = !T report "RemoveIdx Problem: Unexpected action in PEG table",
   !T.index.s,
  if action.s ∈ [S'] then
  if tblaction = T' then action else S'.action
  else if action.s ∈ [Idx] then
  if tblaction = NT then NT.action else if tblaction = NT* then NT*.action else action
  else if action.s = Discard* then
  Discard*.action
  else if action.s = NT then
  NT.action
  else if action.s = NT* then
  NT*.action
  else if action.s = Reduce* then
  Reduce*(reduceNo.s, action)
  else if action.nextState2.Lambda = Reduce then
  s
  else Lambda(reduceNo.s, action)

function %(p:pegpart) seq.word "/br^(part.p)"

Function replaceWords(str:seq.word, subs:seq.word) seq.word
{subs is of format w1 r1, w2 r2,... , wn rn where w1 is a word and r1 is zero or more words.
/br Any occurrence of wi in str is replaced with ri
/br Note that commas cannot occur in ri
/br If wn rn contains /1 then any word w in str not eq to one of w1.. w (n-i) is replace
with wn rn with the /1 replaced by w. }
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
   if subseq(replace, 1, 1) = [w] then
   next(replace << 1, "", true)
   else next(w2, if isempty.replace then "," else "", false)
  else next(w2, replace + e, false),
 acc + if d2 = 0 ∨ matched then w2 else replace(z, zidx, w),
acc

Function postprocess(table:seq.tableEntry, subs:seq.word) seq.tableEntry
if isempty.subs then
table
else
 for newtable = empty:seq.tableEntry, e ∈ table
 do
  newtable
   + 
   if action.e ∈ [T, !T, T'] then
    let m = replaceWords([match.e], subs),
    if m = [match.e] then e else tableEntry(action.e, 1#m, Sstate.e, Fstate.e, "")
   else e,
 newtable

Function isNonTerminal(e:word, g:seq.pegrule) boolean
for isT = e ∉ "any Any" ∨ e ∈ "!", r ∈ g while isT do e ≠ leftside.r,
not.isT

Function NTcount(p:pegpart, gin:seq.pegrule) int
for count = 0, e ∈ part.p do if isNonTerminal(e, gin) then count + 1 else count,
count

function esc(w:word) seq.word
if w ∈ "/cell /row <* *> /em /strong /p" then
%.escapeformat + %.w + %.escapeformat
else [w]

Function %table(t:seq.tableEntry) seq.word
for acc = "", rowno = 1, a ∈ t
do next(
 acc
  + 
  if action.action.a = Reduce then
  "/row^(rowno)^(action.a) /cell /cell^(Sstate.a) /cell^(Fstate.a)"
  else "
  /row^(rowno)^(action.a) /cell^(escapeformat)^([match.a])^(escapeformat) /cell
  ^(Sstate.a) /cell^(Fstate.a)"
 , rowno + 1
),
"<* table^(acc) *>"

function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Function >1(a:state, b:state) ordering toint.a >1 toint.b

let m = (mask (reduceBits) << (reduceBits+actionBits)) ⊻ tobits.-1 toint (tobits.toint.a /and m) >1
toint (tobits.toint.b /and m)

Function %(s:state) seq.word
let action = action.s,
if s = Match then
"Match"
else if action = Reduce then
"Reduce.^(reduceNo.s)"
else if action = Reduce* then
"Reduce* (^(reduceNo.s),^(nextState.s))"
else if action = Lambda then
"Lambda (^(reduceNo.s),^(nextState2.s))"
else if action = NT ∧ action.nextState.s = NT then
"NT.^(index.nextState.s)"
else if action ∈ [Discard*, NT, S'] then
decode.action + "." + %.nextState.s
else if index.s = 0 then
decode.action
else decode.action + "." + %.index.s

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
if action.state = Reduce then
state(Lambda, reduceNo.state, partno, action.state)
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

The state T' is like T but does not rollback result on failure. Similarly actionP but does not rollback
result on failure.

function genEnum seq.seq.word
["newType = state values = Failure Reduce Idx MatchAny T Fail Success* !T Discard* All Discard NT
!Reduce !Fail Reduce* Lambda All* NT* S' T'"]

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
let discard = [
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
if between(i + 1, 1, 20) then
 let r = [
  (i + 1)
  #"Failure Reduce Idx MatchAny T Fail Success* !T Discard* All Discard NT !Reduce !Fail Reduce* Lambda
  All* NT* S' T'"
 ],
 if r ≠ "?" then r else "state." + toword.i
else "state." + toword.i 