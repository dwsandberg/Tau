Module mergeblocks

use otherseq.int

use set.int

use stack.int

use mergeblocks

use standard

use symbol

use seq.symbol

use otherseq.seq.symbol

use seq.seq.symbol

use symbol2

use set.symdef

use otherseq.word

Function noDebug boolean false

function reduceBr(code:seq.symbol, t:int, f:int) seq.symbol
if isempty.code then
 [Br2(t, f)]
else
 let last = last.code
 if last = NotOp then
  reduceBr(code >> 1, f, t)
 else if last = Littrue then
  code + Br2(t, t)
 else if last = Litfalse then code + Br2(f, f) else code + Br2(t, f)

Function mergeblocks(code:seq.symbol, self:symbol) seq.symbol
for partstart = 1
 , parts = empty:seq.seq.symbol
 , skip = false
 , idx = 1
 , sy ∈ code
do
 if isstartorloop.sy ∨ isExit.sy ∨ isbr.sy ∨ iscontinue.sy then
  let thispart = 
   if isbr.sy then
    reduceBr(subseq(code, partstart, idx - 1), brt.sy, brf.sy)
   else
    subseq(code, partstart, idx)
  next(idx + 1
   , if skip then
    parts
   else if not.isempty.parts ∧ last.last.parts = Words."MORE" then
    parts >> 1 + (last.parts >> 1 + thispart)
   else
    parts + thispart
   , false
   , idx + 1)
 else if sy ≠ EndBlock then
  next(partstart, parts, false, idx + 1)
 else
  let lookAhead = if idx < length.code then code_(idx + 1) else Lit.0
  let lp = laststart.parts
  if lookAhead ∈ [Exit, EndBlock] ∧ isstart.last.parts_lp then
   let endpart = [parts_lp >> 1 + parts_(lp + 1)] + parts << (lp + 1)
   let adjustpart = parts >> (length.endpart + 1)
   next(idx + 1, adjust(adjustpart, endpart), isExit.lookAhead, idx + 1)
  else if isbr.lookAhead ∧ isstart.last.parts_lp then
   let br = code_(idx + 1)
   let replaceExit = 
    for acc = empty:seq.seq.symbol
     , amount = 0
     , map = empty:seq.int
     , p ∈ reverse(parts << lp)
    do
     if length.p = 2 ∧ isExit.last.p ∧ first.p ∈ [Littrue, Litfalse] then
      next(acc, amount, [amount + if first.p = Littrue then brt.br else brf.br] + map)
     else if last.p = EndBlock then
      next([p] + acc, amount + 1, [0] + map)
     else
      let newend = 
       if isExit.last.p then
        Br2(brt.br + amount, brf.br + amount)
       else
        assert noDebug ∨ isbr.last.p report "Fail merge $(last.p) $(%n.parts)"
        Br2(newTarget(map, brt.last.p), newTarget(map, brf.last.p))
      next([p >> 1 + newend] + acc, amount + 1, [0] + map)
    /for (acc)
   let endpart = [parts_lp >> 1 + first.replaceExit] + replaceExit << 1
   let adjustpart = parts >> (length.parts - lp + 1)
   next(idx + 1, adjust(adjustpart, endpart), true, idx + 1)
  else
   let partstomerge = parts << (laststart.parts - 1)
   let atend = if idx = length.code ∧ lp = 1 ∧ isstart.last.parts_lp then self else Lit.0
   let newparts = parts >> length.partstomerge + (parts2code(partstomerge, atend) + Words."MORE")
   next(idx + 1, newparts, false, idx + 1)
/for (
 if isempty.parts then
  code
 else
  assert noDebug ∨ length.parts = 1 report "XXX"
  first.parts >> 1 + subseq(code, partstart, length.code)
)

function parts2code(parts:seq.seq.symbol, self:symbol) seq.symbol
assert noDebug ∨ length.parts > 2 ∧ isstartorloop.last.first.parts ∧ isbr.last.parts_2
report "FAIL merge 1"
let x = parts_2_(length.parts_2 - 1)
if x ∈ [Littrue, Litfalse] then
 let target = 2 + if x = Littrue then brt.last.parts_2 else brf.last.parts_2
 let combined = parts_2 >> 2 + parts_target
 if isExit.last.parts_target then
  parts_1 >> 1 + combined >> 1
 else
  parts2code([parts_1] + combined + parts << target, self)
else
 let removeTailR = not.isconst.self ∧ isstart.last.first.parts
 for used = empty:set.int
  , pass = empty:set.int
  , cnt = 1
  , tailR = empty:set.int
  , p ∈ parts
 do
  if isbr.last.p ∧ (cnt = 2 ∨ cnt ∈ used) then
   if length.p = 2 ∧ first.p = Littrue then
    next(used + (brt.last.p + cnt), pass + cnt, cnt + 1, tailR)
   else if length.p = 2 ∧ first.p = Litfalse then
    next(used + (brf.last.p + cnt), pass + cnt, cnt + 1, tailR)
   else
    next(used + (brt.last.p + cnt) + (brf.last.p + cnt), pass, cnt + 1, tailR)
  else if removeTailR ∧ isExit.last.p ∧ self = p_(length.p - 1) then
   next(used, pass, cnt + 1, tailR + cnt)
  else
   next(used, pass, cnt + 1, tailR)
 /for (
  if cardinality.used = length.parts - 2 ∧ isempty.tailR then
   for acc = empty:seq.symbol, p2 ∈ parts do acc + p2 /for (acc + EndBlock)
  else if toseq.pass = [2] ∧ cardinality.used = 1 ∧ isstart.last.first.parts then
   parts_1 >> 1 + parts_(used_1) >> 1
  else
   let map = 
    for acc = [1, 2], adjust = 0, i ∈ toseq(used \ pass) do
     let diff = i - length.acc - 1
     next(acc + constantseq(diff, 0) + [i - adjust - diff], adjust + diff)
    /for (acc)
   for acc = empty:seq.symbol, count = 2, p2 ∈ subseq(parts, 2, length.map) do
    let newpos = map_count
    if newpos = 0 then
     next(acc, count + 1)
    else
     let endsym = last.p2
     if not.isbr.endsym then
      if count ∈ tailR then
       next(acc + (p2 >> 2 + continue.nopara.self), count + 1)
      else
       next(acc + p2, count + 1)
     else
      let t = map_followpass(brt.endsym + count, pass, parts) - newpos
      let f = map_followpass(brf.endsym + count, pass, parts) - newpos
      if t = brt.endsym ∧ f = brf.endsym then
       next(acc + p2, count + 1)
      else
       next(acc + (p2 >> 1 + Br2(t, f)), count + 1)
   /for (
    if isempty.tailR then
     first.parts + acc + EndBlock
    else
     {finish up removing tail Recursion}
     for plist = empty:seq.symbol, e2 ∈ arithseq(nopara.self, 1, 1) do
      plist + Local.e2
     /for (
      assert noDebug ∨ isstart.last.first.parts report "FAIL Merge 2 $(parts)"
      plist + Loopblock(paratypes.self, nopara.self + 1, resulttype.self)
      + adjustvar(first.parts >> 1 + acc, nopara.self)
      + EndBlock
     )
   )
 )

function adjustvar(s:seq.symbol, delta:int) seq.symbol
for acc = empty:seq.symbol, a ∈ s do
 if islocal.a then
  acc + Local(value.a + delta)
 else if isdefine.a then
  acc + Define(value.a + delta)
 else if isloopblock.a then
  acc + Loopblock(paratypes.a, firstvar.a + delta, resulttype.a)
 else
  acc + a
/for (acc)

function followpass(i:int, pass:set.int, parts:seq.seq.symbol) int
if i ∉ pass then
 i
else
 let p = parts_i
 followpass(i + if first.p = Littrue then brt.p_2 else brf.p_2, pass, parts)

function newTarget(map:seq.int, t:int) int
let tmp = map_t
for acc = if tmp = 0 then 1 else map_t, e ∈ subseq(map, 1, t - 1) do
 if e = 0 then acc + 1 else acc
/for (acc)

function laststart(parts:seq.seq.symbol) int
for acc = length.parts, e ∈ reverse.parts while not.isstartorloop.last.e do acc - 1 /for (acc)

function adjust(parts:seq.seq.symbol, endpart:seq.seq.symbol) seq.seq.symbol
let amount = length.endpart - 1
for acc = empty:seq.seq.symbol, jumppast = 2, p ∈ reverse.parts
while not.isstartorloop.last.p
do
 let b = last.p
 let adjustBr = 
  if isbr.b then
   let t = if brt.b < jumppast then 0 else amount
   let f = if brf.b < jumppast then 0 else amount
   if t + f = 0 then p else p >> 1 + Br2(brt.b + t, brf.b + f)
  else
   p
 next([adjustBr] + acc, jumppast + 1)
/for (parts >> length.acc + acc + endpart)

function countnodes2(s:stack.int) int
if top.s = 2 then 1 else 1 + countnodes2.pop.s

Function valid(s:seq.symbol) boolean
for valid = true, stk = empty:stack.int, sym ∈ s
while valid
do
 if isblock.sym then
  let noblocks = countnodes2.stk
  next(top.stk ≤ noblocks, pop(stk, noblocks))
 else if isbr.sym then
  let blkno = countnodes2.stk + 1
  next(brt.sym > 0 ∧ brf.sym > 0
   , push(stk, max(blkno + max(brt.sym, brf.sym), top.stk)))
 else if isExit.sym ∨ iscontinue.sym then
  next(valid, push(stk, top.stk))
 else if isstartorloop.sym then next(valid, push(stk, 2)) else next(valid, stk)
/for (valid) 