Module newanal

use otherseq.arc.int

use set.arc.int

use graph.int

use otherseq.int

use set.int

use seq.mytype

use standard

use stack.stkele

use symbol

use otherseq.symbol

use otherseq.seq.symbol

use symbol2

function adjustvar(s:seq.symbol, delta:int) seq.symbol
for acc = empty:seq.symbol, a ∈ s
do
 if islocal.a then
 acc + Local(value.a + delta)
 else if isdefine.a then
 acc + Define(value.a + delta)
 else if isloopblock.a then
 acc + Loopblock(paratypes.a, firstvar.a + delta, resulttype.a)
 else acc + a,
acc

Function checkLoopIsNoOp(syms:seq.symbol, parts:seq.seq.symbol) seq.symbol
let prior = syms >> 1
let loop = 1^syms,
if
 n.parts = 3
 ∧ n.3_parts ∈ [13, 14]
 ∧ 2_parts = [Lit.0, Exit]
 ∧ nopara.loop = 2
 ∧ prior << (n.prior - 1) = [Lit.0]
 ∧ isseq.1_paratypes.loop
then
 let lastpart = 3_parts
 let theseqtype = resulttype.3^lastpart
 let theseq = 5_lastpart,
  if %.parameter.theseqtype ∈ ["packed2", "ptr"] then
  {???? hack! should at least check to see if cat is defined.} empty:seq.symbol
  else
   let firstvar = firstvar.loop
   let idx = firstvar + 1
   let seqlen =
    if isrecordconstant.theseq then
    Lit.nopara.1^fullconstantcode.theseq
    else if iswords.theseq then
    Lit.n.worddata.theseq
    else Local(firstvar - 1)
   let symidx = 7_lastpart,
    if nopara.symidx ≠ 2 then
    empty:seq.symbol
    else
     let idxNB = symbol(internalmod, "idxNB", paratypes.symidx, resulttype.symidx)
     let cat =
      if n.lastpart = 14 then
      [
       Sequence(resulttype.symidx, 1)
       , symbol(moduleref("* seq", parameter.theseqtype), "+", theseqtype, theseqtype, theseqtype)
      ]
      else [symbol(moduleref("* seq", parameter.theseqtype), "+", theseqtype, parameter.theseqtype, theseqtype)]
     let matchbrf =
      [
       Local(firstvar + 1)
       , Lit.1
       , PlusOp
       , Define(firstvar + 2)
       , theseq
       , Local(firstvar + 2)
       , idxNB
       , Define(firstvar + 3)
       , Local.firstvar
       , Local(firstvar + 3)
      ]
      + cat
      + [Local(firstvar + 2), continue.2],
      if [Local.idx, seqlen, EqOp] = 1_parts >> 1 ∧ lastpart = matchbrf then
       let newsyms =
        if prior << (n.prior - 3) = [GetSeqLength, Define(firstvar.loop - 1), Lit.0] then
        syms >> 4
        else empty:seq.symbol,
        if isempty.newsyms then
        empty:seq.symbol
        else
         newsyms
         + symbol(moduleref("* seq", parameter.theseqtype), "+", theseqtype, theseqtype, theseqtype)
         + Define.firstvar
         + Lit.0
      else empty:seq.symbol
else empty:seq.symbol

type stkele is part:seq.symbol, blkparts:seq.seq.symbol

Function newanal(ss:seq.symbol, self:symbol) seq.symbol
let EndMark = symbol(internalmod, "endmark", typeint)
for
 part = empty:seq.symbol
 , blkparts = empty:seq.seq.symbol
 , stk = empty:stack.stkele
 , sym = Lit.0
 , ahead ∈ ss + if isconst.self then Lit.0 else EndMark
do
 if not.isspecial.sym then
 next(part + sym, blkparts, stk, ahead)
 else if iscontinue.sym ∨ isExit.sym then
 next(empty:seq.symbol, blkparts + (part + sym), stk, ahead)
 else if isstartorloop.sym then
 next(empty:seq.symbol, empty:seq.seq.symbol, push(stk, stkele(part + sym, blkparts)), ahead)
 else if isbr.sym then
  let newpart =
   if 1^part = NotOp then
   part >> 1 + Br2(brf.sym, brt.sym)
   else part + Br2(brt.sym, brf.sym),
  next(empty:seq.symbol, blkparts + newpart, stk, ahead)
 else if sym = EndBlock then
  let blockheader = 1^part.top.stk
  let nonLoop = isstart.blockheader
  let checkNoOp =
   if not.nonLoop ∧ nopara.blockheader = 2 then
   checkLoopIsNoOp(part.top.stk, blkparts)
   else empty:seq.symbol,
   if not.isempty.checkNoOp then
   next(checkNoOp, blkparts.top.stk, pop.stk, ahead)
   else if 1^1_blkparts = Exit ∧ nonLoop then
    {remove block with just one Exit}
    next(part.top.stk >> 1 + 1_blkparts >> 1, blkparts.top.stk, pop.stk, ahead)
   else if ahead = Exit ∧ nonLoop then
    {combine current block with outer block}
    let tmp2 =
     adjustbr(blkparts.top.stk, n.blkparts)
     + [part.top.stk >> 1 + 1_blkparts]
     + blkparts << 1,
    next(1^tmp2 >> 1, tmp2 >> 1, pop.stk, 1^1^tmp2)
   else if isbr.ahead ∧ nonLoop then
    {combine boolean block with outer block}
    for partsA = empty:seq.seq.symbol, brt = brt.ahead, brf = brf.ahead, p ∈ reverse.blkparts
    do
     let p1 = if 1^p = Exit then p >> 1 + Br2(brt, brf) else p,
     next([p1] + partsA, brt + 1, brf + 1)
    let tmp2 =
     adjustbr(blkparts.top.stk, n.blkparts)
     + [part.top.stk >> 1 + 1_partsA]
     + partsA << 1,
    next(1^tmp2 >> 1, tmp2 >> 1, pop.stk, 1^1^tmp2)
   else
    let recursive =
     if nonLoop ∧ ahead = EndMark then
     checkrecursive(blkparts, self, part.top.stk)
     else empty:seq.symbol,
     if not.isempty.recursive then
     next(recursive, blkparts.top.stk, pop.stk, ahead)
     else next(blocktocode(part.top.stk, blkparts), blkparts.top.stk, pop.stk, ahead)
 else next(part + sym, blkparts, stk, ahead),
part << 1

function checkrecursive(parts:seq.seq.symbol, self:symbol, stkpart:seq.symbol) seq.symbol
let nopara = nopara.self
for changed = false, acc = empty:seq.seq.symbol, p ∈ parts
do
 if 1^p = Exit ∧ 2^p = self then
  let newacc =
   if changed then
   acc
   else for acc2 = empty:seq.seq.symbol, p2 ∈ acc do acc2 + adjustvar(p2, nopara), acc2,
  next(true, newacc + adjustvar(p >> 2 + continue.nopara, nopara))
 else next(changed, acc + if changed then adjustvar(p, nopara) else p),
if changed then
 for pvar = empty:seq.symbol, i ∈ arithseq(nopara.self, 1, 1) do pvar + Local.i,
  [Lit.0]
  + pvar
  + Loopblock(paratypes.self, nopara + 1, resulttype.self)
  + adjustvar(subseq(stkpart, 2, n.stkpart - 1), nopara)
  + blocktocode(empty:seq.symbol, acc)
else empty:seq.symbol

function adjustbr(parts:seq.seq.symbol, amount:int) seq.seq.symbol
{adjust branches that jump after what has been processed in outer block}
for tmp = parts, place = 1, e ∈ parts
do
 let x = 1^e,
  if isbr.x then
   let adjustt = if brt.x + place > n.tmp + 1 then amount - 1 else 0
   let adjustf = if brf.x + place > n.tmp + 1 then amount - 1 else 0,
    if adjustt + adjustf ≠ 0 then
    next(replace(tmp, place, e >> 1 + Br2(brt.x + adjustt, brf.x + adjustf)), place + 1)
    else next(tmp, place + 1)
  else next(tmp, place + 1),
tmp

/function %kind (i:seq.int) seq.word for acc ="", e /in i do acc+if e = 0 /or e > 4 then %.e else
[e_" same sameMore unreachable run"] acc

function blocktocode(result:seq.symbol, parts:seq.seq.symbol) seq.symbol
let same = 1
let sameMore = 2
let unreachable = 3
let run = 4
for
 absParts = empty:seq.seq.symbol
 , arcs = asset.[arc(1, 0)]
 , kind0 = empty:seq.int
 , place = 1
 , p0 ∈ parts
do
 let b = findelement2(arcs, arc(place, 0)),
  if n.b = 0 then
  next(absParts + p0, arcs, kind0 + unreachable, place + 1)
  else
   let isbr = isbr.1^p0
   let thispart =
    if not.isbr then
    p0
    else
     let x = 1^p0
     let y = 2^p0
     let brt = place + if y = Litfalse then brf.x else brt.x
     let brf = place + if y = Littrue then brt.x else brf.x,
      if 2^p0 = JumpOp then
      p0 >> 2 + EqOp + Br2(brt, brf)
      else if isIntLit.y then
      p0 >> 2 + 4^(place - 1)_absParts + y + EqOp + Br2(brt, brf)
      else p0 >> 1 + Br2(brt, brf)
   for sameArcs = empty:seq.arc.int, sameMoreArcs = empty:seq.arc.int, e2 ∈ toseq.b
   do
    if head.e2 = 0 ∨ (head.e2)_kind0 = same then
    next(sameArcs + e2, sameMoreArcs)
    else if (head.e2)_kind0 = sameMore then
    next(sameArcs, sameMoreArcs + e2)
    else next(sameArcs, sameMoreArcs)
   let chainArcs =
    if place = 1 then
    empty:seq.arc.int
    else if n.b = 1 ∧ n.sameMoreArcs = 1 then
    sameMoreArcs
    else sameArcs
   for kind1 = kind0, arcs1 = arcs, parts1 = absParts, chain ∈ chainArcs
   do
    let tochange = findelement2(arcs, arc(head.chain, 0))
    for arcs2 = arcs1, parts2 = parts1, arc ∈ toseq.tochange
    do next(
     arcs2 + arc(place, head.arc)
     , if head.arc = 0 then
      parts2
      else
       let p3 = (head.arc)_parts2
       let brt = brt.1^p3
       let brf = brf.1^p3
       let newpart =
        p3 >> 1
        + Br2(if brt = tail.arc then place else brt, if brf = tail.arc then place else brf),
       replace(parts2, head.arc, newpart)
    )
    let newkind = if head.chain > 0 then replace(kind1, head.chain, unreachable) else kind1,
    next(newkind, arcs2 \ (tochange + chain), parts2)
   let newkind =
    if isbr then
     kind1
     + 
      if brf.1^thispart = brt.1^thispart ∧ isconst.2^thispart then
      if n.thispart = 2 then same else sameMore
      else if 2^thispart = EqOp ∧ isIntLit.3^thispart ∧ islocal.4^thispart then
      run
      else 0
    else kind1 + 0
   let newarcs =
    if isbr then
    arcs1 + arc(brt.1^thispart, place) + arc(brf.1^thispart, place)
    else arcs1
   let p =
    if n.b = 1 ∧ n.sameMoreArcs = 1 then
    (head.1_sameMoreArcs)_absParts >> 2 + thispart
    else thispart,
   next(parts1 + p, newarcs, newkind, place + 1),
if n.arcs = 1 then
result >> 1 + (tail.1_arcs)_absParts >> 1
else
 for
  placements = empty:seq.int
  , map = arithseq(n.absParts, 1, 1)
  , revisedParts = absParts
  , final = empty:seq.symbol
  , haverun = empty:seq.int
  , idx = n.absParts
  , p ∈ reverse.absParts
 do
  if idx_kind0 = unreachable then
  next(placements, replace(map, idx, n.map + 1), revisedParts, final, haverun, idx - 1)
  else
   let x = 1^p,
    if not.isbr.x then
     for j = n.revisedParts
     while j_kind0 = unreachable ∨ j_revisedParts ≠ idx_revisedParts
     do j - 1,
      if j = idx then
      next([j] + placements, map, revisedParts, p + final, haverun, idx - 1)
      else next(placements, replace(map, idx, j), revisedParts, final, haverun, idx - 1)
    else
     let j = (brt.x)_map
     let k = (brf.x)_map
     let changed = j ≠ brt.x ∨ k ≠ brf.x
     let newp = if changed then p >> 1 + Br2(j, k) else p
     let parts1 = if changed then replace(revisedParts, idx, newp) else revisedParts,
      if idx ∈ haverun then
       if idx = 1^haverun then
        for
         placements0 = placements
         , final1 = final
         , bf = findindex(placements, (brf.1^(1_haverun)_parts1)_map)
         , e ∈ haverun
        do
         let ecode = e_parts1
         let tt = findindex(placements0, (brt.1^ecode)_map)
         let newfinal =
          if e = 1^haverun then
          ecode >> 2 + JumpOp + Br2(tt, bf) + final1
          else ecode >> 4 + 3^ecode + Br2(tt, bf) + final1,
         next([e] + placements0, newfinal, 1),
        next(placements0, map, parts1, final1, empty:seq.int, idx - 1)
       else next(placements, map, parts1, final, haverun, idx - 1)
      else
       let t =
        if isempty.haverun ∧ n.newp = 4 ∧ idx_kind0 = run then
         let h = 4^newp
         for accxx = empty:seq.int, this = newp, i = idx, values = asset.[value.3^newp]
         while i > 0
         do
          let f = findelement2(arcs, arc(i, 0)),
           if n.this ≠ 4 ∨ n.f ≠ 1 then
            {must be start of run /or multiple ways to get to i. So i must be first in run. }
            next(accxx + i, this, 0, values)
           else
            let i2 = head.1_f,
             if i2 = 0 ∨ i2_kind0 ≠ run ∨ 4^i2_parts1 ≠ h then
              {no more of block to included or i2 is not right format so end run.}
              next(accxx + i, this, 0, values)
             else
              let brvalue = value.3^i2_parts1,
               if brvalue ∈ values then
               {duplicate branch value so end run.} next(accxx + i, this, 0, values)
               else next(accxx + i, i2_parts1, i2, values + brvalue),
         accxx
        else empty:seq.int,
        if n.t ≥ 3 then
        next(placements, map, parts1, final, t, idx - 1)
        else
         for l = n.parts1 while l > idx ∧ l_parts1 ≠ newp do l - 1
         let lr = findindex(placements, l),
          if lr ≤ n.placements then
           {equivalent has aleady been added to final}
           next(placements, replace(map, idx, l), parts1, final, haverun, idx - 1)
          else
           let jj = findindex(placements, j)
           let kk = findindex(placements, k)
           let newfinal = newp >> 1 + Br2(jj, kk) + final,
           next([idx] + placements, map, parts1, newfinal, haverun, idx - 1),
 result + final + EndBlock

function %(a:arc.int) seq.word "/br^(tail.a)^(head.a)" 