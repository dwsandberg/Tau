module mergeblocks2

use standard

use symbol

use words

use otherseq.casenode

use seq.int

use set.int

use stack.int

use seq.repos

use otherseq.symbol

use seq.symbol

type ggg is code:seq.symbol, stk:stack.int

function countnodes2(s:stack.int)int if top.s = 2 then 1 else 1 + countnodes2.pop.s

Function valid(s:seq.symbol)boolean
 for valid = true, stk = empty:stack.int, sym = s while valid do if isblock.sym then
 let noblocks = countnodes2.stk
  next(top.stk ≤ noblocks, pop(stk, noblocks))
 else if isbr.sym then
 let blkno = countnodes2.stk + 1
  next(brt.sym > 0 ∧ brf.sym > 0, push(stk, max(blkno + max(brt.sym, brf.sym), top.stk)))
 else if first.module.sym ∈ "$exitblock $continue"then next(valid, push(stk, top.stk))
 else if isstartorloop.sym then next(valid, push(stk, 2))else next(valid, stk)/for(valid)

function ghj(code:seq.symbol, stk:stack.int, label:int, replace:int)seq.symbol
 if top.stk < 0 then code
 else
  let sym = code_(top.stk)
   { assert not.isbr.sym report"TFL"+ print.brt.sym + print.brf.sym + print.label + print.replace }
   let newcode = if isbr.sym ∧ (label = brt.sym ∨ label = brf.sym)then
    replace(code
    , top.stk
    , Br2(if label = brt.sym then replace else brt.sym, if label = brf.sym then replace else brf.sym)
    )
   else code
    ghj(newcode, pop.stk, label + 1, replace + 1)

type casenode is key:symbol, nodeno:int, brt:int

function keyvalue(n:casenode)int
let s = key.n
 if module.s = "$word"then encoding.(fsig.s)_1 else value.s

function ?(a:casenode, b:casenode)ordering keyvalue.a ? keyvalue.b

type repos is case:casenode, kind:word, branch:int

type reorgresult is code:seq.symbol, offset:int

function reorg(sorted:seq.casenode, brf:int, var:symbol, nodes:seq.int, nodeno:int)reorgresult
 { brf is absolute }
 if length.sorted < 4 then
  { rechain }
  let new = for acc = empty:seq.symbol, off = nodeno - (length.sorted - 1), c = sorted >> 1 do
   next(acc + [ var, key.c, EqOp, Br2(brt.c - off, 1)], off + 1)
  /for(let last = last.sorted
  let brt = brt.last - nodeno
   acc + [ var, key.last, EqOp, Br2(brt, brf - nodeno)])
   reorgresult(new, nodeno - length.sorted)
 else
  { split in two }
  let mid = length.sorted / 2
  let m = sorted_mid
  let lastpart = reorg(subseq(sorted, mid + 1, length.sorted), brf, var, nodes, nodeno)
  let firstpart = reorg(subseq(sorted, 1, mid - 1), brf, var, nodes, offset.lastpart)
  let new = [ var, key.m, GtOp, Br2(offset.lastpart - offset.firstpart + 2, 1)]
  + [ var, key.m, EqOp, Br2(brt.m - offset.firstpart, 1)]
  + code.firstpart
  + code.lastpart
   reorgresult(new, offset.firstpart - 2)

function findcases(code:seq.symbol, nodes:seq.int, casenodes:seq.int, dead:seq.int, nextvar:int, reorgwhen:int)seq.symbol
 for cases = empty:seq.casenode, last =-nodes_1, nodeno = 2, nextcase = 0, first = empty:seq.symbol, eqivs = empty:seq.symbol, e = nodes << 1 do
  if nodeno ∉ casenodes then next(cases, e, nodeno + 1, nextcase - 1, first, eqivs)
  else
   let sym = code_e
   let brt = brt.sym + nodeno
    if isempty.first then
     let b=subseq(code, last + 1, e - 3)
      if  length.b > 2 /and islocal.last.b /and b_-2=Define.first.fsig.last.b then
      next(cases + casenode(code_(e - 2), nodeno, brt), e, nodeno + 1, brf.sym, 
       subseq(code, last + 1, e - 5), [ last.b])
    else 
     next(cases + casenode(code_(e - 2), nodeno, brt), e, nodeno + 1, brf.sym, b, empty:seq.symbol)
    else if nextcase = 1 /and (subseq(code, last + 1, e - 3) = first /or last = e - 4 ∧ code_(e - 3) ∈ eqivs) then
     next(cases + casenode(code_(e - 2), nodeno, brt), e, nodeno + 1, brf.sym, first, eqivs)
    else if nextcase = 1 /and islocal.code_(e - 3)
    ∧ Define.first.fsig.code_(e - 3) = code_(e - 4)
    ∧ subseq(code, last + 1, e - 5) = first then
     next(cases + casenode(code_(e - 2), nodeno, brt), e, nodeno + 1, brf.sym, first, eqivs + code_(e - 3))
    else 
      if length.cases < reorgwhen then
       next([casenode(code_(e - 2), nodeno, brt)], e, nodeno + 1, brf.sym, subseq(code, last + 1, e - 3), empty:seq.symbol)
      else
       next (cases,e,nodeno+1,nextcase-1,first,eqivs)
 /for(if length.cases < reorgwhen then removedead(code, nodes, dead)
 else 
  let testvar = if length.first = 1 then first_1 else if isempty.eqivs then Local.nextvar else eqivs_1
  let settestvar = if length.first = 1 then empty:seq.symbol else first + Define.first.fsig.testvar
  let t = reorg(sort.cases, nodeno.last.cases + brf.code_(nodes_(nodeno.last.cases)), testvar, nodes, nodeno.first.cases - 1)
  let nonewnodes = length.code.t / 4
  let locnode = nodeno.first.cases - 1
  let nodesBeforeStartOfCase = subseq(nodes, 1, locnode)
  let newcasecode = settestvar + code.t
  let loc = abs.nodes_locnode
  let newcode = subseq(adjustbr(code, subseq(nodes, 1, locnode + 1), nonewnodes), 1, loc) + newcasecode
  + subseq(code, loc + 1, length.code)
  let newnodes = for l = nodesBeforeStartOfCase + arithseq(nonewnodes, 4, loc + length.settestvar + 4), n = nodes << locnode do
   l + [ length.newcasecode + n]
  /for(l)
  let newunreached = for l = for x = empty:seq.int, y = dead do x + 
   if y < locnode then y else (nonewnodes + y)/for(x), n = cases do
  let n2 = nodeno.n + nonewnodes
   if isempty.l then [ n2]
   else if last.l > n2 then l + n2
   else if n2 > first.l then [ n2] + l
   else
    for l2 = [ first.l], lastx = first.l, n3 = l << 1 do
     next(if between(n2, n3, lastx)then l2 + n2 + n3 else l2 + n3, n3)
    /for(l2)
  /for(l)
   { nodes_node.first.cases }
   assert true report"cases" + for l = EOL, c = cases do l + print.nodeno.c /for(l)
   + print.newcode
   + EOL
   + { for l = EOL, c = newnodes do l + print.newcode_abs.c end(l)+ } EOL
   + for l ="dead" + EOL, c = newunreached do l + print.c /for(l)
   + EOL
   + for l ="deadin" + EOL, c = dead do l + print.c /for(l)
   + EOL
   + for l ="olddead" + EOL, c = cases do l + print.nodeno.c /for(l)
   + EOL
   + print.nonewnodes
   + EOL
   + print.removedead(newcode, newnodes, newunreached)
    removedead(newcode, newnodes, newunreached)/if)

function unreached(code:seq.symbol, nodes:seq.int, nextvar:int, reorgwhen:int)seq.symbol
 for unreached = empty:seq.int, multpred = empty:seq.int, cases = empty:seq.int, targets = asset.[ 2], count = 2, n = nodes << 1 do
 let sym = code_n
  if count ∉ targets then next([ count] + unreached, multpred, cases, targets, count + 1)
  else if not.isbr.sym then next(unreached, multpred, cases, targets, count + 1)
  else
   { isbr }
   let t = count + brt.sym
   let f = count + brf.sym
   let c = if t ∈ targets then 1 else 0 /if + if f ∈ targets then 2 else 0
   let newcases = if n ∉ multpred ∧ fsig.code_(n - 1) = "=(int, int)"
   ∧ isconst.code_(n - 2)then
    cases + count
   else cases
   let newtargets = if c = 0 then targets + t + f
   else if c = 1 then targets + f else if c = 2 then targets + t else targets
   let newmultpred = if c = 0 then multpred
   else if c = 1 then multpred + t
   else if c = 2 then multpred + f else multpred + t + f
    next(unreached, newmultpred, newcases, newtargets, count + 1)
 /for(assert true report"casenodes" + for l ="", c = cases do l + print.c /for(l)
 + "unreached"
 + for l ="", c = unreached do l + print.c /for(l)
 + "targets"
 + for l ="", c = toseq.targets do l + print.c /for(l)
 + "multpred"
 + for l ="", c = multpred do l + print.c /for(l)
 + EOL
 + print.code
  if length.nodes - 3 = length.unreached ∧ isstart.code_(-first.nodes)then
   { just two active nodes which must be a branch follow by an exit.so remove block }
   let blkstart =-first.nodes
   let secondnode = code_(nodes_2)
   let firstpart=subseq(code, blkstart + 1, nodes_2 - 1)
   let firstpart1=if length.firstpart=1 /and (isconst.firstpart_1 /or islocal.firstpart_1) then empty:seq.symbol
   else    firstpart+Define.100000
    subseq(code, 1, blkstart - 1) + firstpart1
    + subseq(code, nodes_(1 + brt.secondnode) + 1, nodes_(2 + brt.secondnode) - 1)
  else if length.cases < reorgwhen then removedead(code, nodes, unreached)else findcases(code, nodes, cases, unreached, nextvar, reorgwhen)/if /if)

function removedead(code:seq.symbol, nodes:seq.int, dead:seq.int)seq.symbol
 { nodes in dead are in descending order }
 for newcode = code, n = dead do
  adjustbr(subseq(newcode, 1, nodes_(n - 1)), subseq(nodes, 2, n - 1),-1)
  + subseq(newcode, nodes_n + 1, length.code)
 /for(newcode + EndBlock)

Function optB(s:seq.symbol, self:symbol)seq.symbol
let reorgwhen = 6
 for acc = empty:seq.symbol, stk = empty:stack.int, nextvar = length.s, lastsymbol = Lit.0, sym = s do
  if(lastsymbol = Littrue ∨ lastsymbol = Litfalse) ∧ isbr.sym
  ∧ top.stk = length.acc - 1 then
   { patch previous br's so they skip over this block }
   next(ghj(acc, stk, 1, 1 + if lastsymbol = Littrue then brt.sym else brf.sym) + sym, push(stk, length.acc + 1), nextvar, sym)
  else if isblock.sym then next(acc, stk, nextvar, sym)
  else if not.isblock.lastsymbol then next(acc + sym, newstk(sym, stk, acc), nextvar, sym)
  else
   { lastsymbol isblock }
   let noblocks = countnodes.stk
   let nodes = top(stk, noblocks)
   let stk1 = pop(stk, noblocks)
   let blkstart =-first.nodes
    if isloopblock.acc_blkstart ∨ sym ≠ Exit ∧ not.isbr.sym then
    let code0 = unreached(acc, nodes, nextvar, reorgwhen)
     next(code0 + sym, newstk(sym, stk1, code0), nextvar + 1, sym)
    else if isbr.sym then
     { assert noblocks ≠ 4 report"X"+ print.noblocks + print.length.s }
     { adjust br in enclosing block }
     let code0 = adjustbr(acc, top(stk1, countnodes.stk1 - 1), noblocks - 2)
      { remove start of block }
      let code1 = subseq(code0, 1,-first.nodes - 1) + subseq(code0,-first.nodes + 1, length.code0)
       { replace exit by br sym }
       let t = for code2 = code1, stk2 = stk1, adjust = noblocks - 2, n1 = nodes << 1 do
       let n = n1 - 1
        next(if code2_n = Exit then
         if top.stk2 = n - 2 ∧ code2_(n - 1) = Littrue then
         let code3 = ghj(code2, stk2, 1, brt.sym + adjust + 1)
          replace(code3, n, Br2(brt.sym + adjust, brt.sym + adjust))
         else if top.stk2 = n - 2 ∧ code2_(n - 1) = Litfalse then
         let code3 = ghj(code2, stk2, 1, brf.sym + adjust + 1)
          replace(code3, n, Br2(brf.sym + adjust, brf.sym + adjust))
         else replace(code2, n, Br2(brt.sym + adjust, brf.sym + adjust))
        else code2, push(stk2, n), adjust - 1)
       /for(ggg(code2, stk2))
        next(code.t, stk.t, nextvar, sym)
    else
     assert sym = Exit report"Expected Exit"
      { adjust br in enclosing block }
      let code0 = adjustbr(acc, top(stk1, countnodes.stk1 - 1), noblocks - 2)
       { remove start of block }
       let code1 = subseq(code0, 1,-first.nodes - 1) + subseq(code0,-first.nodes + 1, length.code0)
        { build new stk }
        let stk2 = for stk2 = stk1, n = nodes << 1 do push(stk2, n - 1)/for(stk2)
         next(code1, stk2, nextvar, sym)
 /for(if isblock.lastsymbol then
  if not.isconst.self ∧ first.toseq.stk = -1 then tailR(acc + lastsymbol, self, stk)
  else unreached(acc, toseq.stk, nextvar, reorgwhen)
 else acc /if)

function newstk(sym:symbol, stk:stack.int, acc:seq.symbol)stack.int
 if isstartorloop.sym then push(stk,-length.acc - 1)
 else if first.module.sym ∈ "$br $exitblock $continue"then push(stk, length.acc + 1)else stk

function tailR(code:seq.symbol, self:symbol, stk:stack.int)seq.symbol
let l = for l = empty:seq.int, ss = toseq.stk do
 if ss > 0 ∧ code_ss = Exit ∧ code_(ss - 1) = self then
  [ ss] + l
 else l
/for(l)
 if isempty.l then code
 else
  let nopara = nopara.self
  let plist = for acc = empty:seq.symbol, e2 = arithseq(nopara, 1, 1)do acc + Local.e2 /for(acc)
  let code2 = for code2 = code, i = l do
   subseq(code2, 1, i - 2) + continue.nopara + subseq(code2, i + 1, length.code2)
  /for(code2)
   plist + Loopblock(paratypes.self, nopara + 1, resulttype.self) + adjustvar(code2 << 1, nopara)

function adjustvar(s:seq.symbol, delta:int)seq.symbol
 for acc = empty:seq.symbol, a = s do
  if islocal.a then acc + Local(toint.(fsig.a)_1 + delta)
  else if isdefine.a then acc + Define.toword(toint.(fsig.a)_2 + delta)
  else if isloopblock.a then acc + Loopblock(paratypes.a, firstvar.a + delta, resulttype.a)else acc + a
 /for(acc)

function adjustbr(code:seq.symbol, nodestoadjust:seq.int, adjust:int)seq.symbol
 { if branch target is not in nodestoadjust then it is adjusted }
 { nodes to adjust does not include block start node }
 for acc = code, blockcount = length.nodestoadjust, i = nodestoadjust do
 let sym = acc_i
  if isbr.sym ∧ (brt.sym > blockcount ∨ brf.sym > blockcount)then
  let newt = if brt.sym > blockcount then brt.sym + adjust else brt.sym
  let newf = if brf.sym > blockcount then brf.sym + adjust else brf.sym
   next(replace(acc, i, Br2(newt, newf)), blockcount - 1)
  else next(acc, blockcount - 1)
 /for(acc)

function countnodes(s:stack.int)int if top.s < 0 then 1 else 1 + countnodes.pop.s

Function removeismember(c:symbol, var:symbol)seq.symbol
 if module.c = "$words"then
 let words = fsig.c
  if isempty.words then [ Litfalse]
  else
   let t = length.words + 2
    if length.words = 1 then [ var, Word.words_1, EqOp]
    else
     for acc = [ start.typeboolean], idx = 2, w = words >> 1 do
      next(acc + [ var, Word.w, EqOp] + Br2(t - idx, 1), idx + 1)
     /for(acc + [ var, Word.last.words, EqOp, Exit, Littrue, Exit, EndBlock])
 else
  let z = constantcode.c << 2
   if isempty.z then [ Litfalse]
   else if length.z = 1 then [ var, first.z, EqOp]
   else
    let t = length.z + 2
     for acc = [ start.typeboolean], idx = 2, w = z >> 1 do
      next(acc + [ var, w, EqOp] + Br2(t - idx, 1), idx + 1)
     /for(acc + [ var, last.z, EqOp, Exit, Littrue, Exit, EndBlock])