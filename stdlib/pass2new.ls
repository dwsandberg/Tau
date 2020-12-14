Module pass2new

use UTF8

use bits

use otherseq.block

use seq.block

use stack.block

use otherseq.caseblock

use seq.caseblock

use seq.char

use otherseq.int

use otherseq.seq.int

use seq.seq.int


use set.int

use otherseq.mytype

use seq.mytype

use real

use stacktrace

use standard

use otherseq.symbol

use seq.seq.seq.symbol

use seq.seq.symbol

use worddict.seq.symbol

use seq.symbol

use set.symbol

use symbol

use otherseq.word

use seq.seq.word

use set.seq.word

use seq.int

use set.word

type block is record kind:word, blkno:int, label1:int, label2:int, code:seq.symbol, subblks:seq.block

function block(kind:word, blkno:int, label1:int, label2:int, code:seq.symbol)block block(kind, blkno, label1, label2, code, empty:seq.block)

function breakblocks(p:program, code:seq.symbol, self:symbol, alltypes:typedict)seq.symbol
 let a = breakblocks(p, code, 1, 1, empty:seq.symbol, empty:stack.block)
  if length.a = 1 then code.a_1
  else if kind.a_1 ≠ "LOOPBLOCK"_1 ∧ a @ ∨(false, tailrecursion(self, @e))then
  // tail recursion //
   let nopara = nopara.self
   let a2 = a @ +(empty:seq.block, preparetail(nopara, self, continue.nopara, @e))
   let plist = arithseq(nopara, 1, 1) @ +(empty:seq.symbol, var.@e)
   let entry = block("LOOPBLOCK"_1, 0, blkno.a2_1, 0, plist + Lit(nopara + 1)
   + Loopblock(paratypes.self @ list("",",", [ parakind2(alltypes, @e)]) + ", int)"))
    ascode(p, [ entry] + a2, self)
  else ascode(p, a, self)

function parakind2(alltypes:typedict, type:mytype)word kind.gettypeinfo(alltypes, type)

function preparetail(nopara:int, self:symbol, continue:symbol, b:block)block
 let code = adjustvar(code.b, nopara, 1, empty:seq.symbol)
  if kind.b = "EXIT"_1 ∧ code_(length.code - 1) = self then
  block("CONTINUE"_1, blkno.b, label1.b, label2.b, subseq(code, 1, length.code - 2) + continue)
  else block(kind.b, blkno.b, label1.b, label2.b, code)

function tailrecursion(self:symbol, b:block)boolean
 kind.b = "EXIT"_1 ∧ (code.b)_(length.code.b - 1) = self

function adjustvar(s:seq.symbol, delta:int, i:int, result:seq.symbol)seq.symbol
 if i > length.s then result
 else
  let a = s_i
   if islocal.a then
   adjustvar(s, delta, i + 1, result + var(toint.(fsig.a)_1 + delta))
   else if isdefine.a then
   adjustvar(s, delta, i + 1, result + Define.toword(toint.(fsig.a)_2 + delta))
   else if isloopblock.a then
   let b = subseq(result, 1, i - 2) + Lit(value.s_(i - 1) + delta) + a
     adjustvar(s, delta, i + 1, b)
   else adjustvar(s, delta, i + 1, result + a)

function breakblocks(p:program, code:seq.symbol, i:int, start:int, blkcode:seq.symbol, blks:stack.block)seq.block
 if i > length.code then
 [ block("FINAL"_1, 0, 0, 0, blkcode + subseq(code, start, i))]
 else if isbr.code_i then
 breakblocks(p, code, i + 1, i + 1, empty:seq.symbol, push(blks, block("BR"_1, i, 0, 0, blkcode + subseq(code, start, i))))
 else if isexit.code_i then
 breakblocks(p, code, i + 1, i + 1, empty:seq.symbol, push(blks, block("EXIT"_1, i, 0, 0, blkcode + subseq(code, start, i))))
 else
  let rep = code_i
   if not.isspecial.rep then breakblocks(p, code, i + 1, start, blkcode, blks)
   else
    let kind =(fsig.rep)_1
     if kind ∈ "CONTINUE LOOPBLOCK"then
     breakblocks(p, code, i + 1, i + 1, empty:seq.symbol, push(blks, block(kind, i, 0, 0, blkcode + subseq(code, start, i))))
     else if kind ≠ "BLOCK"_1 then breakblocks(p, code, i + 1, start, blkcode, blks)
     else
      let nopara = nopara.rep
      let args = top(blks, nopara)
      let subblks = cvtlabels(args, 1, empty:seq.block)
       if i = length.code then subblks
       else if isexit.code_(i + 1) ∧ kind.subblks_1 ≠ "LOOPBLOCK"_1 then
       breakblocks(p, code, i + 2, i + 2, empty:seq.symbol, push(pop(blks, nopara), block("SEQBLKS"_1, blkno.subblks_1, 0, 0, empty:seq.symbol, subblks)))
       else if i + 3 ≤ length.code ∧ isbr.code_(i + 3)
       ∧ kind.subblks_1 = "BR"_1 then
       breakblocks(p
        , code
        , i + 4
        , i + 4
        , empty:seq.symbol
        , push(pop(blks, nopara), block("BRBLKS"_1, blkno.subblks_1, 0, 0, subseq(code, i + 1, i + 3), subblks)))
       else
        breakblocks(p, code, i + 1, i + 1, blkcode + ascode(p, subblks, rep), pop(blks, nopara))

function ascode(p:program, subblks1:seq.block, org:symbol)seq.symbol
 let x = ascode(p, subblks1, 1, [ subblks1_1], empty:seq.symbol)
 let rrr = subseq(x, 1, length.x - 1)
 let blksize = value.last.x
  if isblock.org ∧ nopara.org = blksize then // use original block // rrr + org
  else
   let type ="int"
    rrr + Block(resulttype.org, blksize)

function =(a:block, b:block)boolean blkno.a = blkno.b

function checkforcase(p:program, blk:block)seq.symbol
 if not.iscaseblock.blk then empty:seq.symbol
 else
  let t = backparse2(code.blk, length.code.blk - 5, 1, empty:seq.int)
  let exp = subseq(code.blk, t_1, length.code.blk - 5)
   if exp @ ∨(false, hasstate(p, @e))then empty:seq.symbol else exp

function ascode(p:program, l:seq.block, i:int, assigned:seq.block, result:seq.symbol)seq.symbol
 if i > length.assigned then result + Lit.length.assigned
 else
  let blk = assigned_i
   if kind.blk ∈ "BR"then
   let a2 = findblk2(l, 1, label2.blk)
    let exp = checkforcase(p, blk)
     if not.isempty.exp then
     let r = gathercase(l, blk, exp, empty:seq.caseblock)
       if length.caseblks.r = 1 then
       // go ahead and process BR"//
        let c =(caseblks.r)_1
        let a1 = findblk2(l, 1, label1.blk)
        let l1 = findindex(a1, assigned)
        let assigned1 = if l1 > length.assigned then assigned + a1 else assigned
        let l2 = findindex(a2, assigned1)
        let assigned2 = if l2 > length.assigned1 then assigned1 + a2 else assigned1
         ascode(p, l, i + 1, assigned2, result + subseq(code.blk, 1, length.code.blk - 5) + keysig.c + EqOp
         + Lit.l1
         + Lit.l2
         + Br)
       else
        // more than one case block //
        let var = if islocal.last.exp then last.exp else var.1000
        let prefix = if islocal.last.exp then subseq(code.blk, 1, length.code.blk - 6)
        else subseq(code.blk, 1, length.code.blk - 5) + Define."1000"_1
        let z = rearrangecase(caseblks.r, blkno.last.l + 1, defaultlabel.r, var)
        let newl = if blkno.last.l < nextblklabel.z - 1 then
        l + block("?"_1, nextblklabel.z - 1, 0, 0, empty:seq.symbol)
        else l
        let first =(allocated.z)_1
        let first1 = if isempty.prefix then first else block(kind.first, blkno.first, label1.first, label2.first, prefix + code.first)
         ascode(p, newl, i, replace(assigned, i, first1) + subseq(allocated.z, 2, length.allocated.z), result)
     else
      let a1 = findblk2(l, 1, label1.blk)
      let l1 = findindex(a1, assigned)
      let assigned1 = if l1 > length.assigned then assigned + a1 else assigned
      let l2 = findindex(a2, assigned1)
      let assigned2 = if l2 > length.assigned1 then assigned1 + a2 else assigned1
       ascode(p, l, i + 1, assigned2, result + subseq(code.blk, 1, length.code.blk - 3) + Lit.l1 + Lit.l2
       + Br)
   else if kind.blk ∈ "BRC"then
   let l1 = findindex(label1.blk, 1, assigned)
    let assigned1 = if l1 > length.assigned then assigned + findblk2(l, 1, label1.blk)else assigned
    let l2 = findindex(label2.blk, 1, assigned1)
    let assigned2 = if l2 > length.assigned1 then assigned1 + findblk2(l, 1, label2.blk)else assigned1
     ascode(p, l, i + 1, assigned2, result + subseq(code.blk, 1, length.code.blk - 3) + Lit.l1 + Lit.l2
     + Br)
   else if kind.blk ∈ "LOOPBLOCK"then
   let a1 = findblk2(l, 1, label1.blk)
    let l1 = findindex(a1, assigned)
    let assigned1 = if l1 > length.assigned then assigned + a1 else assigned
     ascode(p, l, i + 1, assigned1, result + code.blk)
   else
    assert kind.blk ∈ "EXIT CONTINUE"report"PROB 4" + kind.blk
     ascode(p, l, i + 1, assigned, result + code.blk)

function caseblock(truelabel:int, orgblkno:int, rep:symbol)caseblock
 let key = if islit.rep then toint.(fsig.rep)_1
 else
  assert module.rep = "$word"report"unexpected const type"
   hash.(fsig.rep)_1
  caseblock(key, rep, truelabel, orgblkno)

function caseblock(truelabel:int, orgblkno:int, w:word)caseblock caseblock(hash.w, Word.w, truelabel, orgblkno)

function findindex(label:int, i:int, a:seq.block)int
 if i > length.a then i
 else if blkno.a_i = label then i else findindex(label, i + 1, a)

type caseblock is record key:int, keysig:symbol, truelabel:int, orgblkno:int

function print(c:caseblock)seq.word
 " &br" + toword.key.c + print.[ keysig.c] + toword.truelabel.c
 + toword.orgblkno.c

function =(a:caseblock, b:caseblock)boolean key.a = key.b

function ?(a:caseblock, b:caseblock)ordering key.a ? key.b

function iscaseblock(blk:block)boolean
 let code = code.blk
 let len = length.code
  len > 5 ∧ kind.blk = "BR"_1 ∧ isconst.code_(len - 4)
  ∧ isinOp.code_(len - 3)
  ∧ not.isFref.code_(len - 4)

type gathercaseresult is record caseblks:seq.caseblock, defaultlabel:int

function gathercase(l:seq.block, blk:block, exp:seq.symbol, caseblks:seq.caseblock)gathercaseresult
 // blk is a caseblock but have not created the caseblks yet or check for following case blocks //
 let code = code.blk
 let len = length.code
 let label = blkno.findblk2(l, 1, label1.blk)
 let t = if code_(len - 3) = EqOp then [ caseblock(label, blkno.blk, code_(len - 4))]
 else
  let rep = code_(len - 4)
   if module.rep = "$words"then
   fsig.rep @ +(empty:seq.caseblock, caseblock(label, 0, @e))
   else
    assert length.constantcode.rep > 2
    ∧ ((constantcode.rep)_1 = Lit0 ∨ (constantcode.rep)_1 = Lit.1)report"not a standard seq" + print.code
     subseq(constantcode.rep, 3, length.constantcode.rep) @ +(empty:seq.caseblock, caseblock(label, 0, @e))
  // now check to see if following block is a case block //
  let newblock = findblk2(l, 1, label2.blk)
   if iscaseblock.newblock ∧ subseq(code.newblock, 1, length.code.newblock - 5) = exp then
   gathercase(l, newblock, exp, caseblks + t)
   else gathercaseresult(sort(caseblks + t), blkno.newblock)

type gggresult is record nextblklabel:int, allocated:seq.block

function rearrangecase(cbs:seq.caseblock, nextblklabel:int, defaultlabel:int, var:symbol)gggresult
 if length.cbs = 1 then
 let blklabel = if orgblkno.cbs_1 > 0 then orgblkno.cbs_1 else nextblklabel
   gggresult(if blklabel = nextblklabel then nextblklabel + 1 else nextblklabel, [ block("BRC"_1, blklabel, truelabel.cbs_1, defaultlabel, [ var, keysig.cbs_1, EqOp, Lit0, Lit0, Br])])
 else if length.cbs = 2 then
 let blklabel1 = if orgblkno.cbs_1 > 0 then orgblkno.cbs_1 else nextblklabel
  let next1 = if blklabel1 = nextblklabel then nextblklabel + 1 else nextblklabel
  let blklabel2 = if orgblkno.cbs_2 > 0 then orgblkno.cbs_2 else next1
  let next2 = if blklabel2 = next1 then next1 + 1 else next1
   gggresult(next2
   , [ block("BRC"_1, blklabel1, truelabel.cbs_1, blklabel2, [ var, keysig.cbs_1, EqOp, Lit0, Lit0, Br]), block("BRC"_1, blklabel2, truelabel.cbs_2, defaultlabel, [ var, keysig.cbs_2, EqOp, Lit0, Lit0, Br])])
 else
  let m = length.cbs / 2 + 1
  let middle = cbs_m
  let low = rearrangecase(subseq(cbs, 1, m - 1), nextblklabel + 2, defaultlabel, var)
  let high = rearrangecase(subseq(cbs, m + 1, length.cbs), nextblklabel.low, defaultlabel, var)
  let lowerlabel = blkno.(allocated.low)_1
  let upperlabel = blkno.(allocated.high)_1
   gggresult(nextblklabel.high
   , [ block("BRC"_1, nextblklabel, upperlabel, nextblklabel + 1, [ var, keysig.middle, gtOp, Lit0, Lit0, Br]), block("BRC"_1, nextblklabel + 1, truelabel.middle, lowerlabel, [ var, keysig.middle, EqOp, Lit0, Lit0, Br])]
   + allocated.low
   + allocated.high)

function findblk2(l:seq.block, i:int, blkno:int)block
 assert i ≤ length.l report"did not find block" + stacktrace
 let blk = l_i
  if blkno.blk = blkno then
  if kind.blk = "JMP"_1 then findblk2(l, 1, label1.blk)else blk
  else findblk2(l, i + 1, blkno)

function ascode(r:set.int, t:block)seq.symbol
 if blkno.t ∉ r then empty:seq.symbol
 else if kind.t = "BR"_1 then
 subseq(code.t, 1, length.code.t - 3) + Lit.findindex(label1.t, toseq.r)
  + Lit.findindex(label2.t, toseq.r)
  + Br
 else
  assert kind.t ∈ "EXIT CONTINUE LOOPBLOCK"report"PROB 4" + kind.t
   code.t

function cvtlabels(blks:seq.block, i:int, result:seq.block)seq.block
 // set block labels in BR //
 if i > length.blks then
 let b = blks_1
   if kind.b = "LOOPBLOCK"_1 then
   let label = blkno.blks_2
     [ block("LOOPBLOCK"_1, blkno.b, label, label, code.b)] + subseq(result, 2, length.result)
   else result
 else
  let b = blks_i
  let newtrees = if kind.b = "BR"_1 ∧ label1.b = 0 then
  let len = length.code.b
    [ block(kind.b, blkno.b, blkno.blks_(value.(code.b)_(len - 2)), blkno.blks_(value.(code.b)_(len - 1)), code.b)]
  else if kind.b = "SEQBLKS"_1 then subblks.blks_i
  else if kind.b = "BRBLKS"_1 then
  assert length.code.b = 3 report"OPT P"
    subblks.b
    @ +(empty:seq.block, convertexits(blkno.blks_(value.(code.b)_1), blkno.blks_(value.(code.b)_2), @e))
  else [ blks_i]
   cvtlabels(blks, i + 1, result + newtrees)

function print(b:block)seq.word
 " &br >>>>" + [ kind.b, toword.blkno.b]
 + if kind.b ∈ "BR BRC"then
 [ toword.label1.b, toword.label2.b]
  + print.// [(code.b)_(length.code.b-3)]// code.b
 else if kind.b = "BRBLKS"_1 then
 "(" + subblks.b @ +("", print.@e) + ")"
 else if kind.b ∈ "EXIT CONTINUE"then print.code.b
 else if kind.b = "JMP"_1 then [ toword.label1.b] + print.code.b else"??"

function convertexits(label1:int, label2:int, b:block)block
 if kind.b ∈ "BR JMP"then b
 else
  assert kind.b = "EXIT"_1 report"unexpected block type" + kind.b
   if length.code.b = 2 ∧ isconst.(code.b)_1 then
   let target = if Lit0 = (code.b)_1 then label2 else label1
     block("JMP"_1, blkno.b, target, target, empty:seq.symbol)
   else
    block("BR"_1, blkno.b, label1, label2, subseq(code.b, 1, length.code.b - 1) + [ Lit0, Lit0, Br])

type backresult is record code:seq.symbol, places:seq.int

Function firstopt(p:program, rep:symbol, code:seq.symbol, alltypes:typedict)program
 let nopara = nopara.rep
  if isbuiltin.module.rep then
  let options = caloptions(p, code, nopara, module.rep, fsig.rep)
    map(p, symbol(fsig.rep, module.rep, returntype.rep), addoptions(code, options))
  else
   let pdict = addpara(emptyworddict:worddict.seq.symbol, nopara)
   let code2 = code.yyy(p, code, 1, empty:seq.symbol, nopara + 1, pdict)
   let options = caloptions(p, code2, nopara, module.rep, fsig.rep)
   let s = symbol(fsig.rep, module.rep, returntype.rep)
   let a = breakblocks(p, code2, s, alltypes)
   let a2 = code.yyy(p, a, 1, empty:seq.symbol, nopara + 1, pdict)
    map(p, s, addoptions(a2, options))

function print(s:seq.int)seq.word s @ +("", toword.@e)

function var(i:int)symbol var.toword.i

function var(w:word)symbol Local.w

function addpara(map:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i ≤ 0 then map
 else
  let v = var.i
   addpara(add(map, toword.i, [ v]), i - 1)

function addlooplocals(map:worddict.seq.symbol, firstvar:int, nextvar:int, nopara:int, i:int)worddict.seq.symbol
 if i = nopara then map
 else
  addlooplocals(replace(map, toword(firstvar + i), [ var(nextvar + i)]), firstvar, nextvar, nopara, i + 1)

function yyy(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, map:worddict.seq.symbol)expandresult
 if k > length.org then expandresult(nextvar, result)
 else
  let sym = org_k
  let len = length.result
   if isconst.sym then yyy(p, org, k + 1, result + sym, nextvar, map)
   else  if isspecial.sym then
   if(fsig.sym)_1 = "BLOCK"_1 ∧ fsig.sym = "BLOCK 3"then
    let t = backparse(result, len, 3, empty:seq.int) + [ len + 1]
     let condidx = t_2 - 4
     let cond = result_condidx
      if isbr.result_(condidx + 3) ∧ isconst.cond then
      let keepblock = if value.cond = 1 then value.result_(condidx + 1)else value.result_(condidx + 2)
       let new = subseq(result, t_keepblock, t_(keepblock + 1) - 2)
        yyy(p, org, k + 1, subseq(result, 1, condidx - 1) + new, nextvar, map)
      else yyy(p, org, k + 1, result + sym, nextvar, map)
    else if // isdefine //(fsig.sym)_1 = "DEFINE"_1 then
    let thelocal =(fsig.sym)_2
      if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
      yyy(p, org, k + 1, subseq(result, 1, length.result - 1), nextvar, replace(map, thelocal, [ result_len]))
      else
       yyy(p, org, k + 1, result + Define.toword.nextvar, nextvar + 1, replace(map, thelocal, [ var.nextvar]))
    else if isloopblock.sym then
    let nopara = nopara.sym - 1
     let firstvar = value.result_len
      yyy(p, org, k + 1, subseq(result, 1, len - 1) + Lit.nextvar + sym, nextvar + nopara, addlooplocals(map, firstvar, nextvar, nopara, 0))
    else if(fsig.sym)_1 = "RECORD"_1 then
    let nopara = nopara.sym
     let args = subseq(result, len + 1 - nopara, len)
      if args @ ∧(true, isconst.@e)then
      yyy(p, org, k + 1, subseq(result, 1, len - nopara) + Constant2(args + sym), nextvar, map)
      else yyy(p, org, k + 1, result + sym, nextvar, map)
    else if(module.sym)_1 = "local"_1 then
    let t = lookup(map,(fsig.sym)_1)
      if isempty.t then yyy(p, org, k + 1, result + sym, nextvar, map)
      else yyy(p, org, k + 1, result + t_1, nextvar, map)
    else if(module.sym)_1 = "para"_1 then
    let sym2 = Local.(module.sym)_2
     let t = lookup(map,(fsig.sym2)_1)
      if isempty.t then yyy(p, org, k + 1, result + sym2, nextvar, map)
      else yyy(p, org, k + 1, result + t_1, nextvar, map)
    else if len > 2 ∧ isnotOp.result_(len - 2) ∧ fsig.sym = "BR 3"then
    yyy(p, org, k + 1, subseq(result, 1, len - 3) + [ result_len, result_(len - 1), Br], nextvar, map)
    else yyy(p, org, k + 1, result + sym, nextvar, map)
   else if(fsig.sym)_1 ∈ "apply3"then applycode3(p, org, k, result, nextvar, map)
   else
    let nopara = nopara.sym
    let dd = code.lookupcode(p, sym)
     if not.isempty.dd ∧ "INLINE"_1 ∈ options.dd then
     let code = if last.dd = Optionsym then subseq(dd, 1, length.dd - 2)else dd
       if isempty.code then yyy(p, org, k + 1, result + sym, nextvar, map)
       else inline(p, org, k, result, nextvar, nopara, code, map, options.dd)
     else if nopara = 0 ∨ nopara > 2 ∨ not.isconst.result_len then
     yyy(p, org, k + 1, result + sym, nextvar, map)
     else
      // one or two parameters with last arg being constant //
      if nopara = 1 then
      // one constant parameter //
       if sym = symbol("toword(int)","UTF8","word")then
       yyy(p, org, k + 1, subseq(result, 1, length.result - 1) + Word.(fsig.last.result)_1, nextvar, map)
       else  if fsig.sym = "makereal(word seq)" ∧ module.sym = "UTF8"then
       let arg1 = last.result
         if module.arg1 = "$words"then
         let x = Reallit.representation.makereal.fsig.arg1
           yyy(p, org, k + 1, subseq(result, 1, length.result - 1) + x, nextvar, map)
         else yyy(p, org, k + 1, result + sym, nextvar, map)
       else if fsig.sym = "merge(word seq)" ∧ module.sym = "words"then
       let arg1 = last.result
         if module.arg1 = "$words"then
         yyy(p, org, k + 1, subseq(result, 1, length.result - 1) + Word.merge.fsig.arg1, nextvar, map)
         else yyy(p, org, k + 1, result + sym, nextvar, map)
       else if fsig.sym = "decode(char seq encoding)" ∧ module.sym = "char seq encoding"then
       let arg1 = result_len
         if module.arg1 = "$word"then
         let a1 = tointseq.decodeword.(fsig.arg1)_1 @ +(empty:seq.symbol, Lit.@e)
          let d = Constant2([ Stdseq, Lit.length.a1] + a1 + Record.constantseq(length.a1 + 2,"int"_1))
           yyy(p, org, k + 1, subseq(result, 1, len - 1) + d, nextvar, map)
         else yyy(p, org, k + 1, result + sym, nextvar, map)
       else if fsig.sym = "encode(char seq)" ∧ module.sym = "char seq encoding"then
       let arg1 = result_len
         if module.arg1 = "$constant"then
         let chseq = subseq(constantcode.arg1, 3, length.constantcode.arg1) @ +(empty:seq.int, value.@e)
           assert subseq(constantcode.arg1, 3, length.constantcode.arg1) @ ∧(true, islit.@e)report"const problem"
           let new = Word.encodeword(chseq @ +(empty:seq.char, char.@e))
            yyy(p, org, k + 1, subseq(result, 1, len - 1) + new, nextvar, map)
         else yyy(p, org, k + 1, result + sym, nextvar, map)
       else yyy(p, org, k + 1, result + sym, nextvar, map)
      else
       // two parameters with constant args //
       // should add case of IDXUC with record as first arg //
       if not.isconst.result_(len - 1)then yyy(p, org, k + 1, result + sym, nextvar, map)
       else
        // two parameters with constant args //
        if isbuiltin.module.sym then opttwoopbuiltin(p, org, k, result, nextvar, map, sym)
        else if last.module.sym = "seq"_1
        ∧ (fsig.sym = "_(T seq, int)"
        ∨ fsig.sym
        = "_(" + subseq(module.sym, 1, length.module.sym - 1) + "seq, int)")then
        let idx = value.result_len
         let arg1 = result_(len - 1)
          if module.arg1 = "$words" ∧ between(idx, 1, length.fsig.arg1)then
          yyy(p, org, k + 1, subseq(result, 1, len - 2) + Word.(fsig.arg1)_idx, nextvar, map)
          else if isrecordconstant.arg1 ∧ ((constantcode.arg1)_1 = Lit.0 ∨ (constantcode.arg1)_1 = Lit.1)
          ∧ between(idx, 1, length.constantcode.arg1 - 2)then
          yyy(p, org, k + 1, subseq(result, 1, len - 2) + (constantcode.arg1)_(idx + 2), nextvar, map)
          else yyy(p, org, k + 1, result + sym, nextvar, map)
        else if fsig.sym = "+(word seq, word seq)" ∧ module.sym = "word seq"then
        let arg1 = result_(len - 1)
         let arg2 = result_len
          if module.arg1 = "$words" ∧ module.arg2 = "$words"then
          yyy(p, org, k + 1, subseq(result, 1, len - 2) + Words(fsig.arg1 + fsig.arg2), nextvar, map)
          else yyy(p, org, k + 1, result + sym, nextvar, map)
        else yyy(p, org, k + 1, result + sym, nextvar, map)

function opttwoopbuiltin(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, map:worddict.seq.symbol, rep:symbol)expandresult
 let s = result
 let i = length.result + 1
  if isIdx.rep then
  let j = value.s_(i - 1)
   let x = s_(i - 2)
    if between(j, 0, length.constantcode.x - 1)then
    yyy(p, org, k + 1, subseq(result, 1, i - 3) + [(constantcode.x)_(j + 1)], nextvar, map)
    else yyy(p, org, k + 1, result + rep, nextvar, map)
  else if fsig.rep = "+(int, int)"then
  if isrecordconstant.s_(i - 2)then
   // address calculation // yyy(p, org, k + 1, result + rep, nextvar, map)
   else
    yyy(p, org, k + 1, subseq(result, 1, i - 3)
    + Lit(value.s_(i - 2) + value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "*(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) * value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "-(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) - value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "/(int, int)" ∧ value.s_(i - 1) ≠ 0 then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + Lit(value.s_(i - 2) / value.s_(i - 1)), nextvar, map)
  else if fsig.rep = "=(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + if s_(i - 2) = s_(i - 1)then Lit.1 else Lit.0, nextvar, map)
  else if fsig.rep = ">(int, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + if value.s_(i - 2) > value.s_(i - 1)then Lit.1 else Lit.0, nextvar, map)
  else if fsig.rep = "∨(bits, bits)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Lit.toint(bits.value.s_(i - 2) ∨ bits.value.s_(i - 1))], nextvar, map)
  else if fsig.rep = "∧(bits, bits)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Lit.toint(bits.value.s_(i - 2) ∧ bits.value.s_(i - 1))], nextvar, map)
  else if fsig.rep = "<<(bits, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Lit.toint(bits.value.s_(i - 2) << value.s_(i - 1))], nextvar, map)
  else if fsig.rep = ">>(bits, int)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Lit.toint(bits.value.s_(i - 2) >> value.s_(i - 1))], nextvar, map)
  else if fsig.rep = "-(real, real)"then
  yyy(p, org, k + 1, subseq(result, 1, i - 3)
   + [ Reallit.representation(casttoreal.value.s_(i - 2) - casttoreal.value.s_(i - 1))], nextvar, map)
  else yyy(p, org, k + 1, result + rep, nextvar, map)

function inline(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, nopara:int, code:seq.symbol, map:worddict.seq.symbol, options:seq.word)expandresult
 if length.code = 1 ∧ code = [ var.1] ∧ nopara = 1 then
 // function just returns result // yyy(p, org, k + 1, result, nextvar, map)
 else
  let len = length.result
  let t = backparse(result, len, nopara, empty:seq.int) + [ len + 1]
   assert length.t = nopara + 1 report"INLINE PARA PROBLEM"
   let new = if"STATE"_1 ∉ options ∧ issimple(p, nopara, code)then
   let pmap = simpleparamap(result, t, emptyworddict:worddict.seq.symbol, nopara)
     yyy(p, code, 1, empty:seq.symbol, nextvar, pmap)
   else expandinlineX(result, t, emptyworddict:worddict.seq.symbol, nopara, empty:seq.symbol, nextvar, code, p)
    yyy(p, org, k + 1, subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map)

function simpleparamap(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i = 0 then pmap
 else
  simpleparamap(s, t, add(pmap, toword.i, subseq(s, t_i, t_(i + 1) - 1)), i - 1)

function expandinlineX(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int, newcode:seq.symbol, nextvar:int, inlinecode:seq.symbol, p:program)expandresult
 // when i > 0 then assigning parameters to new local variables //
 if i = 0 then
 let r = yyy(p, inlinecode, 1, empty:seq.symbol, nextvar, pmap)
   expandresult(nextvar.r, newcode + code.r)
 else
  expandinlineX(s, t, add(pmap, toword.i, [ var.nextvar]), i - 1, subseq(s, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode, nextvar + 1, inlinecode, p)

function backparse(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
 if no = 0 then result
 else
  assert i > 0 report"back parse 1:" + toword.no + print.s + stacktrace
   assert not.isdefine.s_i report"back parse 2" + print.s
   let nopara = nopara.s_i
    let first = if nopara = 0 then i
    else
     let args = backparse(s, i - 1, nopara, empty:seq.int)
      assert length.args = nopara report"back parse 3" + print.[ s_i] + toword.nopara + "//"
     + args @ +("", toword.@e)
       args_1
    let b = if first > 1 ∧ isdefine.s_(first - 1)then
    let c = backparse(s, first - 2, 1, empty:seq.int)
      c_1
    else first
     backparse(s, b - 1, no - 1, [ b] + result)

function backparse2(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
 if no = 0 then result
 else
  assert i > 0 report"back parse 1" + toword.no + print.s
   assert not.isdefine.s_i report"back parse 2x" + print.s
   let nopara = nopara.s_i
   let first = if nopara = 0 then i
   else
    let args = backparse(s, i - 1, nopara, empty:seq.int)
     assert length.args = nopara report"back parse 3" + print.[ s_i] + toword.nopara + "//"
     + args @ +("", toword.@e)
      args_1
   let b = first
    backparse2(s, b - 1, no - 1, [ b] + result)

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol)seq.symbol
 subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

function adddefines2(s:seq.symbol, t:seq.int, i:int, nopara:int, newcode:seq.symbol, nextvar:int)seq.symbol
 if i > nopara then newcode
 else
  adddefines2(s, t, i + 1, nopara, newcode + subseq(s, t_i, t_(i + 1) - 1)
  + Define.toword(nextvar + i - 1), nextvar)

type expandresult is record nextvar:int, code:seq.symbol

function definepara(code:seq.symbol, t:seq.int, i:int, nextvar:int, newcode:seq.symbol)seq.symbol
 if i = 0 then newcode
 else
  definepara(code, t, i - 1, nextvar - 1, subseq(code, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode)

function dfg(s:symbol)seq.word
 if islocal.s then"%"
 else
  let a = last.module.s
   [ a, if a ∈ "$define local"then first."?"else first.fsig.s]

function applycode3(p:program, org:seq.symbol, k:int, code:seq.symbol, nextvar:int, map:worddict.seq.symbol)expandresult
 // should do multiply once at start of seq instead of at access to every element. Replace will add of stride //
 let totallength = nextvar + 1
 let applysym = org_k
 let seqelementkind =(typerep.parameter.(paratypes.applysym)_1)_1
 let resulttype = [(module.applysym)_1]
 let STKRECORD = symbol("STKRECORD(ptr, ptr)","builtin","ptr")
 let nullptr = symbol("nullptr","builtin","ptr")
 let GtOp = symbol(">(int, int)","builtin","boolean")
 let idxp = Idx."ptr"_1
 let idxi = Idx."int"_1
 let descleft = Lit.-2
 let theseq = Local(nextvar + 2)
 let acc = Local(nextvar + 3)
 let masteridx = Local(nextvar + 4)
 let idx = Local(nextvar + 5)
 let lastidx = Local(nextvar + 6)
 let stk = Local(nextvar + 7)
 let seqtype= Local(nextvar + 8)
 let newidx = Local(nextvar + 9)
 let Definenewidx = Define(nextvar + 9)
 let Definenewmasteridx = Define(nextvar + 10)
 let newmasteridx = Local(nextvar + 10)
 let Defineseqelement = Define(nextvar + 11)
 let seqelement = Local(nextvar + 11)
 let pseq = Fref.symbol("_(int pseq,int)", "int seq","int")
 let typesize=value.code_(-1)
 // let pl=paratypes.applysym
  let x=  [toword.typesize]+seqelementkind+resulttype 
    assert  x in [
    " 1 int int" ,"4 ptr ptr" ,"4 ptr int","5 ptr ptr","1 ptr ptr", "1 ptr int",
    " 1 int real"," 1 int ptr    ",  "3 ptr int","3 ptr ptr","5 ptr int"
  ,"  2 ptr ptr   "
  ]  
  report  "x"+x  //
 let sym = code_(-2)
 let t = backparse(code, length.code - 2, nopara.code_(length.code - 1), empty:seq.int)
 let thunk0 = code >> 1 << t_1 - 1
  assert fsig.thunk0_1 = "@acc"report"apply error" + t @ +("", toword.@e)
  + code @ +(" &br code:", print.@e)
  + thunk0 @ +(" &br code:", print.@e)
  + " &br nopara"
  + toword.nopara.code_(length.code - 1)
  + " &br"
  + t @ +("", toword.@e)
  let checknoop = if length.thunk0 = 10
  ∧ thunk0 @ +("", dfg.@e)
  = "builtin @acc $define ? builtin @e $define ? % $int 0 $int 1 % $record RECORD seq +"then
  let b2 = backparse(code, t_1 - 1, 2, empty:seq.int)
    if subseq(code, b2_1, b2_2 - 1) = [ Constant2.Emptyseq]then
    subseq(code, 1, b2_1 - 1)
    else empty:seq.symbol
  else empty:seq.symbol
   if not.isempty.checknoop then yyy(p, org, k + 1, checknoop, nextvar, map)
   else
    let zz0=parameter.(paratypes.applysym)_3
    let zz=abstracttype.zz0
     let change = seqelementkind ∈ "real"
     //  &or 
    zz &nin "encodingpair   word    symbol  myinternaltype block firstpass"
      &or ( zz in "encodingpair" &and print.parameter.zz0 in 
    ["symboltext","typename","llvmtypeele","symbolconstant","const3","stat5","llvmconst","match5"]) 
    assert change &or  not(zz in "encodingpair") &or  print.parameter.zz0 in ["seq.char"
  ,"word3"] 
     report "XJK"+print.zz0   //
   let fiveor9=if change then Lit.5 else Lit.9
    let part1 = subseq(code, 1, t_1 - 1) + [ Lit.1, Idx."int"_1, Define.totallength]
    let b = subthunk2(thunk0, 1, [ seqelement, masteridx], empty:seq.symbol)
    let thunk = [ acc] + (b << 1)
    let kk = [ Lit.1, Lit.0, descleft, nullptr, Lit.0,Lit(nextvar + 2), // the left side of the pseq remains to be processed when it is on the stack loop(seq, ptr, masteridx, idx, lastidx, stk)//
    // 1 // Loopblock("ptr," + resulttype + ", int, int, int, ptr,int, int)"), 
    // 2 if not(lastidx < idx){ idx < = lastidx then // lastidx, idx, GtOp, Lit.9
    , Lit.3, Br, 
    // 3 if not(masteridx > totallength )then exit // masteridx,Local.totallength,  GtOp, Lit.4, fiveor9, Br, 
    // 4 // acc, Exit
    , // 5 if descleft then // lastidx, descleft, EqOp, Lit.7, Lit.6, Br, 
    // 6 pop pseq continue(  b.top(stk),acc, masteridx,idx,descleft,pop(stk),seqtype // 
      stk, Lit.1, idxp, Lit.3 , idxp, acc, masteridx, idx, descleft, stk, Lit.0, idxi, seqtype, continue.7, 
    // 7 else descleft if not.ispseq.theseq then // 
    theseq, Lit.0, idxi, pseq, EqOp, Lit.10, Lit.8, Br, 
    // 8 start new seq ; continue( theseq,acc, masteridx, Lit.0, length.theseq, stk)// 
    theseq, acc, masteridx, Lit.0, theseq, Lit.1, idxi, stk,    
            theseq, Lit.0, idxi, 
     continue.7, 
    // 9 else--body--let newidx = idx + +, let newmasteridx = masteridx + +, let sequenceele = seq_(idx)continue(thunk, masteridx, idx, lastidx, seq, stk)//
    idx, Lit.1, PlusOp, Definenewidx
    , masteridx, Lit.1, PlusOp, Definenewmasteridx]
    +subblock(theseq,idx,seqtype,newidx, seqelementkind,typesize ,change )  
        +[Defineseqelement, theseq]
    + thunk
    + [ //, acc, seqelement, PlusOp, // newmasteridx, newidx, lastidx, stk, 
    seqtype, continue.7,
    // 10 descleft  continue( a.theseq,    acc,      masteridx, newidx,  descleft,  push(stk,theseq) ,Lit.0 ) //
        theseq, Lit.2, idxp, acc,masteridx, newidx,  descleft,  stk ,theseq,STKRECORD
        ,Lit.0, continue.7,
   Block(mytype.resulttype, 10)]
   //  assert subseq(x,1,3) = "1 int ptr" report  (part1 + kk) @@ +(" &br result", print.@e)
   //   yyy(p, org, k + 1, part1 + kk, nextvar + 12, map)
   
   // zz &in "seq char mytype int token templatepart  myinternaltype UTF8 encoding llvmtype
    Lcode2 slotrecord mapele liblib parc attribute2 prettyresult internalbc"  //

function  subblock(theseq:symbol,idx:symbol,
seqtype:symbol,newidx:symbol, seqelementkind:word ,typesize:int
,change:boolean ) seq.symbol  
     let threeor2=if change then Lit.3 else Lit.2
  let GtOp = symbol(">(int, int)","builtin","boolean")
   if typesize > 1  then
  [ seqtype ,Lit.1000, GtOp, Lit.2, threeor2,Br,
           theseq, newidx, Callidx.seqelementkind,Exit,
           // 3 else if  not(seq > 1 )   then  Idx(theseq,idx) //
                  seqtype,Lit.1,  GtOp, Lit.5,Lit.4,Br,
                 theseq,newidx,Lit.1,PlusOp,Idx.seqelementkind,Exit,
            // else //  
            theseq
                 ,idx, seqtype, symbol("*(int,int)","builtin","int")
                 ,Lit.2
             ,PlusOp
           , Lit.0,symbol("cast(T seq, int, int)","builtin","ptr"),Exit,
        Block(mytype.[seqelementkind],5)]
    else 
   [ seqtype ,Lit.1000, GtOp, Lit.2, threeor2,Br,
           theseq, newidx, Callidx.seqelementkind,Exit,
           theseq,newidx,Lit.1,PlusOp,Idx.seqelementkind,Exit,
        Block(mytype.[seqelementkind],3)]  

function subthunk2(s:seq.symbol, i:int, with:seq.symbol, found:seq.symbol)seq.symbol
 if i > length.s then found + s
 else if abstracttype.modname.s_i ≠ "builtin"_1 then subthunk2(s, i + 1, with, found)
 else
  let t = findindex((fsig.s_i)_1,"@e @i @exit")
  let news = if t > 3 then s else replace(s, i, with_t)
   subthunk2(news, i + 1, with, if t ∈ [ 3] ∧ isempty.found then found + s_i else found)

function maxvarused(code:seq.symbol)int maxvarused(code, 1, 0)

function maxvarused(code:seq.symbol, i:int, lastused:int)int
 if i > length.code then lastused
 else
  let s = code_i
   maxvarused(code
   , i + 1
   , max(lastused, if abstracttype.modname.s = "local"_1 then toint.(fsig.s)_1
   else if abstracttype.modname.s = "$define"_1 then toint.(fsig.s)_2 else 0))

Function depthfirst(processed:program, knownsymbols:program, alltypes:typedict, s:symbol)program depthfirst(knownsymbols, alltypes, 1, [ s], processed, code.lookupcode(knownsymbols, s), s)

function depthfirst(knownsymbols:program, alltypes:typedict, i:int, pending:seq.symbol, processed:program, code:seq.symbol, s:symbol)program
 if i > length.code then firstopt(processed, s, code, alltypes)
 else
  let sym = code_i
  let newprg =
  let sym2 = basesym.sym
   if isnocall.sym2 then processed
   else if sym2 ∈ pending then processed
   else
    let r = lookupcode(processed, sym)
     if isdefined.r then processed
     else
      let rep2 = lookupcode(knownsymbols, sym2)
       if length.code.rep2 > 0 then depthfirst(knownsymbols, alltypes, 1, pending + sym2, processed, code.rep2, sym2)else processed
   depthfirst(knownsymbols, alltypes, i + 1, pending, newprg, code, s)

________________________________

Function addoptions(code:seq.symbol, options:seq.word)seq.symbol
 if options = ""then code
 else
  let codewithoutoptions = if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)
  else code
   codewithoutoptions + Words.options + Optionsym

Function caloptions(p:program, code:seq.symbol, nopara:int, modname:seq.word, fsig:seq.word)seq.word
 let options = options.code
  if length.code = 0 then if not.isbuiltin.modname then"STATE"else""
  else if fsig = "in(int, int seq)" ∨ fsig = "in(word, word seq)"
  ∨ fsig = "∈(int, int seq)"
  ∨ fsig = "∈(word, word seq)"
  ∨ fsig = "_(int seq, int)"
  ∨ fsig = "_(word seq, int)"then
  ""
  else
   let codeonly = if last.code = Optionsym then subseq(code, 1, length.code - 2)else code
   let newoptions = options
   + if"STATE"_1 ∉ options ∧ codeonly @ ∨(false, hasstate(p, @e))then"STATE"
   else""
    newoptions
    + if"NOINLINE"_1 ∈ options ∨ length.code > 20 ∨ checkself(fsig, modname, codeonly)then
    ""
    else"INLINE"

function checkself(fsig:seq.word, module:seq.word, s:symbol)boolean fsig = fsig.s ∧ module = module.s

function checkself(fsig:seq.word, module:seq.word, s:seq.symbol)boolean s @ ∨(false, checkself(fsig, module, @e))

Function print(s:seq.symbol)seq.word s @ +("", print.@e)

function isnotOp(s:symbol)boolean fsig.s = "not(boolean)" ∧ isbuiltin.module.s

Function gtOp symbol symbol(">(int, int)","builtin","boolean")

// statebit is set on option so that adding an option doesn't auto add a inline bit //

Function issimple(p:program, nopara:int, code:seq.symbol)boolean
 between(length.code, 1, 15) ∧ (nopara = 0 ∨ checksimple(p, code, 1, nopara, 0))

Function hasstate(p:program, s:symbol)boolean
 if isconstantorspecial.s then false
 else if fsig.s = "_(int seq, int)" ∨ fsig.s = "_(word seq, int)"then
 false
 else
  let d = lookupcode(p, s)
   if isdefined.d then"STATE"_1 ∈ options.code.d else 
     if isbuiltin.module.s &and fsig.s &ne "setfld(int, T seq, T)" then false else true

function checksimple(p:program, code:seq.symbol, i:int, nopara:int, last:int)boolean
 // check that the parameters occur in order and they all occur exactly once //
 // Any op that may involve state must occur after all parameters //
 if i > length.code then last = nopara
 else if nopara < last ∧ // should also check for loopblock // hasstate(p, code_i)then // state op between parameters // false
 else
  let rep = code_i
   if islocal.rep then
   let parano = toint.(fsig.rep)_1
     if parano = last + 1 then checksimple(p, code, i + 1, nopara, last + 1)else false
   else checksimple(p, code, i + 1, nopara, last)

---------------------------

Function pass2(placehold:program, alltypes:typedict)program toseq.toset.placehold @ depthfirst(emptyprogram, placehold, alltypes, @e)

Function uses(p:program, roots:set.symbol)set.symbol uses(p, empty:set.symbol, roots)

Function defines(p:program, roots:set.symbol)seq.symbol toseq.roots @ +(empty:seq.symbol, defines2(p, @e))

function uses(p:program, s:symbol)seq.symbol
 let d = code.lookupcode(p, s)
  if isempty.d then constantcode.s else d

function uses(p:program, processed:set.symbol, toprocess:set.symbol)set.symbol
 if isempty.toprocess then processed
 else
  let q = asset(toseq.toprocess @ +(empty:seq.symbol, uses(p, @e)))
   uses(p, processed ∪ toprocess, q - processed)

function defines2(p:program, s:symbol)seq.symbol
 if isconstantorspecial.s ∨ isbuiltin.module.s ∨ isabstract.modname.s then empty:seq.symbol
 else
  let d = code.lookupcode(p, s)
   if isempty.d then empty:seq.symbol else [ s]