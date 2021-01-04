Module breakblocks

Part of pass2

use standard

use seq.symbol

use seq.block

use stack.block

use symbol

use seq.caseblock

use otherseq.caseblock

use otherseq.block


Function print(s:seq.symbol)seq.word s @ +("", print.@e)

Function hasstate(p:program, s:symbol)boolean
 if isconstantorspecial.s then false
 else if fsig.s = "_(int seq, int)" ∨ fsig.s = "_(word seq, int)"then
 false
 else
  let d = lookupcode(p, s)
   if isdefined.d then"STATE"_1 ∈ getoption.code.d else 
     if isbuiltin.module.s &and fsig.s &ne "setfld(int, T seq, T)" then false else true


type block is record kind:word, blkno:int, label1:int, label2:int, code:seq.symbol, subblks:seq.block

function block(kind:word, blkno:int, label1:int, label2:int, code:seq.symbol)block block(kind, blkno, label1, label2, code, empty:seq.block)


Function breakblocks(p:program, code:seq.symbol, self:symbol, alltypes:typedict)seq.symbol
 let a = breakblocks(p, code, 1, 1, empty:seq.symbol, empty:stack.block)
  if length.a = 1 then code.a_1
  else if kind.a_1 ≠ "LOOPBLOCK"_1 ∧ a @ ∨(false, tailrecursion(self, @e))then
  // tail recursion //
   let nopara = nopara.self
   let a2 = a @ +(empty:seq.block, preparetail(nopara, self, continue.nopara, @e))
   let plist = arithseq(nopara, 1, 1) @ +(empty:seq.symbol, Local.@e)
   let entry = block("LOOPBLOCK"_1, 0, blkno.a2_1, 0, plist + Lit(nopara + 1)
   + Loopblock(paratypes.self @ list("",",", [ kind.gettypeinfo(alltypes, @e)]) + ", int)"))
    ascode(p, [ entry] + a2, self)
  else ascode(p, a, self)
  
 
  
function tailrecursion(self:symbol, b:block)boolean
 kind.b = "EXIT"_1 ∧ (code.b)_(length.code.b - 1) = self
 
function preparetail(nopara:int, self:symbol, continue:symbol, b:block)block
 let code = adjustvar(code.b, nopara, 1, empty:seq.symbol)
  if kind.b = "EXIT"_1 ∧ code_(length.code - 1) = self then
  block("CONTINUE"_1, blkno.b, label1.b, label2.b, subseq(code, 1, length.code - 2) + continue)
  else block(kind.b, blkno.b, label1.b, label2.b, code)

function adjustvar(s:seq.symbol, delta:int, i:int, result:seq.symbol)seq.symbol
 if i > length.s then result
 else
  let a = s_i
   if islocal.a then
   adjustvar(s, delta, i + 1, result + Local(toint.(fsig.a)_1 + delta))
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

function convertexits(label1:int, label2:int, b:block)block
 if kind.b ∈ "BR JMP"then b
 else
  assert kind.b = "EXIT"_1 report"unexpected block type" + kind.b
   if length.code.b = 2 ∧ isconst.(code.b)_1 then
   let target = if Lit0 = (code.b)_1 &or Litfalse = (code.b)_1 then label2 else label1
     block("JMP"_1, blkno.b, target, target, empty:seq.symbol)
   else
    block("BR"_1, blkno.b, label1, label2, subseq(code.b, 1, length.code.b - 1) + [ Lit.0, Lit.0, Br])


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
    
Function backparse(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
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


function ascode(p:program, l:seq.block, i:int, assigned:seq.block, result:seq.symbol)seq.symbol
 if i > length.assigned then result + Lit.length.assigned
 else
  let blk = assigned_i
   if kind.blk ∈ "BR"then
   let a2 = findblk2(l, 1, label2.blk)
    let exp = checkforcase(p, blk)
     if // false &and // not.isempty.exp then
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
        let var = if islocal.last.exp then last.exp else Local.1000
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

function findblk2(l:seq.block, i:int, blkno:int)block
 assert i ≤ length.l report"did not find block" + stacktrace
 let blk = l_i
  if blkno.blk = blkno then
  if kind.blk = "JMP"_1 then findblk2(l, 1, label1.blk)else blk
  else findblk2(l, i + 1, blkno)


function caseblock(truelabel:int, orgblkno:int, rep:symbol)caseblock
 let key = if islit.rep then value.rep
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
    ∧ ((constantcode.rep)_1 = Lit.0 ∨ (constantcode.rep)_1 = Lit.1)report"not a standard seq" + print.code
     subseq(constantcode.rep, 3, length.constantcode.rep) @ +(empty:seq.caseblock, caseblock(label, 0, @e))
  // now check to see if following block is a case block //
  let newblock = findblk2(l, 1, label2.blk)
   if iscaseblock.newblock ∧ subseq(code.newblock, 1, length.code.newblock - 5) = exp 
    &and  l @ +(0, indegree(blkno.newblock,@e))=1 then
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
   , [ block("BRC"_1, nextblklabel, upperlabel, nextblklabel + 1, [ var, keysig.middle, GtOp, Lit0, Lit0, Br]), block("BRC"_1, nextblklabel + 1, truelabel.middle, lowerlabel, [ var, keysig.middle, EqOp, Lit0, Lit0, Br])]
   + allocated.low
   + allocated.high)
   
function   indegree(label:int,b:block) int
   if kind.b ="JMP"_1 then if label1.b=label then 1 else 0
   else if kind.b ∈ "BR BRC "then  if label1.b=label &or label2.b=label  then 1 else 0 
   else 0
   
function print(b:block)seq.word
 " &br >>>>" + toword.blkno.b +":" +kind.b   
 + if kind.b ∈ "BR BRC"then
 [ toword.label1.b, toword.label2.b]
  + print.code.b
 else if kind.b = "BRBLKS"_1 then
 "(" + subblks.b @ +("", print.@e) + ")"
 else if kind.b ∈ "EXIT CONTINUE"then print.code.b
 else if kind.b = "JMP"_1 then [ toword.label1.b] + print.code.b else"??"

 