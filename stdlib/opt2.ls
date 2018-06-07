module opt2

use buildtree

use passcommon

use seq.int

use seq.tree.cnode

use seq.word

use set.word

use stdlib

use tree.cnode

Function opt2(t:tree.cnode)tree.cnode 
 if inst.t ="FINISHLOOP"_1 
  then let x = removeRECORD.t 
   if inst.x ="nogo"_1 then tree(label.t, @(+, opt2, empty:seq.tree.cnode, sons.t))else x 
  else tree(label.t, @(+, opt2, empty:seq.tree.cnode, sons.t))

function removeRECORD(loop:tree.cnode)tree.cnode 
 let lb = loop_1 
  let first = toint.arg(lb_nosons.lb)
  if not(inst(loop_2)="if"_1)
  then nogo 
  else let checked = asset(look(first, loop_2_3)+ look(first, loop_2_1))
  // assert nosons.loop = 5 report toseq.checked +"FIRST"+ toword.first + printb(0, loop)// 
  let b = toseq(checked - asset."1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25")
  // assert false report a +"/"+ b // 
  if length.b ≠ 1 
  then nogo 
  else let z = decode(b_1)
  let x = decode("X"_1)_1 
  let i = findindex(x, z)
  let candidate = encodeword.subseq(z, 1, i - 1)
  if candidate in checked ∨ not(cnode("LOCAL"_1, candidate)= label(loop_2_2))
  then // Candidate use has whole record rather than components // nogo 
  else let expand = [ toint.candidate]
  let size = toint.encodeword.subseq(z, i + 1, 100)
  let map = constantseq(first, 0)+(size - 1)
  let if1 = splitrecord(first, map, expand, loop_2_1)
  let if2 = tree(cnode("RECORD"_1,"0"_1), @(+, makelocal, empty:seq.tree.cnode, arithseq(size, 1, first)))
  let if3 = splitrecord(first, map, expand, loop_2_3)
  // assert false report a +"/"+ b + printb(0, loop)// 
  let newloopblock = tree(label.lb, @(+, fixloopinit(sons.lb, size, expand, first), empty:seq.tree.cnode, arithseq(nosons.lb - 1, 1, 1))+ lb_nosons.lb)
  let newloop = tree(label.loop, [ newloopblock, tree(label(loop_2), [ if1, if2, if3])])
  assert true report"B"+ printb(0, newloop)+">>>"+ printb(0, loop)
  newloop

function makelocal(i:int)tree.cnode tree.cnode("LOCAL"_1, toword.i)

function nogo tree.cnode tree.cnode("nogo"_1,"0"_1)

function look(first:int, t:tree.cnode)seq.word 
 // returns all local variables that are not accessed like"IDXUC(LOCAL x, LIT y)".Also returns"jXi"where j is loop variable of form RECORD(s1, s2,... , si)// 
  if inst.t ="CONTINUE"_1 
  then @(mergecheckrecord.first, checkrecord,"", sons.t)+ @(+, look.first,"", sons.t)
  else if inst.t ="LOCAL"_1 
  then [ arg.t]
  else if inst.t ="IDXUC"_1 ∧ inst(t_2)="LIT"_1 ∧ inst(t_1)="LOCAL"_1 
  then""
  else @(+, look.first,"", sons.t)

function checkrecord(t:tree.cnode)word 
 if inst.t ="SET"_1 
  then checkrecord(t_2)
  else if inst.t in"RECORD MRECORD"then toword.nosons.t else"X"_1

function mergecheckrecord(first:int, s:seq.word, t:word)seq.word 
 if t ="X"_1 
  then s + toword(first + length.s)
  else s + merge([ toword(first + length.s)]+"X"+ t)

function splitrecord(first:int, map:seq.int, expand:seq.int, t:tree.cnode)tree.cnode 
 let inst = inst.t 
  if inst ="LOCAL"_1 
  then tree.cnode(inst, toword.mapit(map, arg.t))
  else if inst ="SET"_1 
  then tree(cnode(inst, toword.mapit(map, arg.t)), [ splitrecord(first, map, expand, t_1), splitrecord(first, map, expand, t_2)])
  else if inst ="IDXUC"_1 ∧ inst(t_2)="LIT"_1 ∧ inst(t_1)="LOCAL"_1 ∧ toint.arg(t_1)in expand 
  then tree.cnode("LOCAL"_1, toword(mapit(map, arg(t_1))+ toint.arg(t_2)))
  else if inst ="CONTINUE"_1 
  then if inst(t_1)="SET"_1 
   then // push CONTINUE down the tree // 
    let newt = tree(label(t_1), [ t_1_1, tree(label.t, [ t_1_2]+ subseq(sons.t, 2, nosons.t))])
    splitrecord(first, map, expand, newt)
   else assert inst(t_1)in"RECORD MRECORD"report"CONT"+ printb(0, t)
   tree(label.t, @(+, handlecontinue(first, map, expand, t), empty:seq.tree.cnode, arithseq(nosons.t, 1, 1)))
  else tree(label.t, @(+, splitrecord(first, map, expand), empty:seq.tree.cnode, sons.t))

function handlecontinue(first:int, map:seq.int, expand:seq.int, t:tree.cnode, son:int)seq.tree.cnode 
 if son + first - 1 in expand 
  then if inst(t_son)="MRECORD"_1 
   then [ splitrecord(first, map, expand, t_son_2)]
   else @(+, splitrecord(first, map, expand), empty:seq.tree.cnode, sons(t_son))
  else [ splitrecord(first, map, expand, t_son)]

function fixloopinit(loopsons:seq.tree.cnode, size:int, expand:seq.int, first:int, i:int)seq.tree.cnode 
 let son = loopsons_i 
  if first + i - 1 in expand 
  then assert inst.son in"PARAM LOCAL RECORD CRECORD"report"opt2 problem"+ printb(0, son)
   @(+, fixloopinit.son, empty:seq.tree.cnode, arithseq(size, 1, 0))
  else [ son]

function fixloopinit(t:tree.cnode, i:int)tree.cnode 
 tree(cnode("IDXUC"_1,"0"_1), [ t, tree.cnode("LIT"_1, toword.i)])

function mapit(map:seq.int, arg:word)int 
 let i = toint.arg 
  if i > length.map then last.map + i else i + map_i

Function printb(level:int, t:tree.cnode)seq.word 
 // for printing code tree // 
  let inst = inst.t 
  {"&br"+ constantseq(level,"_"_1)+ if inst ="if"_1 
   then"if"+ printb(level + 1, t_1)+"&br"+ constantseq(level,"_"_1)+"then"+ printb(level + 1, t_2)+"&br"+ constantseq(level,"_"_1)+"else"+ printb(level + 1, t_3)
   else(if inst in"PARA PARAM LIT CONST LOCAL FREF WORD FLAT"
    then [ inst, arg.t]
    else if inst in"CALL CALLB"
    then [ inst, toword.nosons.t, arg.t]
    else if inst ="SET"_1 then [ inst, arg.t]else [ inst, toword.nosons.t])+ @(+, printb(level + 1),"", sons.t)}

_____________

Function removerecords(x:tree.cnode)tree.cnode 
 let t = tree(label.x, @(+, removerecords, empty:seq.tree.cnode, sons.x))
  // assert not(inst.t ="SET"_1 ∧ inst.t_1 in"CRECORD RECORD"∧ label.t_1_1 = label.t_1_2)report(if check(arg.t, false, t_2)then"check"else"")+ printb(0, t_2)+"VAR"+ arg.t // 
  if inst.t ="SET"_1 ∧ inst(t_1)in"CRECORD RECORD"
  then let chk = check(arg.t, false, t_2)
   if chk = 10000 then t else fix2(t, empty:seq.tree.cnode, 1, chk + 1)
  else t

function check(var:word, parent:boolean, t:tree.cnode)int 
 // returns 10000 if does not check. Returns max var used in tree if does checkout. parent indicates if the parent is IDXUC // 
  if inst.t ="LOCAL"_1 ∧ arg.t = var 
  then if parent then toint.arg.t else 10000 
  else @(max, check(var, inst.t ="IDXUC"_1), if inst.t ="SET"_1 
   then toint.arg.t 
   else if inst.t ="LOOPBLOCK"_1 then toint.arg(t_nosons.t)+ nosons.t - 2 else 0, sons.t)

function fix2(t:tree.cnode, replacements:seq.tree.cnode, i:int, varbase:int)tree.cnode 
 // replaces"fld1 fld2 RECORD 2 exp SET y"with"fld1 fld2 exp SET v2 SET v1"// 
  if i > nosons(t_1)
  then fix3(arg.t, replacements, t_2)
  else let s = t_1_i 
  if inst.s in"LIT LOCAL PARAM FREF"
  then fix2(t, replacements + s, i + 1, varbase)
  else let var = toword(varbase + i)
  tree(cnode("SET"_1, var), [ s, fix2(t, replacements + tree.cnode("LOCAL"_1, var), i + 1, varbase)])

function fix3(var:word, replacements:seq.tree.cnode, t:tree.cnode)tree.cnode 
 // replaces IDXUC(LOCAL var, LIT i)with replacements_(i + 1)// 
  if inst.t ="IDXUC"_1 ∧ inst(t_2)="LIT"_1 ∧ inst(t_1)="LOCAL"_1 ∧ arg(t_1)= var 
  then replacements_(toint.arg(t_2)+ 1)
  else if inst.t ="SET"_1 ∧ inst.t = var 
  then t 
  else tree(label.t, @(+, fix3(var, replacements), empty:seq.tree.cnode, sons.t))

___________________

function returnsrecord(t:tree.cnode)int 
 if inst.t ="RECORD"_1 
  then nosons.t 
  else if inst.t ="MRECORD"_1 
  then toint.arg(t_2)
  else if inst.t ="SET"_1 
  then returnsrecord(t_2)
  else if inst.t ="if"_1 
  then let a = returnsrecord(t_2)
   if a = 0 then 0 else if a = returnsrecord(t_3)then a else 0 
  else 0

Function hoistRecord(t:tree.cnode)tree.cnode 
 if nosons.t = 0 
  then t 
  else let sons = @(+, hoistRecord, empty:seq.tree.cnode, sons.t)
  if inst.t ="if"_1 
  then let a = returnsrecord.t 
   if a > 0 
   then tree(cnode."MRECORD", [ replacerecord(a, t), tree.cnode("FIRSTVAR"_1, toword.a)])
   else tree(cnode."if", sons)
  else tree(label.t, sons)

function localtree(i:int)tree.cnode tree.cnode("LOCAL"_1, toword.i)

function replacerecord(size:int, t:tree.cnode)tree.cnode 
 if inst.t in"RECORD"
  then tree(cnode."MSET", sons.t)
  else if inst.t ="MRECORD"_1 
  then t_1 
  else if inst.t ="if"_1 
  then tree(cnode."if 4", [ t_1, replacerecord(size, t_2), replacerecord(size, t_3), tree.cnode("FIRSTVAR"_1, toword.size)])
  else assert inst.t ="SET"_1 report"replacerecord"+ inst.t 
  tree(label.t, [ t_1, replacerecord(size, t_2)])

