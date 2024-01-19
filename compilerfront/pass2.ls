Module pass2

use backparse

use set.arc.int

use graph.int

use otherseq.int

use set.int

use seq.mytype

use standard

use symbol2

use seq.symbol

use symbol

use seq.arc.int

use otherseq.seq.symbol

use encoding.track

use otherseq.track

use otherseq.track2

Export type:expandresult

Export code(expandresult) seq.symbol

Export nextvar(expandresult) int

Export expandresult(int, seq.symbol) expandresult

Function reorgwhen int 6000

Function isverysimple(nopara:int, code:seq.symbol) boolean
if code = [Local.1] ∧ nopara = 1 then true
else
 for isverysimple = n.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do
  next(
   if idx ≤ nopara then sym = Local.idx else not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
   , idx + 1
  ),
 isverysimple

Function ismember(s:symbol) boolean
name.module.s = 1#"seq" ∧ name.s = 1#"∈" ∧ 1#paratypes.s ∈ [typeint, typeword]

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol) seq.symbol
subseq(s, 1, start - 1) + value + subseq(s, start + length, n.s)

type expandresult is nextvar:int, code:seq.symbol

function isconstorlocal(p:symbol) boolean isconst.p ∨ islocal.p

Function expandIdxNB(
acc:seq.symbol
, sym:symbol
, nextvar:int
, typedict:typedict
) expandresult
{Expands idxNB}
let acc1 =
 if isconstorlocal.1^acc then
  if isconstorlocal.2^acc then {Neither argument is expression} acc
  else {first argument is expression} acc >> 1 + Define.nextvar + Local.nextvar + 1^acc
 else
  let para2 = backparse3(acc, n.acc, true),
  if isconstorlocal.(para2 - 1)#acc then
   {second argument is expression} subseq(acc, 1, para2 - 2)
    + subseq(acc, para2, n.acc)
    + Define(nextvar + 1)
    + (para2 - 1)#acc
    + Local(nextvar + 1)
  else
   {both arguments are expressions} subseq(acc, 1, para2 - 1)
    + Define(nextvar + 2)
    + subseq(acc, para2, n.acc)
    + Define(nextvar + 1)
    + Local(nextvar + 2)
    + Local(nextvar + 1)
let index = 1^acc1
let theseq = 2^acc1
let theseqtype = basetype(1#paratypes.sym, typedict)
let seqtype = Local.nextvar
let newcode = acc1 >> 2 + indexseqcode(seqtype, theseq, index, theseqtype),
expandresult(nextvar + 3, newcode)

function isemptysymbol(sym:symbol) boolean
if not.isconst.sym then false
else if sym = Words."" then true
else if not.isrecordconstant.sym then false
else
 let full = fullconstantcode.sym,
 isSequence.1#full ∧ nopara.1#full = 0

Function checkemptycat(sym:symbol, result:seq.symbol) seq.symbol
if name.module.sym ∈ "seq" ∧ name.sym ∈ "+" ∧ nopara.sym = 2 then
 let p = paratypes.sym,
 if 1#p = 2#p then
  if isemptysymbol.1^result then result >> 1
  else
   let para2 = backparse3(result, n.result, true),
   if isemptysymbol.(para2 - 1)#result then subseq(result, 1, para2 - 2) + subseq(result, para2, n.result)
   else empty:seq.symbol
 else empty:seq.symbol
else empty:seq.symbol

function indexseqcode(
seqtype:symbol
, theseq:symbol
, idx:symbol
, theseqtype:mytype
) seq.symbol
{seqtype will be a basetype}
let seqparameter = parameter.theseqtype
let elementtype =
 if seqparameter ∈ [typeint, typereal, typeboolean, typebyte] then seqparameter
 else typeptr
let maybepacked = seqparameter ∈ packedtypes ∨ seqparameter = typebyte
let callidx = symbol(internalmod, "callidx", [seqof.elementtype, typeint], elementtype)
let idxseq = symbol(internalmod, "idxseq", seqof.elementtype, typeint, elementtype),
[
 theseq
 , GetSeqType
 , Define.value.seqtype
 , Start.elementtype
 , seqtype
 , Lit.1
 , GtOp
 , Br2(1, 2)
]
 + [theseq, idx, callidx, Exit]
 + if maybepacked then
 [seqtype, Lit.1, EqOp, Br2(2, 1)]
  + [theseq, idx, idxseq, Exit]
  + [
  theseq
  , idx
  , symbol(internalmod, "packedindex", theseqtype, typeint, elementtype)
  , Exit
  , EndBlock
 ]
else [theseq, idx, idxseq, Exit, EndBlock]

type track is key:int, sym:symbol

type track2 is count:int, sym:symbol

Function track(s:symbol) encoding.track encode.track(n.encodingdata:track + 1, s)

function hash(t:track) int key.t

function =(a:track, b:track) boolean key.a = key.b

function >1(a:track, b:track) ordering sym.a >1 sym.b ∧ key.a >1 key.b

function >1(a:track2, b:track2) ordering count.a >1 count.b

function %(t:track2) seq.word %.count.t + %.sym.t

Function trackresults seq.word
for acc = empty:seq.track2, count = 0, last = Lit.0, t ∈ sort.encodingdata:track
do
 if last = sym.t then next(acc, count + 1, sym.t)
 else next(setinsert(acc, track2(count, last)), 1, sym.t),
%("/br", setinsert(acc, track2(count, last)))

----------------

function adjustvar(s:seq.symbol, delta:int) seq.symbol
for acc = empty:seq.symbol, a ∈ s
do
 if islocal.a then acc + Local(value.a + delta)
 else if isdefine.a then acc + Define(value.a + delta)
 else if isloopblock.a then acc + Loopblock(paratypes.a, firstvar.a + delta, resulttype.a)
 else acc + a,
acc

Function checkLoopIsNoOp(syms:seq.symbol, parts:seq.seq.symbol, self:symbol) seq.symbol
let prior = syms >> 1
let loop = 1^syms,
if n.parts = 3
∧ n.3#parts ∈ [13, 14]
∧ 2#parts = [Lit.0, Exit]
∧ nopara.loop = 2
∧ prior << (n.prior - 1) = [Lit.0]
∧ isseq.1#paratypes.loop then
 let lastpart = 3#parts
 let theseqtype = resulttype.3^lastpart,
 let theseq = 5#lastpart,
 if %.parameter.theseqtype ∈ ["packed2", "ptr"] then {???? hack! should at least check to see if cat is defined.} empty:seq.symbol
 else
  let firstvar = firstvar.loop
  let idx = firstvar + 1
  let seqlen =
   if isrecordconstant.theseq then Lit.nopara.1^fullconstantcode.theseq
   else if iswords.theseq then Lit.n.worddata.theseq
   else Local(firstvar - 1),
  let symidx = 7#lastpart,
  if nopara.symidx ≠ 2 then empty:seq.symbol
  else
   let idxNB = symbol(internalmod, "idxNB", paratypes.symidx, resulttype.symidx)
   let cat =
    if n.lastpart = 14 then
     [
      Sequence(resulttype.symidx, 1)
      , symbol(moduleref("* seq", parameter.theseqtype), "+", theseqtype, theseqtype, theseqtype)
     ]
    else
     [
      symbol(
       moduleref("* seq", parameter.theseqtype)
       , "+"
       , theseqtype
       , parameter.theseqtype
       , theseqtype
      )
     ],
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
   if [Local.idx, seqlen, EqOp] = 1#parts >> 1 ∧ lastpart = matchbrf then
    let newsyms =
     if prior << (n.prior - 3) = [GetSeqLength, Define(firstvar.loop - 1), Lit.0] then syms >> 4
     else if isconst.theseq ∧ 1^prior = Lit.0 then syms >> 2 + theseq
     else empty:seq.symbol,
    if isempty.newsyms then empty:seq.symbol
    else
     newsyms
      + symbol(moduleref("* seq", parameter.theseqtype), "+", theseqtype, theseqtype, theseqtype)
      + Define.firstvar
      + Lit.0
   else empty:seq.symbol
else empty:seq.symbol

assert isempty.z  /or %.self /in ["llvm:% (llvmtype) seq.word","llvm:function (seq.llvmtype) llvmtype","UTF8:tocharseq2 (seq.int) seq.char"
,"UTF8:tointseq (seq.char) seq.int"
,"UTF8:tocharseq (seq.int) seq.char"
,"persistant:hash (const3) int","llvm:typerecords seq.seq.int"
,"word:towordseq (seq.alphaword) seq.word"
,"llvm:AGGREGATE (seq.slot) slot"
,"compileTimeT.callconfig:buildargs:callconfig (seq.symbol) seq.int"
,"compileTimeT.callconfig:tocode:callconfig (int, mytype, typedict) seq.symbol"
,"word:alphasort (seq.seq.word) seq.seq.word"
,"word:toalphaseq (seq.word) seq.alphaword"
,"set.mytype:findelement2 (set.mytype, mytype) set.mytype"
,"set.symbol:findelement2 (set.symbol, symbol) set.symbol"
,"set.arc.symbol:findelement2 (set.arc.symbol, arc.symbol) set.arc.symbol"
,"object01:inrec (seq.seq.int) ptr"
,"typedict:asseqseqmytype (typedict) seq.seq.mytype"
,"set.int:findelement2 (set.int, int) set.int"
,"test11a:checkprec seq.word"
,"set.myExport:findelement2 (set.myExport, myExport) set.myExport"
,"set.sym/modref:findelement2 (set.sym/modref, sym/modref) set.sym/modref"
,"prettycompilerfront:transform2 (midpoint, seq.word, seq.word, seq.word, boolean, boolean, seq.word, boolean, boolean, seq.file, seq.file, seq.word) seq.file"
,"opttests:optest16 (seq.char) seq.int"
,"genEnumeration:enumerate (seq.word, seq.word, boolean, seq.word) seq.seq.word"] report %.self
assert name.self /nin "loopisnoop"  /or n.3#parts /in [1400 ] report %.n.3#parts+%.self+%.syms+%n.parts 
+"/br RRR"+%.z
z

Function isMemberCode(
result:seq.symbol
, arg:symbol
, nextvar:int
, nonew:boolean
) seq.symbol
{nonew = true means a no new variable was created for the expression}
let z = seqelements.1^result
let var = if nonew then arg else Local.nextvar
let newcode =
 if isempty.z then [Litfalse]
 else if n.z = 1 then [var, 1#z, EqOp]
 else
  let t = n.z + 2
  for acc = [Start.typeboolean], idx = 2, w ∈ z >> 1
  do next(acc + [var, w, EqOp] + Br2(t - idx, 1), idx + 1),
  acc + [var, 1^z, EqOp, Exit, Littrue, Exit, EndBlock],
if nonew then result >> 2 + newcode else result >> 1 + Define.nextvar + newcode

type stkele is part:seq.symbol, blkparts:seq.seq.symbol

Export type:stkele

Export stkele(part:seq.symbol, blkparts:seq.seq.symbol) stkele

Export part(stkele) seq.symbol

Export blkparts(stkele) seq.seq.symbol

Function checkrecursive(
parts:seq.seq.symbol
, self:symbol
, stkpart:seq.symbol
, nojumptable:boolean
) seq.symbol
let nopara = nopara.self
for changed = false, acc = empty:seq.seq.symbol, p ∈ parts
do
 if 1^p = Exit ∧ 2^p = self then
  let newacc =
   if changed then acc
   else
    for acc2 = empty:seq.seq.symbol, p2 ∈ acc
    do acc2 + adjustvar(p2, nopara),
    acc2,
  next(true, newacc + adjustvar(p >> 2 + continue.nopara, nopara))
 else next(changed, acc + (if changed then adjustvar(p, nopara) else p)),
if changed then
 for pvar = empty:seq.symbol, i ∈ arithseq(nopara.self, 1, 1)
 do pvar + Local.i,
 [Lit.0]
  + pvar
  + Loopblock(paratypes.self, nopara + 1, resulttype.self)
  + adjustvar(subseq(stkpart, 2, n.stkpart - 1), nopara)
  + blocktocode(empty:seq.symbol, acc, self, nojumptable)
else empty:seq.symbol

function ⊻(a:boolean, b:boolean) boolean if a then not.b else b

Function adjustbr(parts:seq.seq.symbol, amount:int) seq.seq.symbol
{adjust branches that jump after what has been processed in outer block}
for tmp = parts, place = 1, e ∈ parts
do
 let x = 1^e,
 if isbr.x then
  let adjustt = if brt.x + place > n.tmp + 1 then amount - 1 else 0
  let adjustf = if brf.x + place > n.tmp + 1 then amount - 1 else 0,
  if adjustt + adjustf ≠ 0 then next(replace(tmp, place, e >> 1 + Br2(brt.x + adjustt, brf.x + adjustf)), place + 1)
  else next(tmp, place + 1)
 else next(tmp, place + 1),
tmp

use otherseq.arc.int

function %(a:arc.int) seq.word "(^(tail.a)^(head.a))"

use seq.int

use seq.seq.int

use set.symbol

Function blocktocode(
result:seq.symbol
, parts0:seq.seq.symbol
, self:symbol
, nojumptable:boolean
) seq.symbol
let first = 1#parts0,
if isExit.1^first then result >> 1 + first >> 1
else
 let z =
  if 2^first = Littrue then brt.1^first
  else if 2^first = Litfalse then brf.1^first
  else 0,
 if z > 0 then
  {assert false report" KKKK"+%.z+%n.parts0}
  blocktocode(result, parts0 << z, self, nojumptable)
 else
  {first part will be Br2 or Jmp}
  for
   parts = empty:seq.seq.symbol
   , reached = asset.[1]
   , arcs5 = empty:set.arc.int
   , brs = empty:seq.int
   , p ∈ parts0
  do
   let place = n.parts + 1,
   if place ∉ reached then next(parts + [Lit.0], reached, arcs5, brs)
   else if not.isbr.1^p then
    let last = 1^p,
    if isJmp.last then
     let tmp = value.last - 4
     for
      new = empty:seq.symbol
      , b = reached
      , islabel = false
      , e ∈ subseq(p, n.p - value.last + 2, n.p - 1)
     do
      {assert n.new /le tmp report %.tmp+%.n.new+%.islabel+%.e+" X^(new)"}
      if not.islabel then next(new + e, b, true)
      else
       let val = value.e
       let c = chain(place + value.e, parts0),
       let newislabel = tmp = n.new,
       if val = c - place then next(new + e, b + c, newislabel)
       else next(new + Lit(c - place), b + c, newislabel),
     {"^(tmp) JUMP"+%.b+"
     /p"+%.p+%.new}
     next(parts + p, b, arcs5, brs)
    else next(parts + p, reached, arcs5, brs)
   else
    let last = 2^p
    let newpart =
     if last = JumpOp then p >> 2 + EqOp + 1^p
     else if isIntLit.last then p >> 2 + 4^(1^parts) + last + EqOp + 1^p
     else
      let brOp = 1^p,
      if last = NotOp then p >> 2 + Br2(brf.brOp, brt.brOp) else p
    let brt = chain(place + brt.1^newpart, parts0),
    let brf = chain(place + brf.1^newpart, parts0),
    next(
     parts + (newpart >> 1 + Br2(brt - place, brf - place))
     , reached + brt + brf
     , if brt = brf then arcs5 + arc(brt, place)
     else arcs5 + arc(brt, place) + arc(brf, place)
     , if n.newpart = 2 ∧ 1#newpart ∈ [Littrue, Litfalse] then brs else brs + place
    )
  {map contains location from end of block. Branch chains have been removed from block.}
  for
   final = empty:seq.symbol
   , placements = empty:set.fromEnd
   , map = arithseq(n.parts, 0, 0)
   , toprocess = brs
  while not.isempty.toprocess
  do
   let place = 1^toprocess
   let part = place#parts
   let brtrue = (place + brt.1^part)#parts
   let brfalse = (place + brf.1^part)#parts
   for
    run = [place]
    , brtrues = empty:seq.int
    , vals = empty:seq.symbol
    , runstart = empty:seq.symbol
    , more = n.part = 4 ∧ 2^part = EqOp ∧ isIntLit.3^part ∧ islocal.4^part
   while more
   do
    let r = findelement2(arcs5, arc(1^run, 0)),
    if n.r ≠ 1 then
     {this part is reachable from more than one point so end run}
     next(run, brtrues, vals, runstart, false)
    else
     let idx = head.1#r
     let tmp = idx#parts,
     if brf.1^tmp + idx = tail.1#r
     ∧ n.tmp > 3
     ∧ 4^tmp = 4^part
     ∧ isIntLit.3^tmp
     ∧ 2^tmp = EqOp then next(run + idx, [idx + brt.1^tmp] + brtrues, vals + 3^tmp, tmp, n.tmp = 4)
     else next(run, brtrues, vals, runstart, false)
   {assert n.run < 13 report" MM"+%.run+%.toseq.arcs5+%n.parts}
   {assert n.parts /ne 7 /or 2#2#parts /ne Lit.7777 report" LLL"+%n.parts}
   let haverun = n.run ≥ 3 ∧ not.nojumptable
   assert not.haverun ∨ n.asset(vals + 3^part) = n.vals + 1 report "Error: Function^(self) has duplicate value in branch table:" + %(vals + 3^part),
   for
    map1 = map
    , acc = empty:seq.int
    , finalp0 = final
    , p0 = placements
    , e ∈ [place + brf.1^part, place + brt.1^part]
     + (if haverun then reverse.brtrues else empty:seq.int)
   do
    let c5 = check5(map1, e, parts)
    for map2 = map1, finalp1 = finalp0, p1 = p0, e1 ∈ c5
    do
     if e1#map2 ≠ 0 then next(map2, finalp1, p1)
     else
      let newpart = makePart(map2, n.p1, e1#parts, e1)
      let j = lookup(p1, newpart, "A"),
      if j = 0 then next(replace(map2, e1, n.p1 + 1), newpart + finalp1, p1 + newpart)
      else next(replace(map2, e1, j), finalp1, p1),
    next(map2, acc + e#map2, finalp1, p1),
   if haverun then
    if false ∧ Lit.3333 ∈ finalp0 then
     let jmp = Jmp(2 * n.run + 3)
     let lastbranch = 1^((1#run)#parts)
     for
      ss = [{default case} Lit(n.p0 - (1#run + brf.lastbranch)#map1 + 1)]
      , e ∈ {brtrues} run
     do
      let ecode = e#parts,
      [3^ecode, Lit(n.p0 - (e + brt.1^ecode)#map1 + 1)] + ss,
     let final2 = (1^run)#parts >> 3 + jmp + ss + jmp + final,
     next(
      final2 + finalp0
      , p0 + final2
      , replace(map1, 1^run, n.p0)
      , toseq(asset.toprocess \ asset.run)
     )
    else
     let endpart = makePart(map1, n.p0, [3^part, 1^part], place)
     for finalb = endpart + finalp0, b = p0 + endpart, e ∈ {brtrues} acc << 2
     do
      let idx = n.b - n.p0
      let newpart =
       if idx = n.acc - 2 then runstart >> 3 + [idx#vals, JumpOp, Br2(n.b - e + 1, 1)]
       else [idx#vals, Br2(n.b - e + 1, 1)],
      next(newpart + finalb, b + newpart),
     next(finalb, b, replace(map1, 1^run, n.b), toseq(asset.toprocess \ asset.run))
   else if place#map1 ≠ 0 then next(finalp0, p0, map1, toprocess >> 1)
   else
    let newpart = part >> 1 + Br2(n.p0 - 2#acc + 1, n.p0 - 1#acc + 1)
    let f = lookup(p0, newpart, "B"),
    if f > 0 then next(finalp0, p0, replace(map1, place, f), toprocess >> 1)
    else
     let newmap = replace(map1, place, n.p0 + 1),
     next(newpart + finalp0, p0 + newpart, newmap, toprocess >> 1),
  result + final + EndBlock

function lookup(a:set.fromEnd, part:seq.symbol, xx:seq.word) int
let part2 = flop(n.a + 1, part)
let c = {if n.a < 5 then findelement2 (a, b) else} a
for f = 0, e ∈ toseq.c while f = 0 do if code2.e = part2 then fromEnd.e else f,
f

function %(a:boolean) seq.word if a then "T" else "F"

function %(a:fromEnd) seq.word "/br^(fromEnd.a):: ^(code2.a)"

type fromEnd is fromEnd:int, code2:seq.symbol

function tofromEnd(fromEnd:int, code:seq.symbol) fromEnd
fromEnd(fromEnd, flop(fromEnd, code))

function flop(fromEnd:int, code:seq.symbol) seq.symbol
{flop Br offset from start and beginning of block to starting at end}
let last = 1^code,
if isbr.last then code >> 1 + Br2(fromEnd - brt.last, fromEnd - brf.last) else code

use otherseq.symbol

function >1(a:fromEnd, b:fromEnd) ordering code2.a >1 code2.b ∧ fromEnd.a >1 fromEnd.b

function >2(a:fromEnd, b:fromEnd) ordering code2.a >1 code2.b

use otherseq.fromEnd

use set.fromEnd

function +(a:set.fromEnd, p:seq.symbol) set.fromEnd a + tofromEnd(n.a + 1, p)

function makePart(map:seq.int, len:int, part:seq.symbol, place:int) seq.symbol
if not.isbr.1^part then part
else
 part >> 1
  + Br2(len - (place + brt.1^part)#map + 1, len - (place + brf.1^part)#map + 1)

function check5(map:seq.int, e0:int, parts:seq.seq.symbol) seq.int
for acc = empty:seq.int, toprocess = [e0]
while not.isempty.toprocess
do
 let e1 = 1#toprocess,
 if e1#map ≠ 0 then next(acc, toprocess << 1)
 else
  let last = 1^(e1#parts),
  if not.isbr.last then next([e1] + acc, toprocess << 1)
  else next([e1] + acc, toprocess << 1 + [e1 + brt.last, e1 + brf.last]),
acc

function chain(i:int, parts:seq.seq.symbol) int
let part = i#parts,
if n.part = 2 ∧ 1#part = Littrue ∧ isbr.1^part then chain(i + brt.1^part, parts)
else if n.part = 2 ∧ 1#part = Litfalse ∧ isbr.1^part then chain(i + brf.1^part, parts)
else i

function p55(s:seq.symbol) seq.word
for acc = "", e ∈ s do acc + if isword.e then "WORD" else %.e,
acc 