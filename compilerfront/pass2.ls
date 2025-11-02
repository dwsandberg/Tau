Module pass2

use backparse

use bits

use set.fromEnd

use arc.int

use graph.arc.int

use set.arc.int

use seq1.int

use seq.int

use set.int

use stack.int

use localmap2

use set.localmap2

use mytype

use seq.mytype

use real

use standard

use seq1.symbol

use seq1.seq.symbol

use set.symbol

use seq.symbol

use symbol1

use set.symdef

use encoding.track

use seq1.track

use sort.track

use seq1.track2

Export type:expandresult

Export code(expandresult) seq.symbol

Export nextvar(expandresult) int

Export expandresult(int, seq.symbol) expandresult

Export type:optargs

Export libname(optargs) word

Export librarymap(optargs) seq.word

Export mapX(optargs) set.localmap2

Export nextvarX(optargs) int

Export options(optargs) seq.word

Export prg(optargs) set.symdef

Export self(optargs) symbol

Export ss(optargs) seq.symbol

Export typedict(optargs) typedict

Export optargs(
librarymap:seq.word
, prg:set.symdef
, ss:seq.symbol
, self:symbol
, nextvarX:int
, mapX:set.localmap2
, libname:word
, typedict:typedict
, options:seq.word
) optargs

Export type:stkele

Export blkparts(stkele) seq.seq.symbol

Export part(stkele) seq.symbol

Export stkele(part:seq.symbol, blkparts:seq.seq.symbol) stkele

type optargs is
librarymap:seq.word
, prg:set.symdef
, ss:seq.symbol
, self:symbol
, nextvarX:int
, mapX:set.localmap2
, libname:word
, typedict:typedict
, options:seq.word

Function calcOptions(self:symbol, optionsIn:symdefOption, code:seq.symbol) symdefOption
if isempty.code ∨ NOINLINE ∈ optionsIn then optionsIn \ VERYSIMPLE
else
 {length of code for" sub" is 36}
 let nopara = nopara.self
 let N = 1
 let C = 2,
 for
  acc = nonReducible
   + (if n.code ≤ 36 then INLINE else NOOPTIONS)
   + (if n.code ≥ nopara then VERYSIMPLE else NOOPTIONS)
  , stk = empty:stack.int
  , idx = 1
  , sym ∈ code
 while acc ≠ NOOPTIONS
 do
  let kind = kind.sym,
  if kind = klocal then
   if value.sym ≤ nopara then
    let newacc = if idx ≤ nopara ∧ value.sym = idx then acc else acc \ VERYSIMPLE,
    next(newacc, push(stk, N), idx + 1)
   else next(acc \ (VERYSIMPLE + nonReducible), stk, idx + 1)
  else if kind = kstacktrace then next(if idx > nopara then acc else acc \ VERYSIMPLE, push(stk, N), idx + 1)
  else if kind ∈ [kint, kreal, kword, kwords, ktrue, kfalse, kfref] then next(if idx > nopara then acc else acc \ VERYSIMPLE, push(stk, C), idx + 1)
  else if kind ∈ [kstart, kloop, kbr, kendblock, kcontinue, kexit, kjmpB, kjmp, klabel, kdefine] then next(acc \ (VERYSIMPLE + nonReducible), stk, idx + 1)
  else if kind ∈ [kother, kcompoundname, kmember, kidx] then next(if self = sym then NOOPTIONS else acc \ nonReducible, stk, idx + 1)
  else if kind
  ∉ [kinternalmod, kprefref, ksetI, ksetP, kglobal, kconstantrecord, kidxNB, kcreatethreadZ]
  ∧ N ∈ top(stk, nopara.sym)
  ∧ nonReducible ∈ acc then next(acc, push(pop(stk, nopara.sym), N), idx + 1)
  else
   let newacc = acc \ (if idx > nopara then nonReducible else VERYSIMPLE + nonReducible),
   next(newacc, stk, idx + 1),
 optionsIn \ (VERYSIMPLE + nonReducible)
  + if VERYSIMPLE ∈ acc then acc + INLINE else acc

Function pdict(nopara:int) set.localmap2
{let d1 = localmap2 (1, [Local.1]) let d2 = localmap2 (2, [Local.2]) let d3 = localmap2 (3, [Local.3]) if nopara = 0 then empty:set.localmap2 else if nopara = 1 then asset.[d1] else if nopara = 2 then asset.[d1, d2] else for pdict = asset.[d1, d2, d3], parano ∈ arithseq (nopara-3, 1, 4)}
for pdict = empty:set.localmap2, parano ∈ arithseq(nopara, 1, 1)
do pdict + localmap2(parano, [Local.parano]),
pdict

type expandresult is nextvar:int, code:seq.symbol

function isemptysymbol(sym:symbol) boolean
let kind = kind.sym,
if kind = kwords then isempty.worddata.sym
else if kind = kconstantrecord then
 let full = fullconstantcode.sym,
 kind.full sub 1 = ksequence ∧ nopara.full sub 1 = 0
else false

Function fromTheEnd(i:int, s:seq.symbol) symbol
{Number elements in sequence from n.s to 1 and return the element numbered i}
s sub (n.s - (i - 1))

Function checkemptycat(sym:symbol, part:seq.symbol) seq.symbol
if isemptysymbol.part sub n.part then part >> 1
else if kind.fromTheEnd(2, part) = kwords ∧ kind.part sub n.part = kwords then part >> 2 + Words(worddata.fromTheEnd(2, part) + worddata.part sub n.part)
else if kind.fromTheEnd(2, part) = kconstantrecord ∧ kind.part sub n.part = kconstantrecord then
 let a = fullconstantcode.fromTheEnd(2, part)
 let b = fullconstantcode.part sub n.part,
 if kind.a sub n.a = ksequence ∧ kind.b sub n.b = ksequence then
  part >> 2
   + a >> 1
   + b >> 1
   + Sequence(parameter.resulttype.b sub n.b, nopara.a sub n.a + nopara.b sub n.b)
 else empty:seq.symbol
else
 let para2 = backparse3(part, n.part, true),
 if isemptysymbol.part sub (para2 - 1) then subseq(part, 1, para2 - 2) + subseq(part, para2, n.part)
 else empty:seq.symbol

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
 let kind = kind.a,
 if kind = klocal then acc + Local(value.a + delta)
 else if kind = kdefine then acc + Define(value.a + delta)
 else if kind = kloop then acc + Loopblock(paratypes.a, firstvar.a + delta, resulttype.a)
 else acc + a,
acc

Function checkLoopIsNoOp(syms:seq.symbol, parts:seq.seq.symbol, self:symbol) seq.symbol
let prior = syms >> 1
let loop = syms sub n.syms,
if n.parts = 3
∧ n.parts sub 3 ∈ [13, 14]
∧ parts sub 2 = [Lit.0, Exit]
∧ nopara.loop = 2
∧ prior << (n.prior - 1) = [Lit.0]
∧ isseq.(paratypes.loop) sub 1 then
 let lastpart = parts sub 3
 let theseqtype = resulttype.fromTheEnd(3, lastpart),
 let theseq = lastpart sub 5,
 if %.parameter.theseqtype ∈ ["packed2", "ptr"] then {???? hack! should at least check to see if cat is defined.} empty:seq.symbol
 else
  let firstvar = firstvar.loop
  let idx = firstvar + 1
  let seqlen =
   if kind.theseq = kconstantrecord then
    let full = fullconstantcode.theseq,
    Lit.nopara.full sub n.full
   else if kind.theseq = kwords then Lit.n.worddata.theseq
   else Local(firstvar - 1),
  let symidx = lastpart sub 7,
  if nopara.symidx ≠ 2 then empty:seq.symbol
  else
   let idxNB = symIdxNB.parameter.(paratypes.symidx) sub 1
   let cat =
    if n.lastpart = 14 then
     [
      Sequence(if resulttype.symidx = typeword then typeint else resulttype.symidx, 1)
      , symbol(moduleref("* seq", parameter.theseqtype), "+", [theseqtype, theseqtype], theseqtype)
     ]
    else
     [
      symbol(
       moduleref("* seq", parameter.theseqtype)
       , "+"
       , [theseqtype, parameter.theseqtype]
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
   if [Local.idx, seqlen, EqOp] = parts sub 1 >> 1 ∧ lastpart = matchbrf then
    let newsyms =
     if prior << (n.prior - 3) = [GetSeqLength, Define(firstvar.loop - 1), Lit.0] then syms >> 4
     else if isconst.kind.theseq ∧ prior sub n.prior = Lit.0 then syms >> 2 + theseq
     else empty:seq.symbol,
    if isempty.newsyms then empty:seq.symbol
    else
     newsyms
      + symbol(moduleref("* seq", parameter.theseqtype), "+", [theseqtype, theseqtype], theseqtype)
      + Define.firstvar
      + Lit.0
   else empty:seq.symbol
else empty:seq.symbol

type stkele is part:seq.symbol, blkparts:seq.seq.symbol

/Function % (a:stkele) seq.word"
/p part::(part.a):(%n.blkparts.a)"

Function checkrecursive(
parts:seq.seq.symbol
, self:symbol
, stkpart:seq.symbol
, nojumptable:boolean
, nextvar:int
) seq.symbol
let nopara = nopara.self
for changed = false, acc = empty:seq.seq.symbol, p ∈ parts
do
 if kind.p sub n.p = kexit ∧ p sub (n.p - 1) = self then
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
  + code.blocktocode(empty:seq.symbol, acc, self, nojumptable, nextvar)
else empty:seq.symbol

function ⊻(a:boolean, b:boolean) boolean if a then not.b else b

Function adjustbr(parts:seq.seq.symbol, amount:int) seq.seq.symbol
{adjust branches that jump after what has been processed in outer block}
for tmp = parts, place = 1, e ∈ parts
do
 let x = e sub n.e
 let kind = kind.x,
 if kind = kbr then
  let adjustt = if brt.x + place > n.tmp + 1 then amount - 1 else 0
  let adjustf = if brf.x + place > n.tmp + 1 then amount - 1 else 0,
  if adjustt + adjustf ≠ 0 then next(replace(tmp, place, e >> 1 + Br2(brt.x + adjustt, brf.x + adjustf)), place + 1)
  else next(tmp, place + 1)
 else if kind = kjmp then
  for acc = e >> (value.x - 2), e2 ∈ subseq(e, n.e - value.x + 3, n.e - 1)
  do
   acc
    + if kind.e2 = klabel then if value.e2 + place > n.tmp + 1 then Label(value.e2 + amount - 1) else e2
   else e2,
  next(replace(tmp, place, acc + e sub n.e), place + 1)
 else next(tmp, place + 1),
tmp

function %(a:arc.int) seq.word "(:(tail.a):(head.a))"

function jmplabels(place:int, p:seq.symbol) seq.int
let last = p sub n.p
for acc = empty:seq.int, e ∈ subseq(p, n.p - value.last + 2, n.p)
do if kind.e = klabel then acc + (place + value.e) else acc,
acc

function findsubexp(part:seq.symbol, subexp:seq.symbol) int
let last = subexp sub n.subexp
for idx = 1, nest = 0, e ∈ part
while idx > 0
do
 if nest = 0 ∧ not.isspecial.kind.e ∧ e = last ∧ subseq(part, idx - n.subexp + 1, idx) = subexp then next(-idx, nest)
 else
  let kind = kind.e,
  next(
   idx + 1
   , if kind ∈ [kstart, kloop] then nest + 1 else if kind = kendblock then nest - 1 else nest
  ),
abs.idx

function findCandidate(part:seq.symbol) int
for idx = 1, count = 0, nest = 0, e ∈ part
while idx > 0
do
 let kind = kind.e,
 if nest = 0 ∧ (isconst.kind ∨ kind = klocal) then next(idx + 1, count + 1, nest)
 else if kind ∈ [kstart, kloop] then next(idx + 1, 0, nest + 1)
 else if kind = kendblock then next(idx + 1, 0, nest - 1)
 else if nest = 0 ∧ count ≥ 2 ∧ name.module.e ∈ "seq" ∧ name.e ∈ "sub" then next(-idx, 0, nest)
 else next(idx + 1, 0, nest),
abs.idx

Function blocktocode(
result:seq.symbol
, parts0:seq.seq.symbol
, self:symbol
, nojumptable:boolean
, nextvar0:int
) expandresult
{???? remove hoist restriction}
let hoist = name.self ∈ "optest37 optest35"
{name.self ∉" union diff getcode newstack reallit"}
{∨ %.self ∈ [" xset.word:diff (seq.word, seq.word, int, int) seq.word"," xset.mytype:diff (seq.mytype, seq.mytype, int, int) seq.mytype"," xset.symbol:diff (seq.symbol, seq.symbol, int, int) seq.symbol"," xset.int:diff (seq.int, seq.int, int, int) seq.int"," xset.filename:diff (seq.filename, seq.filename, int, int) seq.filename"," xset.encoding.word3:diff (seq.encoding.word3, seq.encoding.word3, int, int) seq.encoding.word3"," xset.state:diff (seq.state, seq.state, int, int) seq.state"," xset.arc.int:diff (seq.arc.int, seq.arc.int, int, int) seq.arc.int"]}
let first = parts0 sub 1,
if kind.first sub n.first = kexit then expandresult(nextvar0, result >> 1 + first >> 1)
else
 let kind2 = kind.fromTheEnd(2, first)
 let z =
  if kind2 = ktrue then brt.first sub n.first
  else if kind2 = kfalse then brf.first sub n.first
  else 0,
 if z > 0 then
  assert z + 1 ≤ n.parts0 report ":(self):(z) blocktocode:(%n.parts0)"
  let newparts = [parts0 sub 1 >> 2 + parts0 sub (z + 1)] + parts0 << (z + 1),
  blocktocode(result, newparts, self, nojumptable, nextvar0)
 else
  {first part will be Br2 or Jmp}
  for
   parts = empty:seq.seq.symbol
   , reached = asset.[1]
   , arcs5 = empty:set.arc.int
   , brs = empty:seq.int
   , nextvar = nextvar0
   , this0 ∈ parts0
  do
   let place = n.parts + 1,
   if place ∉ reached then next(parts + [Lit.0], reached, arcs5, brs, nextvar)
   else
    let last = this0 sub n.this0
    let kind = kind.last,
    if kind = kjmp then
     let list = subseq(this0, n.this0 - value.last + 2, n.this0)
     for bx = reached, diff = empty:seq.symbol, e ∈ list
     do
      if kind.e = klabel then
       let org = place + value.e
       let t = chain(org, parts0),
       if t = org then if isempty.diff then next(bx + t, diff) else next(bx + t, diff + e)
       else next(bx + t, diff + Label(t - place))
      else if isempty.diff then next(bx, diff)
      else next(bx, diff + e),
     let this1 = if isempty.diff then this0 else this0 >> n.diff + diff,
     next(parts + this1, bx, arcs5, brs + place, nextvar)
    else if kind ≠ kbr then next(parts + this0, reached, arcs5, brs, nextvar)
    else
     let brt = chain(place + brt.this0 sub n.this0, parts0) - place
     let brf = chain(place + brf.this0 sub n.this0, parts0) - place
     let this =
      if this0 sub (n.this0 - 1) = NotOp then this0 >> 2 + Br2(brf, brt)
      else this0 >> 1 + Br2(brt, brf)
     let exp =
      if place > 1 ∧ hoist then
       let t2 = findCandidate.this,
       if t2 > n.this then 0 else t2
      else 0
     let subexp = subseq(this, exp - 2, exp)
     for placeX = if exp = 0 then 1 else place, idx = 0
     while idx = 0 ∧ placeX > 1
     do
      let r = findelement2(arcs5, arc(placeX, 0)),
      if n.r ≠ 1 then next(1, 0)
      else
       let parent = parts sub head.r sub 1
       let k = findsubexp(parent, subexp),
       if k > n.parent then next(head.r sub 1, 0) else next(head.r sub 1, k)
     let newreached = reached + (brt + place) + (brf + place)
     let newarcs5 =
      if brt = brf then arcs5 + arc(brt + place, place)
      else arcs5 + arc(brt + place, place) + arc(brf + place, place),
     let newbrs = if n.this = 2 ∧ this sub 1 ∈ [Littrue, Litfalse] then brs else brs + place,
     if idx = 0 then {no subexpression was found} next(parts + this, newreached, newarcs5, newbrs, nextvar)
     else
      let parent = parts sub placeX
      {check printrecord slotorder2 are form printbitcodes descslot}
      if kind.parent sub (idx + 1) ≠ kdefine then
       {subexpression was found but not placed in variable}
       let newparent = subseq(parent, 1, idx) + Define.nextvar + Local.nextvar + parent << idx
       let newpart =
        replace(parts, placeX, newparent)
         + (subseq(this, 1, exp - 4)
         + Local.value.newparent sub (idx + 1)
         + subseq(this, exp + 1, n.this)),
       next(newpart, newreached, newarcs5, newbrs, nextvar + 1)
      else
       {subexpression was found that is in variable}
       let newpart =
        subseq(this, 1, exp - 4)
         + Local.value.parent sub (idx + 1)
         + subseq(this, exp + 1, n.this),
       next(parts + newpart, newreached, newarcs5, newbrs, nextvar)
  {map contains location from end of block. Branch chains have been removed from block. Block is reconstruct from end to beginning. }
  for
   final = empty:seq.symbol
   , placements = empty:set.fromEnd
   , map = arithseq(n.parts, 0, 0)
   , toprocess = brs
  while not.isempty.toprocess
  do
   let place = toprocess sub n.toprocess,
   if map sub place ≠ 0 then next(final, placements, map, toprocess >> 1)
   else
    let part = parts sub place
    let quit = empty:seq.symbol
    let kind = kind.part sub n.part
    let tmp1 = if kind = kbr then 4 else value.part sub n.part + 1
    let runreg =
     if n.part < tmp1 then
      assert kind ≠ kjmp report "not expecting jmp:(part)",
      Local.0
     else
      let tmp2 = part sub (n.part - tmp1 + 1),
      if kind.tmp2 = klocal then tmp2
      else
       assert kind ≠ kjmp report "not expecting jmp:(part)",
       Local.0
    for run = [place], brtrues = empty:seq.int, vals = empty:seq.symbol, cpart = part
    while {more} not.isempty.cpart
    do
     let isbr = kind.cpart sub n.cpart = kbr,
     if {not partofrun} isbr
     ∧ (n.cpart < 4
     ∨ cpart sub (n.cpart - 3) ≠ runreg
     ∨ cpart sub (n.cpart - 1) ≠ EqOp
     ∨ kind.cpart sub (n.cpart - 2) ∉ [kint, kword]) then next(run >> 1, brtrues, vals, quit)
     else
      for
       newvals = if isbr then vals + cpart sub (n.cpart - 2) else vals
       , newbrtrues = if isbr then brtrues + [run sub n.run + brt.cpart sub n.cpart] else brtrues
       , e ∈ reverse(
        if isbr then empty:seq.symbol
        else subseq(cpart, n.cpart - value.cpart sub n.cpart + 2, n.cpart - 2)
       )
      do
       if kind.e ≠ klabel then next(newvals + e, newbrtrues)
       else next(newvals, newbrtrues + (run sub n.run + value.e)),
      if isbr ∧ n.cpart ≠ 4 then next(run, newbrtrues, newvals, quit)
      else
       let r = findelement2(arcs5, arc(run sub n.run, 0)),
       if n.r ≠ 1 then
        {this part is reachable from more than one point so end run}
        next(run, newbrtrues, newvals, quit)
       else
        let idx = head.r sub 1
        let tmp = parts sub idx,
        assert kind.tmp sub n.tmp = kbr report "unexpected:(tmp)",
        if brf.tmp sub n.tmp + idx = run sub n.run then next(run + idx, newbrtrues, newvals, tmp)
        else next(run, newbrtrues, newvals, quit)
    let haverun = n.vals ≥ 3 ∧ not.nojumptable
    assert not.haverun ∨ n.asset.vals = n.vals report "Error: Function:(self) has duplicate value in branch table::(vals)"
    let default =
     place
      + if kind.part sub n.part = kbr then brf.part sub n.part else value.fromTheEnd(2, part),
    for
     map1 = map
     , acc = empty:seq.int
     , finalp0 = final
     , p0 = placements
     , e ∈ [default] + (if haverun then brtrues else [place + brt.part sub n.part])
    do
     let c5 = check5(map1, e, parts)
     for map2 = map1, finalp1 = finalp0, p1 = p0, e1 ∈ c5
     do
      if map2 sub e1 ≠ 0 then next(map2, finalp1, p1)
      else
       let newpart = makePart(map2, n.p1, parts sub e1, e1)
       let j = lookup(p1, newpart),
       if j = 0 then next(replace(map2, e1, n.p1 + 1), newpart + finalp1, p1 + newpart)
       else next(replace(map2, e1, j), finalp1, p1),
     next(map2, acc + map2 sub e, finalp1, p1),
    if haverun then
     let lastofrun = run sub n.run
     let tmp = parts sub lastofrun
     let runprefix = if kind.tmp sub n.tmp = kbr then tmp >> 3 else tmp >> value.tmp sub n.tmp
     for ss2 = empty:seq.symbol, e ∈ acc
     do
      let label = Label(n.p0 - e + 1),
      (if isempty.ss2 then [label] else [vals sub (n.ss2 / 2 + 1), label]) + ss2
     let final2 = runprefix + Jmp.ss2,
     let f = lookup(p0, final2),
     if f > 0 then next(finalp0, p0, replace(map1, run sub n.run, f), toseq(asset.toprocess \ asset.run))
     else
      next(
       final2 + finalp0
       , p0 + final2
       , replace(map1, run sub n.run, n.p0 + 1)
       , toseq(asset.toprocess \ asset.run)
      )
    else
     let newpart = part >> 1 + Br2(n.p0 - acc sub 2 + 1, n.p0 - acc sub 1 + 1)
     let f = lookup(p0, newpart),
     if f > 0 then next(finalp0, p0, replace(map1, place, f), toprocess >> 1)
     else
      let newmap = replace(map1, place, n.p0 + 1),
      next(newpart + finalp0, p0 + newpart, newmap, toprocess >> 1),
  expandresult(nextvar, result + final + EndBlock)

function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

function lookup(a:set.fromEnd, part:seq.symbol) int
let part2 = flop(n.a + 1, part)
for f = 0, e ∈ toseq.a while f = 0 do if code2.e = part2 then fromEnd.e else f,
f

function %(a:fromEnd) seq.word "/br:(fromEnd.a):: :(code2.a)"

type fromEnd is fromEnd:int, code2:seq.symbol

function tofromEnd(fromEnd:int, code:seq.symbol) fromEnd
fromEnd(fromEnd, flop(fromEnd, code))

function flop(fromEnd:int, code:seq.symbol) seq.symbol
{flop Br offset from start and beginning of block to starting at end}
let last = code sub n.code
let kind = kind.last,
if kind = kbr then code >> 1 + Br2(fromEnd - brt.last, fromEnd - brf.last)
else if kind = kjmp then
 for acc = empty:seq.symbol, e ∈ subseq(code, n.code - value.last + 2, n.code - 1)
 do acc + (if kind.e = klabel then Label(fromEnd - value.e) else e)
 let newEnd = acc + last,
 code >> n.newEnd + newEnd
else code

function >1(a:fromEnd, b:fromEnd) ordering code2.a >1 code2.b ∧ fromEnd.a >1 fromEnd.b

function >2(a:fromEnd, b:fromEnd) ordering code2.a >1 code2.b

function +(a:set.fromEnd, p:seq.symbol) set.fromEnd a + tofromEnd(n.a + 1, p)

function makePart(map:seq.int, len:int, part:seq.symbol, place:int) seq.symbol
if kind.part sub n.part ≠ kbr then part
else
 part >> 1
  + Br2(
  len - map sub (place + brt.part sub n.part) + 1
  , len - map sub (place + brf.part sub n.part) + 1
 )

function check5(map:seq.int, e0:int, parts:seq.seq.symbol) seq.int
for acc = empty:seq.int, toprocess = [e0]
while not.isempty.toprocess
do
 let e1 = toprocess sub 1,
 if map sub e1 ≠ 0 then next(acc, toprocess << 1)
 else
  let last = last.parts sub e1
  let kind = kind.last,
  if kind = kbr then next([e1] + acc, toprocess << 1 + [e1 + brt.last, e1 + brf.last])
  else if kind = kjmp then next([e1] + acc, toprocess << 1 + jmplabels(e1, parts sub e1))
  else next([e1] + acc, toprocess << 1),
acc

function chain(i:int, parts:seq.seq.symbol) int
{remove recursion}
let part = parts sub i
let last = part sub n.part,
if n.part ≠ 2 ∨ kind.last ≠ kbr then i
else
 let kind = kind.part sub 1,
 if kind = ktrue then chain(i + brt.last, parts)
 else if kind = kfalse then chain(i + brf.last, parts)
 else i

Function membercode(p1:mytype, part:seq.symbol, prg:set.symdef, nextvar:int) expandresult
let last = part sub n.part
let part1 =
 if kind.last = kwords then
  for acc = part >> 1, w ∈ worddata.last do acc + Word.w,
  acc + Sequence(typeword, n.worddata.last)
 else if kind.last = kconstantrecord then part >> 1 + fullconstantcode.last
 else part
assert kind.part1 sub n.part1 = ksequence report "membercode expected sequence ksequence:(part1 sub n.part1)",
if value.part1 sub n.part1 = 0 then expandresult(nextvar + 2, part1 + Define.nextvar + Define(nextvar + 1) + Litfalse)
else
 let EqOp2 =
  if p1 ∈ [typeword] then [EqOp]
  else
   let f1 =
    {findelement2}
    lookup(prg, symdef(symbol(internalmod, "=", [p1, p1], typeboolean), empty:seq.symbol, 0))
   for EqOp1 = empty:seq.symbol, e ∈ toseq.f1
   do if isunbound.sym.e then EqOp1 else EqOp1 + sym.e,
   EqOp1,
 if n.EqOp2 ≠ 1 then expandresult(0, empty:seq.symbol)
 else
  for caselist = empty:seq.seq.symbol, idx = n.part1 - 1, parano = nopara.part1 sub n.part1
  while parano > 0
  do
   let tmp = backparse3(part1, idx, true)
   let paraval = subseq(part1, tmp, idx),
   next([paraval] + caselist, tmp - 1, parano - 1)
  let kind = kind.part1 sub idx
  let newnextvar = if kind = klocal ∨ isconst.kind then nextvar else nextvar + 1
  let part12 =
   if newnextvar = nextvar then subseq(part1, 1, idx - 1)
   else subseq(part1, 1, idx) + Define.nextvar
  let reg = if newnextvar = nextvar then part1 sub idx else Local.nextvar,
  for outcode = part12 + Start.typeboolean, caseno = n.caselist + 1, e ∈ caselist
  do next(outcode + reg + e + EqOp2 + Br2(caseno, 1), caseno - 1),
  expandresult(newnextvar, outcode + Litfalse + Exit + Littrue + Exit + EndBlock)

Function builtinCompileTime(part:seq.symbol, ctsym:symbol, libname:word) seq.symbol
let kind = kind.ctsym
let tmp6 =
 if kind = kmulint then [Lit(value.fromTheEnd(2, part) * value.part sub n.part)]
 else if kind = kaddint then [Lit(value.fromTheEnd(2, part) + value.part sub n.part)]
 else if kind = ksubint then [Lit(value.fromTheEnd(2, part) - value.part sub n.part)]
 else if kind = kdivint ∧ part sub n.part ≠ Lit.0 then [Lit(value.fromTheEnd(2, part) / value.part sub n.part)]
 else if kind ∈ [kidx, kidxNB] then
  let args = subseq(part, n.part - 1, n.part),
  if kind.args sub 1 = kwords then [Word.(worddata.args sub 1) sub value.args sub 2]
  else
   let t = fullconstantcode.args sub 1,
   if kind.t sub n.t ≠ ksequence then empty:seq.symbol
   else
    let idx = value.args sub 2,
    if nopara.t sub n.t = n.t - 1 ∧ between(idx, 1, n.t - 1) then [t sub idx]
    else empty:seq.symbol
 else if kind = kgetseqlength then
  if kind.part sub n.part = kwords then [Lit.n.worddata.part sub n.part]
  else
   let x = last.fullconstantcode.part sub n.part,
   if kind.x = ksequence then [Lit.nopara.x] else empty:seq.symbol
 else if kind = kgetseqtype then
  if kind.part sub n.part = kwords then [Lit.0]
  else
   let x = last.fullconstantcode.part sub n.part,
   if kind.x = ksequence then [Lit.0] else empty:seq.symbol
 else if kind = keqlB then [if kind.fromTheEnd(2, part) = kind.part sub n.part then Littrue else Litfalse]
 else if kind = keqlI then
  let tmp =
   if kind.fromTheEnd(2, part) = kword then worddata.fromTheEnd(2, part) = worddata.part sub n.part
   else value.fromTheEnd(2, part) = value.part sub n.part,
  [if tmp then Littrue else Litfalse]
 else if kind = kgrtI then [if value.fromTheEnd(2, part) > value.part sub n.part then Littrue else Litfalse]
 else if kind = k<<bits then [Lit.toint(tobits.value.fromTheEnd(2, part) << value.part sub n.part)]
 else if kind = k>>bits then [Lit.toint(tobits.value.fromTheEnd(2, part) >> value.part sub n.part)]
 else if kind = k∨bits then [Lit.toint(tobits.value.fromTheEnd(2, part) ∨ tobits.value.part sub n.part)]
 else if kind = k∧bits then [Lit.toint(tobits.value.fromTheEnd(2, part) ∧ tobits.value.part sub n.part)]
 else if kind = kxorbits then [Lit.toint(tobits.value.fromTheEnd(2, part) ⊻ tobits.value.part sub n.part)]
 else if kind = kaddreal then [Reallit.representation(casttoreal.value.fromTheEnd(2, part) + casttoreal.value.part sub n.part)]
 else if kind = ksubreal then [Reallit.representation(casttoreal.value.fromTheEnd(2, part) - casttoreal.value.part sub n.part)]
 else if kind = kmakereal ∧ kind.part sub n.part = kwords then [Reallit.representation.makereal.worddata.part sub n.part]
 else if kind = kfld then
  let t = fullconstantcode.fromTheEnd(2, part)
  let val = value.part sub n.part,
  if kind.t sub n.t = krecord ∧ between(val, 0, nopara.t sub n.t - 1) ∧ nopara.t sub n.t = n.t - 1 then [t sub (val + 1)]
  else empty:seq.symbol
 else if kind = kcat then
  if kind.fromTheEnd(2, part) = kwords ∧ kind.part sub n.part = kwords then [Words(worddata.fromTheEnd(2, part) + worddata.part sub n.part)]
  else if kind.fromTheEnd(2, part) = kconstantrecord ∧ kind.part sub n.part = kconstantrecord then
   let a = fullconstantcode.fromTheEnd(2, part)
   let b = fullconstantcode.part sub n.part,
   if kind.a sub n.a = ksequence ∧ kind.b sub n.b = ksequence then
    a >> 1
     + b >> 1
     + Sequence(parameter.resulttype.b sub n.b, nopara.a sub n.a + nopara.b sub n.b)
   else empty:seq.symbol
  else empty:seq.symbol
 else empty:seq.symbol,
if isempty.tmp6 then empty:seq.symbol
else
 let newconst = if n.tmp6 > 1 then Constant2(libname, tmp6) else tmp6 sub 1,
 part >> nopara.ctsym + newconst

Function makeconst(libname:word, incode:seq.symbol) symbol
{assumes incode contains constants, Records, and Sequences}
if n.incode = 1 then incode sub 1
else if n.incode = nopara.incode sub n.incode + 1 then Constant2(libname, incode)
else
 for part = empty:seq.symbol, sym ∈ incode
 do
  if kind.sym ∈ [krecord, ksequence] then
   let nopara = nopara.sym
   let len = n.part,
   let args = subseq(part, len + 1 - nopara, len),
   part >> nopara + Constant2(libname, args + sym)
  else part + sym
 assert n.part = 1 report "makeconst problem",
 part sub 1

function noopsymbolss(self:symbol) boolean
%.self
∈ [
 "llvm:% (llvmtype) seq.word"
 , "llvm:function (seq.llvmtype) llvmtype"
 , "UTF8:tocharseq2 (seq.int) seq.char"
 , "UTF8:tointseq (seq.char) seq.int"
 , "UTF8:tocharseq (seq.int) seq.char"
 , "persistant:hash (const3) int"
 , "llvm:typerecords seq.seq.int"
 , "llvm:AGGREGATE (seq.slot) slot"
 , "compileTimeT.callconfig:buildargs:callconfig (seq.symbol) seq.int"
 , "compileTimeT.callconfig:tocode:callconfig (int, mytype, typedict) seq.symbol"
 , "set.mytype:findelement2 (set.mytype, mytype) set.mytype"
 , "set.symbol:findelement2 (set.symbol, symbol) set.symbol"
 , "set.arc.symbol:findelement2 (set.arc.symbol, arc.symbol) set.arc.symbol"
 , "object01:inrec (seq.seq.int) ptr"
 , "typedict:asseqseqmytype (typedict) seq.seq.mytype"
 , "set.int:findelement2 (set.int, int) set.int"
 , "test11a:checkprec seq.word"
 , "set.myExport:findelement2 (set.myExport, myExport) set.myExport"
 , "set.sym/modref:findelement2 (set.sym/modref, sym/modref) set.sym/modref"
 , "prettycompilerfront:transform2 (midpoint, seq.word, seq.word, seq.word, boolean, boolean, seq.word, boolean, boolean, seq.file, seq.file, seq.word) seq.file"
 , "opttests:optest16 (seq.char) seq.int"
 , "genEnumeration:enumerate (seq.word, seq.word, boolean, seq.word) seq.seq.word"
] 
