Module opt

use bits

use llvmcode

use compilerfrontT.callconfig

use encoding.exp

use otherseq.encoding.exp

use otherseq.Exp

use stack.Exp

use otherseq.exp

use seq.exp

use stack.exp

use file

use otherseq.int

use set.int

use otherseq.loc

use set.loc

use standard

use symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use symbol2

use otherseq.symdef

use seq.symdef

use set.symdef

use set.word

Function test(input:seq.file, o:seq.word) seq.file
{ENTRYPOINT}
let m = compilerFront:callconfig("pass2", input)
let mm = hasstate.prg.m
let output =
 for acc = "", sd ∈ toseq.mm
 do
  if name.sym.sd ∈ "setinsert" then
  let a = 1_GG.asset.[sd], acc + "^(sym.sd)^(code.sd) /p^(code.a)"
  else acc,
 acc,
[file(o, output)]

[file (o, %.cardinality.newprg+profileresults." time")]

+{%.toseq.mm} %n.encodingdata:exp [file (o, output)]

Function hasstate(prg:set.symdef) set.symdef
let inithasstate = asset.[
 symbol(internalmod, "addencoding", [typeint, typeptr, typeint, typeint], typeint)
 , symbol(internalmod, "getinstance", typeint, typeptr)
 , symbol(moduleref("* builtin", typereal), "assert", seqof.typeword, typereal)
 , symbol(moduleref("* builtin", typeptr), "assert", seqof.typeword, typeptr)
 , symbol(moduleref("* builtin", typeint), "assert", seqof.typeword, typeptr)
]
let hasstate = hasstate(inithasstate, toseq.prg)
for acc = empty:set.symdef, sd ∈ toseq.prg
do
 {if isabstract.module.sym.sd then acc else}
 let options = getOptions.sd
 assert isempty(asset.options \ asset."COMPILETIME NOINLINE PROFILE INLINE STATE VERYSIMPLE ThisLibrary")
 report "SDFSDF^(options)"
 let newOptions =
  options
  + 
   if sym.sd ∈ hasstate then
   "STATE"
   else "
    ^(
     if not.isempty.code.sd ∧ 1_"NOINLINE" ∉ options ∧ isverysimple(nopara.sym.sd, code.sd) then
     "VERYSIMPLE"
     else "")",
  if options = newOptions then
  acc + sd
  else acc + symdef4(sym.sd, code.sd, paragraphno.sd, newOptions)
for acc2 = acc, sym ∈ toseq.inithasstate
do acc2 + symdef4(sym, empty:seq.symbol, 0, "STATE"),
acc2

Function GG(mm:set.symdef) set.symdef
for acc = empty:set.symdef, sd ∈ toseq.mm
do
 if {%.sym.sd =" parsersupport.bindinfo:last (reduction.bindinfo) bindinfo" /and} n.code.sd > 0 then
  {assert length.acc < 40750 report" XXX"+%.length.acc+%.sym.sd+%.code.sd}
  let b = {checkTailRecursion (C (code.sd, mm), sym.sd)} C(code.sd, mm)
  let b3 = FF.b
  {assert false report"^(sym.sd)^(getOptions.sd)^(code.sd)
   /p^(b)
   /p^(b3)
   /p"+%n.encodingdata:exp}
  acc + symdef4(sym.sd, b3, paragraphno.sd, getOptionsBits.sd)
 else acc + sd,
acc

use symbol

function check(code:seq.symbol, hasstate:set.symbol) boolean
if 1^code ∈ hasstate then
for acc = true, sy ∈ code >> 1 while acc do acc = sy ∉ hasstate, not.acc
else true

function %(a:symdef) seq.word "/p^(getOptions.a)^(sym.a)^(paragraphno.a)"

function >1(a:exp, b:exp) ordering sym.a >1 sym.b

type exp is sym:symbol, args:seq.Exp, bits:bits

function exp(sym:symbol, args:seq.Exp) exp
exp(sym, args, if not.isconst.sym ∧ name.sym ∈ "DEF2" then SymHasStateFlag else 0x0)

use set.exp

type Exp is bits:bits

function flagsNo int 4

function ConstFlag bits 0x1

function LocalFlag bits 0x2

function SymHasStateFlag bits 0x4

function uses(e:Exp) set.Exp
if isConst.e ∨ isLocal.e then empty:set.Exp else uses(e, empty:set.Exp, false)

function avail(e:Exp) set.Exp
if isConst.e ∨ isLocal.e then empty:set.Exp else uses(e, empty:set.Exp, true)

function avail(s:seq.Exp) set.Exp
for acc = empty:set.Exp, b ∈ s
do if isConst.b ∨ isLocal.b then acc else acc ∪ uses(b, acc, true),
acc

function uses(e:Exp, k:set.Exp, avail:boolean) set.Exp
let a = toexp.e
let t =
 if avail then
  if isloopblock.sym.a then
  args.a >> 1
  else if isbr.sym.a then
  {??? only includes branch condition but loop contains defs too} [(n.args.a - 2)_args.a]
  else args.a
 else args.a
for acc = k + e, b ∈ t
do if isConst.b ∨ isLocal.b ∨ b ∈ k then acc else acc ∪ uses(b, acc, avail),
acc

use set.Exp

function >1(a:Exp, b:Exp) ordering toint.bits.a >1 toint.bits.b

function flags(a:exp) bits
if islocal.sym.a then
LocalFlag
else if isconst.sym.a ∨ (isSequence.sym.a ∨ isRecord.sym.a) ∧ allconst.a then
ConstFlag
else bits.a

function allconst(a:exp) boolean for acc = true, e ∈ args.a while acc do isConst.e, acc

function isConst(e:Exp) boolean (bits.e ∧ ConstFlag) ≠ 0x0

function isLocal(e:Exp) boolean (bits.e ∧ LocalFlag) ≠ 0x0

function isDEF2(e:Exp) boolean (bits.e ∧ SymHasStateFlag) ≠ 0x0

function toexp(a:Exp) exp decode.to:encoding.exp(toint(bits.a >> flagsNo))

function toExp(a:exp) Exp Exp(bits.valueofencoding.encode.a << flagsNo ∨ flags.a)

function =(a:Exp, b:Exp) boolean bits.a = bits.b

function =(a:exp, b:exp) boolean sym.a = sym.b ∧ args.a = args.b

function hash(e:exp) int
for acc = hash(hashstart, hash.worddata.sym.e), a ∈ args.e do hash(acc, toint.bits.a),
finalmix.acc

use xxhash

function toSeqExp(a:seq.exp) seq.Exp for acc = empty:seq.Exp, e ∈ a do acc + toExp.e, acc

function %(a:Exp) seq.word
if false then
"{^(toint.bits.a)}"
else
 let e = toexp.a,
 %.args.e + %.sym.e + if isempty.args.e then "" else "{^(toint.bits.a)}"

function removeStart(e:exp) Exp
if isExit.sym.e then
let t = 1_args.e let b = toexp.t, if isstart.sym.b then 1_args.b else t
else
 {assert isconst.sym.e ∨ islocal.sym.e report" XX"+%.sym.e}
 if isstart.sym.e ∨ isExit.sym.e then 1_args.e else toExp.e

function %(e:exp) seq.word "expression^(name.sym.e) [^(%n.args.e)]"

%.toExp.e

use stack.seq.exp

function HH(s:seq.Exp, b:set.Exp, result:seq.Exp) seq.Exp
{we do not want to move calculation done in an outer to and inner basic block. This figures out
 which calculations are not used in the inter block and removes them}
if isempty.s then
result
else
 let e = 1^s,
  if e ∈ b then
  HH(s >> 1, b \ avail.e, [e] + result)
  else if isConst.e ∨ isLocal.e then
  HH(s >> 1, b, result)
  else
   let c = toexp.e,
   HH(
    s >> 1
    + if isloopblock.sym.c then args.c >> 1 else if isbr.sym.c then [1_args.c] else args.c
    , b
    , result
   )

function C(code:seq.symbol, mm:set.symdef) Exp
let PreFref0 = PreFref
for
 blkstk = empty:seq.symbol
 , cnt = {???} 1
 , pre = empty:seq.Exp
 , stk = empty:stack.exp
 , locals = empty:set.exp
 , last = Lit.1
 , sy ∈ code
do
 {assert length.blkstk < 75 report" XX"+%.length.code+%.blkstk+"
  /p
  /p"+% (code << length.blkstk)}
 (
  if isconst.sy then
  next(blkstk + sy, cnt, pre, push(stk, exp(sy, empty:seq.Exp)), locals, sy)
  else if last = PreFref0 then
  next(blkstk + sy, cnt, pre, push(stk, exp(Fref.sy, empty:seq.Exp)), locals, sy)
  else if isspecial.sy then
   if sy = PreFref0 then
   next(blkstk, cnt, pre, stk, locals, sy)
   else if sy = EndBlock then
    let parts =
     for stk2 = stk, acc = empty:seq.exp, x ∈ constantseq(n.toseq.stk, 0)
     while not.isstartorloop.sym.top.stk2
     do
      let blocksym = sym.top.stk2,
       if isExit.blocksym ∨ iscontinue.blocksym then
       next(pop.stk2, [top.stk2] + acc)
       else
        assert isbr.blocksym report "DSF^(blocksym)^(code)^(%n.toseq.stk)"
        let used = uses.toExp.(brt.blocksym)_acc ∪ uses.toExp.(brf.blocksym)_acc \ avail.1^args.top.stk2,
        next(
         pop.stk2
         , [exp(
          blocksym
          , HH(args.top.stk2 >> 1, used, empty:seq.Exp)
           + 1^args.top.stk2
           + removeStart.(brt.blocksym)_acc
           + removeStart.(brf.blocksym)_acc
         )]
          + acc
        )
     let body = toExp.1_acc
     let args = args.top.stk2
     let defs = args >> nopara.sym.top.stk2
     let newargs =
      if isempty.defs then
      args + body
      else
       let loopargs = args << n.defs
       let used = uses.body \ avail.loopargs,
       HH(defs, used, empty:seq.Exp) + loopargs + body,
     push(pop.stk2, exp(sym.top.stk2, newargs)),
    next(blkstk + sy, cnt, empty:seq.Exp, parts, locals, sy)
   else if isdefine.sy then
    if islocal.sym.top.stk ∨ isconst.sym.top.stk then
    next(blkstk + sy, cnt, pre, pop.stk, locals + exp(Local.value.sy, [toExp.top.stk]), sy)
    else
     let argx = [{?} toExp.top.stk, toExp.exp(Lit.cnt, empty:seq.Exp)],
     next(
      blkstk + sy
      , cnt
      , pre + toExp.top.stk
      , pop.stk
      , locals + exp(Local.value.sy, [toExp.top.stk])
      , sy
     )
   else if islocal.sy ∧ not.isempty.lookup(locals, exp(sy, empty:seq.Exp)) then
    let a = lookup(locals, exp(sy, empty:seq.Exp)),
    next(blkstk + sy, cnt, pre, push(stk, toexp.1_args.1_a), locals, sy)
   else if isstart.sy then
   next(blkstk + sy, cnt, pre, push(stk, exp.sy), locals, sy)
   else if isbr.sy ∨ isloopblock.sy then
    let exp = {?} exp(sy, pre + toSeqExp.top(stk, nopara.sy)),
    next(blkstk + sy, cnt, empty:seq.Exp, push(pop(stk, nopara.sy), exp), locals, sy)
   else if sy = Exit then
   next(
    blkstk + sy
    , cnt
    , empty:seq.Exp
    , push(pop.stk, exp(Exit, [wrappre(stk, pre)]))
    , locals
    , sy
   )
   else
    let exp = {?} exp(sy, toSeqExp.top(stk, nopara.sy)),
    next(blkstk + sy, cnt, pre, push(pop(stk, nopara.sy), exp), locals, sy)
  else
   let sd = getSymdef(mm, sy),
    if not.isempty.sd ∧ hasState.1_sd then
     let argx = [{?} toExp.exp(sy, toSeqExp.top(stk, nopara.sy)), toExp.exp(Lit.cnt, empty:seq.Exp)]
     let expx = exp(symbol(internalmod, "DEF2", typeint), argx),
     next(blkstk + sy, cnt + 1, pre + toExp.expx, push(pop(stk, nopara.sy), expx), locals, sy)
    else
     let exp = {?} exp(sy, toSeqExp.top(stk, nopara.sy)),
     next(blkstk + sy, cnt, pre, push(pop(stk, nopara.sy), exp), locals, sy)
 ),
wrappre(stk, pre)

function wrappre(stk:stack.exp, pre:seq.Exp) Exp
toExp.
 if isempty.pre then
 top.stk
 else exp(symbol(internalmod, "DEF", typeint), pre + toExp.top.stk)

type result is code:seq.symbol, places:seq.place, parts:seq.Exp, fixes:seq.loc

function result(code:seq.symbol, places:seq.place, fixes:seq.loc) result
result(code, places, empty:seq.Exp, fixes)

type place is exp:Exp, idx:int

use otherseq.place

use otherseq.mytype

function =(a:place, b:place) boolean exp.a = exp.b

function %(p:place) seq.word "[^(toint.bits.exp.p)^(idx.p)]"

function FF(e:Exp) seq.symbol
let r = FF(e, empty:seq.symbol, empty:seq.place, empty:seq.loc, true)
for acc = code.r, f ∈ toseq.asset.fixes.r
do subseq(acc, 1, loc.f) + Define(100 + loc.f) + Local(100 + loc.f) + acc << loc.f,
acc

function addExit(s:seq.symbol) seq.symbol
if isExit.1^s ∨ iscontinue.1^s then s else s + Exit

function FF(
 e:Exp
 , codein:seq.symbol
 , placein:seq.place
 , infixes:seq.loc
 , share:boolean
) result
let i = if share then findindex(placein, place(e, 0)) else n.placein + 1,
if i ≤ n.placein then
 let idx = idx.i_placein,
 result(
  codein + Local(100 + idx)
  , placein
  , if idx < n.codein ∧ isdefine.(idx + 1)_codein then
   infixes
   else infixes + loc.idx.i_placein
 )
else
 let d = toexp.e,
  if isconst.sym.d then
  result(codein + sym.d, placein, infixes)
  else if isstart.sym.d then
   let r = FF(1_args.d, codein + sym.d, placein, infixes, true),
   result(code.r + EndBlock, places.r + place(e, n.code.r + 1), fixes.r)
  else if isbr.sym.d then
   let z = args.d << (n.args.d - 3)
   let r =
    if n.args.d > 3 then
     let r1 = defs(args.d >> 3, codein, placein, infixes, true),
     FF(1_z, code.r1, places.r1, fixes.r1, true)
    else FF(1_z, codein, placein, infixes, true)
   let r2 = FF(2_z, code.r + Br2(1, 2), places.r, fixes.r, true)
   let r3 = FF(3_z, addExit.code.r2, places.r, fixes.r2, true)
   let partsTrue = if 1^code.r2 = Exit then parts.r2 else [2_z]
   let partsFalse = if 1^code.r3 = Exit then parts.r3 else [3_z]
   let idxtrue = findindex(partsFalse, 2_z),
    if idxtrue ≤ n.partsFalse then
     let r4 = FF(3_z, code.r + Br2(idxtrue, 1), places.r, fixes.r, true),
     result(addExit.code.r4, placein, [e] + partsFalse, fixes.r4)
    else
     let tmp =
      if brf.sym.d = n.partsTrue + 1 then
      code.r3
      else code.r + Br2(1, n.partsTrue + 1) + code.r3 << (n.code.r + 1),
     result(addExit.tmp, placein, [e] + partsTrue + partsFalse, fixes.r3)
  else if name.sym.d ∈ "DEF2" then
   let r = FF(1_args.d, codein, placein, infixes, false),
   result(code.r, places.r + place(e, n.code.r), fixes.r)
  else if name.sym.d ∈ "DEF" then
   let r0 = defs(args.d >> 1, codein, placein, infixes, false),
   FF(1^args.d, code.r0, places.r0, fixes.r0, false)
  else if isloopblock.sym.d then
   let body = 1^args.d
   let defs = args.d >> (nopara.sym.d + 1)
   let params = subseq(args.d, n.defs + 1, n.args.d - 1)
   let r0 = defs(defs, codein, placein, infixes, true)
   for code = code.r0, place = places.r0, fixes = fixes.r0, a ∈ params
   do let r = FF(a, code, place, fixes, true), next(code.r, places.r, fixes.r)
   let r = FF(body, code + sym.d, place, fixes, true),
   result(code.r + EndBlock, places.r + place(e, n.code.r + 1), fixes.r)
  else
   for code = codein, place = placein, fixes = infixes, a ∈ args.d
   do
    {assert toint.bits.e /in [96, 64, 32, 18] report %.e+"
     /p"+%.a+" places"+%.place+" fixes:"+%.fixes}
    let r = FF(a, code, place, fixes, true), next(code.r, places.r, fixes.r),
   result(
    code + sym.d
    , if isempty.args.d ∨ not.share then place else place + place(e, n.code + 1)
    , fixes
   )

function defs(
 defs:seq.Exp
 , codein:seq.symbol
 , placein:seq.place
 , infixes:seq.loc
 , all:boolean
) result
for code = codein, place = placein, fixes = infixes, a ∈ defs
do
 if all ∨ isDEF2.a then
  let r = FF(a, code, place, fixes, true),
  next(code.r + Define(100 + n.code.r), places.r, fixes.r)
 else next(code, place, fixes),
result(code, place, fixes)

type loc is loc:int

function >1(a:loc, b:loc) ordering loc.b >1 loc.a

function %(a:loc) seq.word %.loc.a

function exp(s:symbol) exp exp(s, empty:seq.Exp)

_____________________

function checkTailRecursion(e:Exp, this:symbol) Exp
let d = toexp.e,
if not.isstart.sym.d then
e
else
 let t = expandBlock(toexp.1_args.d, this),
  if t = 1_args.d then
  e
  else
   for acc = empty:seq.Exp, i ∈ arithseq(nopara.this, 1, 1) do acc + toExp.exp.Local.i,
   toExp.exp(Loopblock(paratypes.this, nopara.this + 1, resulttype.this), acc + adjust(t, nopara.this))

Function adjust(e:Exp, val:int) Exp
{??? need to handle loopblock}
let d = toexp.e,
if islocal.sym.d then
toExp.exp.Local(value.sym.d + val)
else for acc = empty:seq.Exp, a ∈ args.d do acc + adjust(a, val) {?} toExp.exp(sym.d, acc)

Function expandBlock(d:exp, this:symbol) Exp
assert isbr.sym.d report "???"
let argt = (n.args.d - 1)_args.d
let argf = 1^args.d
let bt = toexp.argt
let bf = toexp.argf
let newbt =
 if isbr.sym.bt then
 expandBlock(bt, this)
 else if this = sym.bt then
 toExp.exp(continue.nopara.this, args.bt)
 else argt
let newbf =
 if isbr.sym.bf then
 expandBlock(bf, this)
 else if this = sym.bf then
 toExp.exp(continue.nopara.this, args.bf)
 else argf,
toExp.exp(sym.d, args.d >> 2 + [newbt, newbf])

function isverysimple(nopara:int, code:seq.symbol) boolean
if code = [Local.1] ∧ nopara = 1 then
true
else
 for isverysimple = n.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do next(
  if idx ≤ nopara then
  sym = Local.idx
  else not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
  , idx + 1
 ),
 isverysimple

function hasstate(hasstate:set.symbol, unknown:seq.symdef) set.symbol
let PreFref0 = PreFref
for hasstate0 = hasstate, acc = empty:seq.symdef, sd ∈ unknown
do
 if name.sym.sd ∈ "makereal" ∧ %.sym.sd = "real:makereal (seq.word) real" then
 next(hasstate0, acc)
 else
  let options = getOptions.sd,
   if 1_"STATE" ∈ options then
   next(hasstate0 + sym.sd, acc)
   else
    let nostate =
     for nostate = true, last = Lit.0, sy ∈ code.sd
     while nostate
     do next(
      if isspecial.sy ∨ sy = sym.sd ∨ last = PreFref0 then
      nostate
      else not.isGlobal.sy ∧ sy ∉ hasstate
      , sy
     ),
     nostate,
    if nostate then next(hasstate0, acc + sd) else next(hasstate0 + sym.sd, acc),
if n.acc = n.unknown then hasstate else hasstate(hasstate0, acc) 