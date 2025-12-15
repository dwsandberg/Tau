Module compilerfrontT.T

use compileTimeT.T

use addprofile

use backparse

use bits

use compilerfront

use entrypoint

use process.expandresult

use file

use seq.file

use localmap2

use set.localmap2

use objectio.midpoint

use seq.midpoint

use seq.modExports

use seq1.modref

use set.modref

use seq1.mytype

use seq.mytype

use seq.seq.mytype

use orderModules

use pass2

use seq1.seg

use standard

use stack.stkele

use seq.symbol

use seq1.seq.symbol

use symbol1

use seq.symbolKind

use symbolconstant

use seq.symdef

use set.symdef

use set.word

Function newanal:T(ss:seq.symbol, self:symbol, options:seq.word) seq.symbol
let nopara = nopara.self
for pdict = empty:set.localmap2, parano ∈ arithseq(nopara, 1, 1)
do pdict + localmap2(parano, [Local.parano]),
code.newanal:T(
 ""
 , empty:set.symdef
 , ss
 , self
 , nopara + 1
 , pdict
 , "dummylib" sub 1
 , emptytypedict
 , options
)

Function compilerFront:T(
option:seq.word
, input:seq.file
, exports0:seq.word
, entryUses:seq.word
) midpoint
{OPTION PROFILEX}
for libinfo = empty:midpoint, srcfiles = empty:seq.file, i ∈ input
do
 if ext.fn.i ∈ "libinfo" then
  let new = inbytes:midpoint(data.i) sub 1,
  next(
   midpoint(
    ""
    , prg.libinfo ∪ prg.new
    , emptytypedict
    , libmods.libinfo + libmods.new
    , empty:seq.seq.word
   )
   , srcfiles
  )
 else if ext.fn.i ∈ "lib html" then next(libinfo, srcfiles)
 else
  assert ext.fn.i ∈ "ls libsrc" report "Extension" + fullname.fn.i,
  next(libinfo, srcfiles + i)
let allsrc = breakparagraph.srcfiles
let libname =
 libname.midpoint(option, empty:set.symdef, emptytypedict, empty:seq.modExports, allsrc)
let exports = extractExports(allsrc, exports0)
let m =
 if "bitcode" sub 1 ∉ option then compilerfront3(option, allsrc, libname, exports, libinfo)
 else
  let EPname = merge.[libname, "$EP" sub 1],
  compilerfront3(
   option
   , allsrc + ["Module:(EPname)"] + modEntry(allsrc, entryUses, false)
   , libname
   , exports + EPname
   , libinfo
  ),
if (option.m) sub 1 ∈ "library text pass1 pass1a prebind" then m
else
 let librarymap = [libname, "*" sub 1]
 let prg = {if"xxx"sub 1 ∈ option then GG.hasstate.prg.m else}prg.m
 let prg5 = pass2:T(librarymap, prg, typedict.m, option, libname, libinfo),
 let m2 =
  if "profile" sub 1 ∈ option then
   let profinit = symbol(moduleref.[libname, "initialize" sub 1], "initProfile", typeptr)
   let profdata = symbol(moduleref.[libname, "initialize" sub 1], "profileData", typeptr),
   let prg6 = addprofile(prg5, libname),
   if isempty.prg6 then m
   else
    midpoint5(
     option
     , prg6 ∪ prg5
     , templates.m
     , typedict.m
     , libmods.m + modExports(module.profinit, [profinit, profdata], empty:seq.seq.mytype)
     , src.m
    )
  else midpoint5(option, prg5, templates.m, typedict.m, libmods.m, src.m),
 if "bitcode" sub 1 ∈ option then
  let m3 = prepareback(m2, libinfo, extractValue(option, "uses")),
  midpoint5(option.m3, prg.m3, templates.m3, typedict.m3, libmods.m3, src.m3 + allsrc)
 else midpoint5(option.m2, prg.m2, templates.m2, typedict.m2, libmods.m2, src.m2 + allsrc)

unbound interpretCompileTime:T(
librarymap:seq.word
, args:seq.symbol
, ctsym:symbol
, typedict:typedict
) seq.symbol

Function pass2:T(
librarymap:seq.word
, prg:set.symdef
, typedict:typedict
, option:seq.word
, libname:word
, libinfo:midpoint
) set.symdef
{OPTION PROFILE}
let nojumptable = "nojumptable" sub 1 ∈ option
for
 big = empty:seq.symdef
 , complete = empty:set.symdef
 , modorder = empty:seq.symbol
 , pele0 ∈ toseq.prg
do
 let code = code.pele0,
 if isempty.code then next(big, complete + pele0, modorder)
 else
  let newoptions = calcOptions(sym.pele0, options.pele0, code),
  if nonReducible ∈ newoptions then
   let sd = symdef4(sym.pele0, code.pele0, paragraphno.pele0, newoptions),
   next(big, complete + sd, modorder)
  else if kind.sym.pele0 = kconstantrecord then
   for acc = [code sub 1], last = code sub 1, c ∈ code << 1
   do next(if kind.last = kprefref then acc >> 1 + Fref.c else acc + c, c)
   let sd = symdef4(sym.pele0, acc, paragraphno.pele0, options.pele0),
   let discard = registerConstant.sd,
   next(big, complete, modorder)
  else if libname ≠ library.module.sym.pele0 ∧ not.isempty.getSymdef(prg.libinfo, sym.pele0) then
   {???? optimize add flag in sd so do not need to do lookup of in libinfo}
   let sd = symdef4(sym.pele0, code.pele0, paragraphno.pele0, newoptions),
   next(big, complete + sd, modorder)
  else if OrderSym = sym.pele0 then next(big, complete, fullconstantcode.(code.pele0) sub 1)
  else next(big + pele0, complete, modorder)
let final =
 if nojumptable then "nojumptable noinline tailrecursion" else "noinline tailrecursion"
let jjmp = if nojumptable then "nojumptable" else ""
let segs = tosegs(asset.big, modorder)
assert true report %.segs + "/p" + check(segs, toseq.prg, complete)
for prg1 = complete, e ∈ segs
do
 for prg5 = prg1, part1 = part.e, x ∈ [1, 2]
 do
  for prg2 = prg5, part2 = empty:seq.symdef, sd ∈ part1
  do
   let self = sym.sd
   let nopara = nopara.self
   let pdict = pdict.nopara
   let kk = options.sd
   for code0 = code.sd, cnt = 1
   while cnt > 0
   do
    let tmp =
     code.newanal:T(librarymap, prg2, code0, self, nopara + 1, pdict, libname, typedict, jjmp)
    let newcnt = if cnt < 3 ∧ n.code.sd < 35 ∧ tmp ≠ code0 then cnt + 1 else 0,
    next(tmp, newcnt)
   let code1 =
    if x = 2 ∧ INLINE ∉ kk then
     code.newanal:T(librarymap, prg2, code0, self, nopara + 1, pdict, libname, typedict, final)
    else code0
   let newoptions = calcOptions(self, kk, code1),
   let newsd = symdef4(self, code1, paragraphno.sd, newoptions),
   next(newsd ∪ prg2, if nonReducible ∈ newoptions then part2 else part2 + newsd),
  next(prg2, part2),
 prg5,
prg1 ∪ constantsymbols.libname

Function newanal:T(
librarymap:seq.word
, prg:set.symdef
, ss:seq.symbol
, self:symbol
, nextvarX:int
, mapX:set.localmap2
, libname:word
, typedict:typedict
, options:seq.word
) expandresult
{OPTION XPROFILE}
let EndMark = symbol(internalmod, "endmark", typeint)
let nojumptable = "nojumptable" sub 1 ∈ options
let noinline = "noinline" sub 1 ∈ options
let tailrecursion = "tailrecursion" sub 1 ∈ options
let debug = "debug" sub 1 ∈ options
for
 part = empty:seq.symbol
 , blkparts = empty:seq.seq.symbol
 , stk = empty:stack.stkele
 , nextvar = nextvarX
 , map = mapX
 , sym = Lit.0
 , ahead ∈ ss + if isconst.self then Lit.0 else EndMark
do
 let kind = kind.sym,
 if between(kind, kfref, kconstantrecord) ∨ kind ∈ [kjmpB, klabel] then next(part + sym, blkparts, stk, nextvar, map, ahead)
 else if kind = klocal then
  let t = lookup(map, value.sym),
  next(
   part + (if isempty.t then [sym] else value.t sub 1)
   , blkparts
   , stk
   , nextvar
   , map
   , ahead
  )
 else if kind = kdefine then
  let thelocal = value.sym
  let len = n.part,
  if len > 0 ∧ (isconst.part sub len ∨ kind.part sub len = klocal) then next(part >> 1, blkparts, stk, nextvar, localmap2(thelocal, [part sub len]) ∪ map, ahead)
  else
   {renumber}
   next(
    part + Define.nextvar
    , blkparts
    , stk
    , nextvar + 1
    , localmap2(thelocal, [Local.nextvar]) ∪ map
    , ahead
   )
 else if kind ∈ [krecord, ksequence] then
  let nopara = nopara.sym
  let len = n.part
  let args = subseq(part, len + 1 - nopara, len),
  for constargs = n.args = nopara, @e ∈ args while constargs do isconst.@e,
  if constargs then next(part >> nopara + Constant2(libname, args + sym), blkparts, stk, nextvar, map, ahead)
  else next(part + sym, blkparts, stk, nextvar, map, ahead)
 else if kind ∈ [kcontinue, kexit] then next(empty:seq.symbol, blkparts + (part + sym), stk, nextvar, map, ahead)
 else if kind ∈ [kjmp] then
  let jmparg = part sub (n.part - value.sym + 1)
  let newpart =
   if isconst.jmparg then
    let tmp = part << (n.part - value.sym + 2)
    for last = tmp sub 1, continue = true, e ∈ tmp << 1
    while continue
    do if last = jmparg then next(e, false) else next(e, true),
    subseq(part, 1, n.part - value.sym) + Littrue + Br2(value.last, value.last)
   else part + sym,
  next(empty:seq.symbol, blkparts + newpart, stk, nextvar, map, ahead)
 else if kind = kloop then
  {renumber}
  let nopara = nopara.sym
  let addlooplocals =
   for pmap = map, parano = 1, e ∈ constantseq(10000, 1)
   while parano ≤ nopara
   do
    next(
     localmap2(firstvar.sym + parano - 1, [Local(nextvar + parano - 1)]) ∪ pmap
     , parano + 1
    ),
   pmap,
  let newsym = Loopblock(paratypes.sym, nextvar, resulttype.sym),
  next(
   empty:seq.symbol
   , empty:seq.seq.symbol
   , push(stk, stkele(part + newsym, blkparts))
   , nextvar + nopara
   , addlooplocals
   , ahead
  )
 else if kind = kstart then
  next(
   empty:seq.symbol
   , empty:seq.seq.symbol
   , push(stk, stkele(part + sym, blkparts))
   , nextvar
   , map
   , ahead
  )
 else if kind = kbr then
  let newpart =
   if kind.last.part = knot then part >> 1 + Br2(brf.sym, brt.sym)
   else part + Br2(brt.sym, brf.sym),
  next(empty:seq.symbol, blkparts + newpart, stk, nextvar, map, ahead)
 else if kind = kendblock then
  let blockheader = last.part.top.stk,
  if kind.blockheader ≠ kstart then
   {at the end of a loop block}
   let checkNoOp =
    if nopara.blockheader = 2 then checkLoopIsNoOp(part.top.stk, blkparts, self)
    else empty:seq.symbol,
   if not.isempty.checkNoOp then next(checkNoOp, blkparts.top.stk, pop.stk, nextvar, map, ahead)
   else
    let tmp = blocktocode(part.top.stk, blkparts, self, nojumptable, nextvar),
    next(code.tmp, blkparts.top.stk, pop.stk, nextvar.tmp, map, ahead)
  else if kind.last.blkparts sub 1 = kexit then
   {remove block with just one Exit}
   next(
    part.top.stk >> 1 + blkparts sub 1 >> 1
    , blkparts.top.stk
    , pop.stk
    , nextvar
    , map
    , ahead
   )
  else if kind.ahead = kexit then
   {combine current block with outer block}
   let tmp2 =
    adjustbr(blkparts.top.stk, n.blkparts)
    + [part.top.stk >> 1 + blkparts sub 1]
    + blkparts << 1,
   next(last.tmp2 >> 1, tmp2 >> 1, pop.stk, nextvar, map, last.last.tmp2)
  else if kind.ahead = kbr then
   {combine boolean block with outer block}
   for partsA = empty:seq.seq.symbol, brt = brt.ahead, brf = brf.ahead, p ∈ reverse.blkparts
   do
    let p1 = if kind.last.p = kexit then p >> 1 + Br2(brt, brf) else p,
    next([p1] + partsA, brt + 1, brf + 1)
   let tmp2 =
    adjustbr(blkparts.top.stk, n.blkparts)
    + [part.top.stk >> 1 + partsA sub 1]
    + partsA << 1,
   next(last.tmp2 >> 1, tmp2 >> 1, pop.stk, nextvar, map, last.last.tmp2)
  else
   let recursive =
    if tailrecursion ∧ ahead = EndMark then checkrecursive(blkparts, self, part.top.stk, nojumptable, nextvar)
    else empty:seq.symbol,
   if not.isempty.recursive then next(recursive, blkparts.top.stk, pop.stk, nextvar + nopara.self, map, ahead)
   else
    let tmp = blocktocode(part.top.stk, blkparts, self, nojumptable, nextvar),
    next(code.tmp, blkparts.top.stk, pop.stk, nextvar.tmp, map, ahead)
 else
  {end of kind = kendblock}
  if not.isempty.part ∧ kind.last.part = kprefref then next(part >> 1 + Fref.sym, blkparts, stk, nextvar, map, ahead)
  else if kind
  ∈ [
   kdivint
   , kmulint
   , kaddint
   , ksubint
   , kgetseqtype
   , kgetseqlength
   , kidx
   , kidxNB
   , kmakereal
   , kaddreal
   , ksubreal
   , keqlI
   , keqlB
   , kgrtI
   , k<<bits
   , k>>bits
   , kxorbits
   , k∨bits
   , k∧bits
   , kfld
  ] then
   let nopara = nopara.sym
   let compiletime2 =
    if nopara = 1 ∧ isconst.kind.last.part then builtinCompileTime(part, sym, libname)
    else if nopara = 2 ∧ isconst.kind.last.part ∧ isconst.kind.part sub (n.part - 1) then builtinCompileTime(part, sym, libname)
    else empty:seq.symbol,
   if not.isempty.compiletime2 then next(compiletime2, blkparts, stk, nextvar, map, ahead)
   else next(part + sym, blkparts, stk, nextvar, map, ahead)
  else if kind = knot then
   let last = last.part
   let kind2 = kind.last,
   let newPart =
    if kind.last = knot then part >> 1
    else if kind2 = ktrue then part >> 1 + Litfalse
    else if kind2 = kfalse then part >> 1 + Littrue
    else part + sym,
   next(newPart, blkparts, stk, nextvar, map, ahead)
  else if kind = kmember
  ∧ kind.last.part ∈ [kconstantrecord, ksequence, kwords]
  ∧ not.isseq.(paratypes.sym) sub 1 then
   let p1 = (paratypes.sym) sub 1
   let r = membercode(p1, part, prg, nextvar),
   if isempty.code.r then next(part + sym, blkparts, stk, nextvar, map, ahead)
   else next(code.r, blkparts, stk, nextvar.r, map, ahead)
  else if sym = self then next(part + sym, blkparts, stk, nextvar, map, ahead)
  else
   let newresult =
    if kind.sym = kcat then checkemptycat(sym, part) else empty:seq.symbol,
   if not.isempty.newresult then next(newresult, blkparts, stk, nextvar, map, ahead)
   else
    let nopara = nopara.sym
    let b = getSymdef(prg, sym)
    let symoptions = if isempty.b then NOOPTIONS else options.b sub 1,
    let compiletime =
     if not(COMPILETIME ∈ symoptions ∨ name.sym ∈ "sub" ∧ nopara = 2) then empty:seq.symbol
     else
      let len = n.part
      let args = subseq(part, len - nopara + 1, len),
      for allconstant = true, sy ∈ args while allconstant do isconst.sy,
      if allconstant then compileTime:T(librarymap, part, args, sym, typedict, libname)
      else empty:seq.symbol,
    if not.isempty.compiletime then next(compiletime, blkparts, stk, nextvar, map, ahead)
    else if noinline ∨ INLINE ∉ symoptions ∨ isempty.b then next(part + sym, blkparts, stk, nextvar, map, ahead)
    else
     let code = code.b sub 1,
     if VERYSIMPLE ∈ symoptions then next(part + code << nopara.sym, blkparts, stk, nextvar, map, ahead)
     else if n.code = 1 ∧ code = [Local.1] ∧ nopara = 1 then{function just returns result}next(part, blkparts, stk, nextvar, map, ahead)
     else if nopara = 0 then
      let r =
       newanal:T(librarymap, prg, code, self, nextvar, empty:set.localmap2, libname, typedict, options),
      next(part + code.r, blkparts, stk, nextvar.r, map, ahead)
     else
      for
       paracode = empty:seq.symbol
       , pmap = empty:set.localmap2
       , nextvarExpand = nextvar
       , idx = n.part
       , parano = nopara
      while parano > 1
      do
       let tmp = backparse3(part, idx, true)
       let paraval = subseq(part, tmp, idx),
       if n.paraval = 1 ∧ (isconst.paraval sub 1 ∨ kind.paraval sub 1 = klocal) then next(paracode, pmap + localmap2(parano, paraval), nextvarExpand, tmp - 1, parano - 1)
       else
        next(
         paraval + Define.nextvarExpand + paracode
         , pmap + localmap2(parano, [Local.nextvarExpand])
         , nextvarExpand + 1
         , {idx}tmp - 1
         , parano - 1
        )
      let r =
       newanal:T(
        librarymap
        , prg
        , code
        , self
        , nextvarExpand + 1
        , pmap + localmap2(1, [Local.nextvarExpand])
        , libname
        , typedict
        , options
       ),
      let expandresult = subseq(part, 1, idx) + Define.nextvarExpand + paracode + code.r,
      next(expandresult, blkparts, stk, nextvar.r, map, ahead)
{for maxvar = nextvarX-1, p ∈ part do if islocal.p ∨ isdefine.p then max(value.p, maxvar)else maxvar assert maxvar < nextvar report %.maxvar+"/br
nextvar:(nextvar)/br
self::(self)"+%.part,}
expandresult(nextvar, part << 1)

use seq1.localmap2

use seq1.stkele

function compileTime:T(
librarymap:seq.word
, part:seq.symbol
, args:seq.symbol
, sym:symbol
, typedict:typedict
, libname:word
) seq.symbol
if name.sym ∈ "=" ∧ name.module.sym ∈ "seq" ∧ args sub 1 = args sub 2 then part >> n.args + [Littrue]
else
 let tmp6 = interpretCompileTime:T(librarymap, args, sym, typedict)
 assert isempty.tmp6 ∨ name.sym ∉ "idxNB" ∨ %.parameter.(paratypes.sym) sub 1 ∈ ["word", "int"] report "YYY:(basetype((paratypes.sym) sub 1, typedict)):(sym)",
 if isempty.tmp6 then empty:seq.symbol else part >> n.args + makeconst(libname, tmp6)
 