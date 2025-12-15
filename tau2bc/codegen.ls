Module codegen

use seq1.Lcode

use seq.Lcode

use stack.Lcode

use UTF8

use bits

use seq.byte

use seq.seq.char

use codetemplates

use codetemplates2

use file

use seq.file

use idxNBtemplate

use seq1.int

use seq.int

use seq.seq.int

use stack.int

use internalbc

use process.internalbc

use seq.internalbc

use llvm

use llvmcode

use seq1.llvmtype

use seq.llvmtype

use seq1.localmap

use seq.localmap

use seq.match5

use mytype

use seq1.mytype

use seq.mytype

use persistant

use seq.slot

use standard

use seq1.symbol

use set.symbol

use symbol1

use seq.symbolKind

use seq.symdef

use set.symdef

use seq.seq.word

use set.word

use encoding.word3

use seq.encoding.word3

function nameslot(b:seq.char) slot
let libnametype = array(n.b + 1, i8),
modulerecord(
 ""
 , [
  toint.GLOBALVAR
  , typ.libnametype
  , 2
  , toint.DATA(libnametype, tointseq.b + 0) + 1
  , 3
  , toint.align8
  , 0
 ]
)

builtin basewords seq.seq.char

Function compilerback(
m:midpoint
, outname:filename
, options:seq.word
, uses:seq.word
) seq.file
{OPTION PROFILEX}
let libname = libname.m
let baselib = extractValue((src.m) sub 1, "baselib") sub 1
let initprofile =
 for acc = empty:seq.symbol, x ∈ libmods.m
 do if name.modname.x ∈ "initialize" then acc + exports.x else acc,
 toseq.asset.acc
let bcwordFilename = filename."+:(dirpath.outname):(baselib).bcword"
let baselibwords = if isempty.uses then empty:seq.seq.char else basewords
let bcwords = if isempty.uses then empty:seq.char else getbcwords.bcwordFilename
let typedict = typedict.m
let isbase = isempty.uses
let prgX = prg.m
let t5a =
 getSymdef(
  prgX
  , symbol(
   moduleref.[libname, "entrypoint" sub 1]
   , "entrypoint"
   , [typeref."UTF8 UTF8 *"]
   , typeref."UTF8 UTF8 *"
  )
 )
let t5 =
 if not.isempty.t5a then t5a
 else
  getSymdef(
   prgX
   , symbol(
    moduleref.[libname, merge.[libname, "$EP" sub 1]]
    , "entrypoint"
    , [typeref."UTF8 UTF8 *"]
    , typeref."UTF8 UTF8 *"
   )
  )
assert not.isempty.t5 report
 for txt = "", p ∈ toseq.prgX do if name.sym.p ∈ "entrypoint" then txt + %.sym.p else txt,
 "CodeGen:cannot find entrypoint:(txt)"
let entrypointsym = sym.t5 sub 1
let tobepatched = typ.conststype + toint.symboltableentry("list", conststype)
let discard0 = initwordref(baselibwords, bcwords)
let liblist =
 {baselib will be first in list and this library last}
 for
  acc = empty:seq.slot
  , w ∈ if isempty.uses then uses else [baselib] + toseq(asset.uses \ asset.[baselib])
 do acc + symboltableentry([merge("liblib _" + w)], function.[ptr.i64]),
 acc
 + modulerecord(
  [merge("liblib _" + libname)]
  , [toint.FUNCTIONDEC, typ.function.[ptr.i64], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
 )
let discard1 = initmap5.liblist
let defines = stepone(typedict, prgX, libname, isbase, initprofile)
let symboladdress = symboladdress(prgX, typedict, libname, defines)
let stacktraceinfo = extractValue((src.m) sub 1, "stacktrace")
assert n(stacktraceinfo >> 1) = 2 report "No stackTraceImp:((src.m) sub 1)"
let stacktracesymbol =
 symbol(moduleref(stacktraceinfo >> 1), stacktraceinfo << 2, seqof.typeword)
for bodies = empty:seq.internalbc, e ∈ defines
do
 bodies
 + addfuncdef(
  m
  , if kind.sym.e ∈ [kother, kcompoundname, kcat, kidx, kmakereal, kmember] then e
  else
   let internalbody =
    for acc2 = empty:seq.symbol, e9 ∈ arithseq(nopara.sym.e, 1, 1) do acc2 + Local.e9,
    acc2 + if name.sym.e ∈ "stacktrace" then stacktracesymbol else sym.e,
   symdef4(sym.e, internalbody, internalidx.sym.e, ThisLibrary + options.e)
 )
assert n.defines = n.bodies report "proBLEM?:(n.defines):(n.bodies)"
let f3a =
 if isbase then
  modulerecord(
   "initializewords"
   , [toint.FUNCTIONDEC, typ.function.[ptr.i64, i64], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  )
 else slot.0
let f4 =
 modulerecord(
  "entrypoint" + libname
  , [
   toint.FUNCTIONDEC
   , typ.tollvmtype(typedict, entrypointsym)
   , 0
   , 0
   , 0
   , 1
   , 0
   , 0
   , 0
   , 0
   , 0
   , 0
   , 0
   , 0
  ]
 )
let xxxx =
 {all other args to addliblib must be evaluated before this one}wordstoadd.baselibwords
let wordreps2 = wordreps2(if isbase then xxxx else empty:seq.encoding.word3)
let liblib =
 slot.addobject2("liblib" + libname, symboladdress + wordreps2 + symboladdress)
let bodytxts =
 [BLOCKCOUNT(1, 1) + RET(r.1, liblib)]
 + (if isbase then bodies + initializeWordsBody(typedict, prgX, baselib, liblist)
 else bodies)
 + entrypointbody(
  entrypointsym
  , typedict
  , prgX
  , libname
  , baselib
  , not.isempty.uses
  , fullname.bcwordFilename
  , initprofile
 )
let data = constdata
let showllvm = extractValue(options, "showllvm")
for showcontent = "", i = 1, e ∈ if isempty.showllvm then empty:seq.symdef else defines
do
 next(
  if name.sym.e ∉ showllvm then showcontent
  else showcontent + %.sym.e + %2(bodies sub i, nopara.sym.defines sub i)
  , i + 1
 )
let patchlist =
 [[toint.GLOBALVAR, typ.conststype, 2, toint.AGGREGATE.data + 1, 3, toint.align8 + 1, 0]]
let trec = typerecords
let adjust = [trec sub 1, [toint.ARRAY, n.data, 0]] + trec << 2
let bcdata = llvm(patchlist, bodytxts, adjust)
let cw = commonwords.xxxx,
[
 file(outname, bcdata)
 , file(filename."+:(dirpath.outname):(baselib).bcword", bytes.1 + bytes.n.cw + cw)
]
 + (if isempty.showcontent then empty:seq.file
else [file(filename."+:(dirpath.outname)showllvm.html", showcontent)])
 + if "info" sub 1 ∈ options then
 let extsymbols =
  for acc = empty:seq.word, sd ∈ defines
  do
   acc
   + (%.mangledname(prgX, sym.sd, libname)
   + %.sym.sd
   + "+/br
   "),
  acc,
 [file(filename."+:(dirpath.outname):(merge.[libname, "info" sub 1]).html", extsymbols)]
else empty:seq.file

function initializeWordsBody(
typedict:typedict
, prgX:set.symdef
, baselib:word
, liblist:seq.slot
) seq.internalbc
let typeseqofchar = seqof.typeref("char kernal" + baselib)
let addwords =
 symbol(
  moduleref([baselib] + "encoding", typeseqofchar)
  , "addencodings"
  , [seqof.typeseqofchar]
  , typeint
 )
assert not.isempty.getSymdef(prgX, addwords) report "No addencodings function"
let functyp2 = tollvmtype(typedict, addwords),
[
 BLOCKCOUNT(2, 1)
 + CALL(r.2, 0, 32768, function.[ptr.i64], last.liblist)
 + GEP(r.3, i64, r.2, C64.1)
 + LOAD(r.4, r.3, i64)
 + CAST(r.5, r.4, ptr.i64, inttoptr)
 + CALL(
  r.6
  , 0
  , 32768
  , functyp2
  , symboltableentry([mangledname(prgX, addwords, baselib)], functyp2)
  , r.1
  , r.5
 )
 + RETURN
]

function entrypointbody(
entrypointsym:symbol
, typedict:typedict
, prgX:set.symdef
, libname:word
, baselib:word
, bcwords:boolean
, bcwordFilename:word
, initprofile:seq.symbol
) seq.internalbc
[
 for acc = BLOCKCOUNT(1, 1), reg = 3, sym ∈ initprofile
 do
  if name.sym ∉ "initProfile" then next(acc, reg)
  else
   let functyp = tollvmtype(typedict, sym),
   next(
    acc
    + CALL(
     r.reg
     , 0
     , 32768
     , functyp
     , symboltableentry([mangledname(prgX, sym, libname)], functyp)
     , r.1
    )
    , reg + 1
   )
 let more =
  if not.bcwords then acc
  else
   let bcchars = decodeword.bcwordFilename
   let bcwordfilenameslot =
    nameslot(
     tocharseq([1, 0, 0, 0, 0, 0, 0, 0] + [n.bcchars, 0, 0, 0, 0, 0, 0, 0])
     + bcchars
    )
   let addbcwords2 =
    symbol(moduleref([baselib] + "llvmcode"), "addbcwords", [seqof.typebyte], typeint)
   assert not.isempty.getSymdef(prgX, addbcwords2) report "PROBLEM3",
   let functypA = tollvmtype(typedict, addbcwords2),
   acc
   + CAST(r.reg, CGEPi8(bcwordfilenameslot, 0), i64, ptrtoint)
   + CAST(r(reg + 1), r.reg, ptr.i64, inttoptr)
   + CALL(
    r(reg + 2)
    , 0
    , 32768
    , functypA
    , symboltableentry([mangledname(prgX, addbcwords2, libname)], functypA)
    , r.1
    , r(reg + 1)
   )
 let offset = if bcwords then reg + 3 else reg,
 let entryfunctyp = tollvmtype(typedict, entrypointsym),
 more
 + CALL(
  r.offset
  , 0
  , 32768
  , entryfunctyp
  , symboltableentry([mangledname(prgX, entrypointsym, libname)], entryfunctyp)
  , r.1
  , r.2
 )
 + RET(r(offset + 1), r.offset)
]

function topackedbyteobject(x:seq.byte) int
for acc = [toint.C64.1, toint.C64.n.x], acc2 = 0x0, shift = 0, b ∈ x
do
 let newacc2 = acc2 ∨ bits.toint.b << shift,
 if shift = 56 then next(acc + toint.C64.toint.newacc2, 0x0, 0)
 else next(acc, newacc2, shift + 8),
addobject(if shift > 0 then acc + toint.C64.toint.acc2 else acc)

function symboladdress(
prg:set.symdef
, typedict:typedict
, libname:word
, defines:seq.symdef
) seq.int
for addrsym = empty:seq.int, sd ∈ {toseq.prg}defines
do
 if isAbstract.module.sym.sd ∨ isconst.sym.sd ∨ kind.sym.sd = kglobal then addrsym
 else
  let f1 = sym.sd
  let functyp = ptr.tollvmtype(typedict, f1),
  let frefslot =
   ptrtoint(functyp, symboltableentry([mangledname(prg, f1, libname)], functyp)),
  addrsym + addobject([toint.frefslot] + addsymbol.f1),
[addobject([toint.C64.0, toint.C64.n.addrsym] + addrsym)]

function addfuncdef(m2:midpoint, sd:symdef) internalbc
let typedict = typedict.m2
assert not.isempty.code.sd report "codegen with no definition:(sym.sd)in:(library.module.sym.sd)"
let nopara = nopara.sym.sd
let paramap =
 for paramap = empty:seq.localmap, i ∈ arithseq(nopara, -1, nopara)
 do paramap + localmap(i, -i - 1),
 paramap
{lastLast is used for createthreadZ}
for
 lastLast = Lit.0
 , last = Lit.0
 , code = emptyinternalbc
 , lmap = paramap
 , noblocks = 1
 , regno = nopara + 1
 , argstk = empty:stack.int
 , blocks = empty:stack.Lcode
 , s ∈ code.sd
do
 let kind = kind.s,
 if kind = kint then next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.value.s), blocks)
 else if kind = kreal then next(last, s, code, lmap, noblocks, regno, push(argstk, toint.Creal.value.s), blocks)
 else if kind = ktrue then next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.1), blocks)
 else if kind = kfalse then next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.0), blocks)
 else if kind = klocal then next(last, s, code, lmap, noblocks, regno, push(argstk, getloc(lmap, value.s, 1)), blocks)
 else if kind = kdefine then
  let newmap = [localmap(value.s, top.argstk)] + lmap,
  next(last, s, code, newmap, noblocks, regno, pop(argstk, 1), blocks)
 else if kind = kbr then
  let condblk = push(blocks, Lcode(code, s, noblocks, regno + 1, argstk, blocks)),
  next(last, s, emptyinternalbc, lmap, noblocks + 1, regno + 1, empty:stack.int, condblk)
 else if kind = kexit then
  assert n.toseq.argstk > 0 report "fail 5e"
  let exitblock = push(blocks, Lcode(code, s, noblocks, regno, argstk, blocks)),
  next(last, s, emptyinternalbc, lmap, noblocks + 1, regno, empty:stack.int, exitblock)
 else if kind = kcontinue then
  let contblock = push(blocks, Lcode(code, s, noblocks, regno, argstk, blocks)),
  next(last, s, emptyinternalbc, lmap, noblocks + 1, regno, empty:stack.int, contblock)
 else if kind = kstart then
  let startblk =
   push(
    blocks
    , Lcode(code, s, noblocks, regno, push(argstk, typ.tollvmtype(typedict, resulttype.s)), blocks)
   ),
  next(last, s, emptyinternalbc, lmap, noblocks, regno, empty:stack.int, startblk)
 else if kind = klabel then
  let newstk = push(argstk, value.s),
  next(last, s, code, lmap, noblocks, regno, newstk, blocks)
 else if kind = kjmp then
  let jmpblock = push(blocks, Lcode(code, s, noblocks, regno, argstk, blocks)),
  next(last, s, emptyinternalbc, lmap, noblocks + 1, regno, empty:stack.int, jmpblock)
 else if kind = kjmpB then next(last, s, code, lmap, noblocks, regno, argstk, blocks)
 else if kind = kendblock then
  for no = 1, e ∈ reverse.toseq.blocks while kind.sym.e ∉ [kstart, kloop] do no + 1
  let blks = top(blocks, no)
  let firstblkargs = args.blks sub 1
  let newstack =
   if kind.sym.blks sub 1 = kstart then push(pop.firstblkargs, -(regno + 1))
   else
    let nopara2 = nopara.sym.blks sub 1,
    push(pop(firstblkargs, 2 * nopara2 + 1), -(regno + 1)),
  let newcode = processblk.blks,
  next(last, s, newcode, lmap, noblocks, regno + 1, newstack, pop(blocks, no))
 else if kind = kidxNB then
  let para = parameter.basetype((paratypes.s) sub 1, typedict)
  let tlist = idxNBtemplate.para
  let resultllvmtype = (llvmtypelist.last.templates.tlist) sub 1
  let startblk =
   push(blocks, Lcode(code, s, noblocks, regno, push(argstk, typ.resultllvmtype), blocks))
  let newcode = processIdxNB(startblk, tlist)
  let newregno = regno + regcount.tlist,
  let newstack = push(pop(argstk, 2), -newregno),
  next(last, s, newcode, lmap, noblocks + n.templates.tlist, newregno, newstack, blocks)
 else if kind ∈ [kconstantrecord, kword, kwords, kloop, ksequence, krecord, kfref] then
  let ee = findtemplate.s
  assert not.isempty.ee report
   "codegen errorA:no code template for:(s)in library"
   + library.module.s
   + "from"
   + %.sym.sd
  let m = ee sub 1,
  let action = action.m,
  if action = "ACTARG" sub 1 then next(last, s, code, lmap, noblocks, regno, push(argstk, arg.m), blocks)
  else if action = "TEMPLATE" sub 1 then
   let newcode = code + usetemplate(m, regno, toseq.argstk)
   let newstk = push(pop(argstk, arg.m), -(regno + length.m)),
   next(last, s, newcode, lmap, noblocks, regno + length.m, newstk, blocks)
  else if action = "LOOPBLOCK" sub 1 then
   let varcount = arg.m
   for bodymap = lmap, @e ∈ arithseq(varcount, 1, 1)
   do addloopmapentry(bodymap, firstvar.m, regno, @e)
   for pushexptypes = argstk, e ∈ llvmtypelist.m do push(pushexptypes, typ.e)
   {stack from top is kind(2), noexps, firstvar, exptypes, exps}
   let newblock = push(blocks, Lcode(code, s, noblocks, regno, pushexptypes, blocks)),
   let newcode = emptyinternalbc,
   next(last, s, newcode, bodymap, noblocks + 1, regno + varcount, empty:stack.int, newblock)
  else
   let fldbc =
    if action = "SEQUENCE" sub 1 then sequencecode(top(argstk, arg.m), (llvmtypelist.m) sub 1, regno, false)
    else
     assert action = "RECORD" sub 1 report "code gen unknown" + action,
     recordcode(top(argstk, arg.m), llvmtypelist.m, regno, false)
   let newstk = push(pop(argstk, arg.m), -(regno + 1)),
   next(last, s, code + bc.fldbc, lmap, noblocks, regno.fldbc, newstk, blocks)
 else if kind.s = kcreatethreadZ then
  let types2 =
   tollvmtypelist(
    typedict
    , basesym(
     if kind.lastLast = kfref then lastLast
     else
      let tmp = getCode(prg.m2, last),
      tmp sub (n.tmp - 1)
    )
   )
  let typelist = types2 << 2 + types2 sub 1,
  let newcode =
   code
   + CALLSTART(
    regno + 1
    , 0
    , 32768
    , typ.function.[ptr.i64, i64, ptr.i64, i64]
    , toint.symboltableentry("createthread", function.[ptr.i64, i64, ptr.i64, i64])
    , 3
   )
   + CALLFINISH(regno + 1, [-1] + top.argstk + toint.C64.buildargcode.typelist),
  next(last, s, newcode, lmap, noblocks, regno + 1, push(pop.argstk, -(regno + 1)), blocks)
 else
  let ee = findtemplate.s
  assert not.isempty.ee report
   "codegen error:no code template for:(s)in library"
   + library.module.s
   + "from"
   + %.sym.sd
  let m = ee sub 1,
  let action = action.m,
  if action = "CALL" sub 1 then
   let noargs = arg.m
   let args = top(argstk, noargs)
   let newcode =
    code + usetemplate(m, regno, empty:seq.int) + CALLFINISH(regno + 1, [-1] + args),
   let newstk = push(pop(argstk, noargs), -(regno + 1)),
   next(last, s, newcode, lmap, noblocks, regno + 1, newstk, blocks)
  else if action = "TEMPLATE" sub 1 then
   if length.m = 0 then next(last, s, code, lmap, noblocks, regno, argstk, blocks)
   else
    let newcode = code + usetemplate(m, regno, toseq.argstk)
    let newstk = push(pop(argstk, arg.m), -(regno + length.m)),
    next(last, s, newcode, lmap, noblocks, regno + length.m, newstk, blocks)
  else
   assert action = "SET" sub 1 report "code gen unknown" + action,
   next(last, s, code, lmap, noblocks, regno, argstk, blocks),
BLOCKCOUNT(1, noblocks) + code + RET(r(regno + 1), slot.top.argstk)

function processIdxNB(blocks:stack.Lcode, IdxTemplate:idxNBtemplate) internalbc
let tlist = templates.IdxTemplate
let firstblk = top.blocks
let args = pop.args.firstblk
for regX = regno.firstblk, noblks = noblocks.firstblk, blks = blocks, m ∈ tlist
do
 let newreg = regX + length.m
 let templateargs = if arg.m = 1 then pop.args else args,
 let newcode = usetemplate(m, regX, toseq.templateargs),
 if arg.m = 1 then
  let cond =
   Lcode(newcode, Br2(1, 2), noblks, newreg + 1, push(empty:stack.int, -newreg), blks),
  next(newreg + 1, noblks + 1, push(blks, cond))
 else
  let exitblock =
   Lcode(newcode, Exit, noblks, newreg, push(empty:stack.int, -newreg), blks),
  next(newreg, noblks + 1, push(blks, exitblock))
assert regX - regno.firstblk + 1 ∈ {[11, 12, 24, 19])}[regcount.IdxTemplate, 19] report "KJL:(para.IdxTemplate):(regX - regno.firstblk + 1)",
processblk.top(blks, n.tlist + 1)

type Lcode is
code:internalbc
, sym:symbol
, noblocks:int
, regno:int
, args:stack.int
, blocks:stack.Lcode

type localmap is localno:int, regno:int

function buildargcode(l:seq.llvmtype) int
{needed because the call interface implementation for reals is different than other types is some implementations}
for acc = 1, typ ∈ l do acc * 2 + if typ.typ = typ.double then 1 else 0,
acc

function processblk(blks:seq.Lcode) internalbc
let exitbr = BR.noblocks.last.blks
let firstblk = blks sub 1
let isloopblock = kind.sym.firstblk = kloop
for
 i = 1
 , code = emptyinternalbc
 , phi = empty:seq.int
 , tailphi = empty:seq.int
 , l ∈ blks << 1
do
 let kind = kind.sym.l,
 if kind = kexit then
  assert n.toseq.args.l ≥ 1 report "check l",
  next(i + 1, code + code.l + exitbr, phi + [noblocks.l - 1] + top.args.l, tailphi)
 else if kind = kcontinue then
  assert isloopblock report "incorrect format on block"
  let noargs = nopara.sym.l
  let newtailphi = tailphi + [noblocks.l - 1] + top(args.l, noargs),
  let newcode = BR.noblocks.firstblk,
  next(i + 1, code + code.l + newcode, phi, newtailphi)
 else if kind = kjmp then
  let args = top(args.l, value.sym.l - 2)
  let defaultBlk = noblocks.blks sub (i + last.args)
  for switchArgs = empty:seq.int, arg ∈ args >> 1
  do
   switchArgs
   + (if n.switchArgs mod 2 = 0 then {toint.C64.}arg
   else noblocks.blks sub (i + arg))
  let stk11 = pop(args.l, n.args),
  let new =
   SWITCH(r(regno.blks sub (i + 1) + 1), i64, slot.top.stk11, defaultBlk, switchArgs),
  next(i + 1, code + code.l + new, phi, tailphi)
 else
  {br block}
  assert kind = kbr report "expecting br block:(sym.l)Y:(n.blks)/br:(toseq.args.l)"
  let brt = brt.sym.l
  let brf = brf.sym.l
  assert between(i + brt, 1, n.blks) ∧ between(i + brf, 1, n.blks) report "codegen error:jmp to unknown block",
  let newcode =
   CAST(r.regno.l, slot.top.args.l, i1, trunc)
   + BR(r(regno.l + 1), noblocks.blks sub (i + brt), noblocks.blks sub (i + brf), r.regno.l),
  next(i + 1, code + code.l + newcode, phi, tailphi),
code.firstblk
 + if isloopblock then
 let noargs = nopara.sym.firstblk
 {stack from top is kind, noexps, firstvar, exptypes, exps}
 let rt = undertop(args.firstblk, noargs),
 let prefix = [noblocks.firstblk - 1] + top(pop(args.firstblk, 1 + noargs), noargs),
 BR.noblocks.firstblk
 + phiinst(regno.firstblk, top(args.firstblk, noargs), prefix + tailphi, noargs)
 + code
 + phiinst(regno.last.blks, [rt], phi, 1)
else code + phiinst(regno.last.blks, [top.args.firstblk], phi, 1)

function Switch(blks:seq.Lcode, begin:int, end:int) internalbc
{adding Switch only gave very slight improvement in performance}
let defaultBlk = noblocks.blks sub (end + brf.sym.blks sub end - 1)
let startBlk = blks sub begin
let startargs = top(args.startBlk, 2)
for i2 = begin, switchArgs = empty:seq.int, l ∈ subseq(blks, begin, end)
do next(i2 + 1, switchArgs + [top.args.l, noblocks.blks sub (i2 + brt.sym.l - 1)])
let new =
 SWITCH(r(regno.startBlk + 1), i64, slot.startargs sub 1, defaultBlk, switchArgs)
for code = code.startBlk + new, l ∈ subseq(blks, begin + 1, end)
do code + code.l + BR.defaultBlk,
code

function getloc(l:seq.localmap, localno:int, i:int) int
if localno.l sub i = localno then regno.l sub i else getloc(l, localno, i + 1)

function addloopmapentry(l:seq.localmap, baselocal:int, regbase:int, i:int) seq.localmap
[localmap(baselocal + i - 1, -regbase - i)] + l 