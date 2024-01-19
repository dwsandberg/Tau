Module codegen

use otherseq.Lcode

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

use otherseq.int

use seq.int

use seq.seq.int

use stack.int

use internalbc

use seq.internalbc

use llvm

use llvmcode

use otherseq.llvmtype

use seq.llvmtype

use otherseq.localmap

use seq.localmap

use seq.match5

use mytype

use seq.mytype

use persistant

use seq.slot

use standard

use symbol

use otherseq.symbol

use set.symbol

use symbol2

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
{OPTION PROFILE}
let libname = libname.m
let baselib = 1#extractValue(1#src.m, "baselib")
let initprofile =
 for acc = empty:seq.symbol, x ∈ libmods.m
 do if name.modname.x ∈ "initialize" then acc + exports.x else acc,
 toseq.asset.acc
let bcwordFilename = filename."+^(dirpath.outname)^(baselib).bcword"
let baselibwords = if isempty.uses then empty:seq.seq.char else basewords
let bcwords = if isempty.uses then empty:seq.char else getbcwords.bcwordFilename
let typedict = typedict.m
let isbase = isempty.uses
let prgX = prg.m
let t5a =
 getSymdef(
  prgX
  , symbol(
   moduleref.[libname, 1#"entrypoint"]
   , "entrypoint"
   , typeref."UTF8 UTF8 *"
   , typeref."UTF8 UTF8 *"
  )
 )
let t5 =
 if not.isempty.t5a then t5a
 else
  getSymdef(
   prgX
   , symbol(
    moduleref.[libname, merge.[libname, 1#"$EP"]]
    , "entrypoint"
    , typeref."UTF8 UTF8 *"
    , typeref."UTF8 UTF8 *"
   )
  )
assert not.isempty.t5 report
 for txt = "", p ∈ toseq.prgX
 do if name.sym.p ∈ "entrypoint" then txt + %.sym.p else txt,
 "CodeGen:cannot find entrypoint^(txt)"
let entrypointsym = sym.1#t5
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
let stacktraceinfo = extractValue(1#src.m, "stacktrace")
assert n(stacktraceinfo >> 1) = 2 report "No stackTraceImp^(1#src.m)"
let stacktracesymbol = symbol(moduleref(stacktraceinfo >> 1), stacktraceinfo << 2, seqof.typeword)
let bodies =
 for acc = empty:seq.internalbc, @e ∈ defines
 do
  acc
   + addfuncdef(
   m
   , if isInternal.sym.@e then
    let internalbody =
     for acc2 = empty:seq.symbol, e9 ∈ arithseq(nopara.sym.@e, 1, 1)
     do acc2 + Local.e9,
     acc2 + if name.sym.@e ∈ "stacktrace" then stacktracesymbol else sym.@e,
    symdef4(sym.@e, internalbody, internalidx.sym.@e, "ThisLibrary^(getOptions.@e)")
   else @e
  ),
 acc
assert n.defines = n.bodies report "proBLEM?^(n.defines)^(n.bodies)"
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
let xxxx = {all other args to addliblib must be evaluated before this one} wordstoadd.baselibwords
let wordreps2 = wordreps2(if isbase then xxxx else empty:seq.encoding.word3)
let liblib = slot.addobject2("liblib" + libname, symboladdress + wordreps2 + symboladdress)
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
  else showcontent + %.sym.e + %2(i#bodies, nopara.sym.i#defines)
  , i + 1
 )
let patchlist = [[toint.GLOBALVAR, typ.conststype, 2, toint.AGGREGATE.data + 1, 3, toint.align8 + 1, 0]]
let trec = typerecords
let adjust = [1#trec, [toint.ARRAY, n.data, 0]] + trec << 2
let bcdata = llvm(patchlist, bodytxts, adjust)
let cw = commonwords.xxxx,
[
 file(outname, bcdata)
 , file(filename."+^(dirpath.outname)^(baselib).bcword", bytes.1 + bytes.n.cw + cw)
]
 + (if isempty.showcontent then empty:seq.file
else [file(filename."+^(dirpath.outname) showllvm.html", showcontent)])
 + if 1#"info" ∈ options then
 let extsymbols =
  for acc = empty:seq.word, sd ∈ defines
  do
   acc
    + (%.mangledname(prgX, sym.sd, libname)
    + %.sym.sd
    + "+
   /br"),
  acc,
 [file(filename."+^(dirpath.outname)^(merge.[libname, 1#"info"]).html", extsymbols)]
else empty:seq.file

function initializeWordsBody(
typedict:typedict
, prgX:set.symdef
, baselib:word
, liblist:seq.slot
) seq.internalbc
let typeseqofchar = seqof.typeref("char standard" + baselib)
let addwords =
 symbol(
  moduleref([baselib] + "encoding", typeseqofchar)
  , "addencodings"
  , seqof.typeseqofchar
  , typeint
 )
assert not.isempty.getSymdef(prgX, addwords) report "No addencodings function"
let functyp2 = tollvmtype(typedict, addwords),
[
 BLOCKCOUNT(2, 1)
  + CALL(r.2, 0, 32768, function.[ptr.i64], 1^liblist)
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
   let bcwordfilenameslot = nameslot(tocharseq([1, 0, 0, 0, 0, 0, 0, 0] + [n.bcchars, 0, 0, 0, 0, 0, 0, 0]) + bcchars)
   let addbcwords2 = symbol(moduleref([baselib] + "llvmcode"), "addbcwords", seqof.typebyte, typeint)
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
for addrsym = empty:seq.int, sd ∈ {toseq.prg} defines
do
 if isAbstract.module.sym.sd ∨ isconst.sym.sd ∨ isBuiltin.sym.sd ∨ isGlobal.sym.sd then addrsym
 else
  let f1 = sym.sd
  let functyp = ptr.tollvmtype(typedict, f1),
  let frefslot = ptrtoint(functyp, symboltableentry([mangledname(prg, f1, libname)], functyp)),
  addrsym + addobject([toint.frefslot] + addsymbol.f1),
[addobject([toint.C64.0, toint.C64.n.addrsym] + addrsym)]

function addfuncdef(m2:midpoint, sd:symdef) internalbc
let typedict = typedict.m2
assert not.isempty.code.sd report "codegen with no definition^(sym.sd) in" + library.module.sym.sd
let nopara = nopara.sym.sd
let paramap =
 for paramap = empty:seq.localmap, i ∈ arithseq(nopara,-1, nopara)
 do paramap + localmap(i,-i - 1),
 paramap
for
 lastLast = Lit.0
 , last = Lit.0
 , code = emptyinternalbc
 , lmap = paramap
 , noblocks = 1
 , regno = nopara + 1
 , argstk = empty:stack.int
 , blocks = empty:stack.Lcode
 , s ∈ {removeJump.} code.sd
do
 if isconst.s ∧ not(isword.s ∨ iswords.s ∨ isrecordconstant.s ∨ isFref.s) then
  if isIntLit.s then next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.value.s), blocks)
  else if isRealLit.s then next(last, s, code, lmap, noblocks, regno, push(argstk, toint.Creal.value.s), blocks)
  else if s = Littrue then next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.1), blocks)
  else
   assert s = Litfalse report "gencode error5",
   next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.0), blocks)
 else if isspecial.s ∧ not(isloopblock.s ∨ isRecord.s ∨ isSequence.s) then
  if islocal.s then next(last, s, code, lmap, noblocks, regno, push(argstk, getloc(lmap, value.s, 1)), blocks)
  else if isdefine.s then
   next(
    last
    , s
    , code
    , [localmap(value.s, top.argstk)] + lmap
    , noblocks
    , regno
    , pop(argstk, 1)
    , blocks
   )
  else if isbr.s then
   let cond =
    if last = JumpOp then Lcode(code, s, noblocks, regno, argstk, blocks)
    else
     let newcode = CAST(r(regno + 1), slot.top.argstk, i1, trunc),
     Lcode(code, s, noblocks, regno + 1, argstk, blocks),
   next(
    last
    , s
    , emptyinternalbc
    , lmap
    , noblocks + 1
    , if last = JumpOp ∨ isIntLit.last then regno else regno + 1
    , empty:stack.int
    , push(blocks, cond)
   )
  else if isExit.s then
   assert n.toseq.argstk > 0 report "fail 5e"
   let exitblock = Lcode(code, s, noblocks, regno, argstk, blocks),
   next(
    last
    , s
    , emptyinternalbc
    , lmap
    , noblocks + 1
    , regno
    , empty:stack.int
    , push(blocks, exitblock)
   )
  else if iscontinue.s then
   let exitblock = Lcode(code, s, noblocks, regno, argstk, blocks),
   next(
    last
    , s
    , emptyinternalbc
    , lmap
    , noblocks + 1
    , regno
    , empty:stack.int
    , push(blocks, exitblock)
   )
  else if isstart.s then
   let exitblock = Lcode(code, s, noblocks, regno, push(argstk, typ.tollvmtype(typedict, resulttype.s)), blocks),
   next(
    last
    , s
    , emptyinternalbc
    , lmap
    , noblocks
    , regno
    , empty:stack.int
    , push(blocks, exitblock)
   )
  else
   assert isblock.s report "codegen: Expecting block"
   let no =
    for nodecount = 1, e ∈ reverse.toseq.blocks
    while not(isstart.sym.e ∨ isloopblock.sym.e)
    do nodecount + 1,
    nodecount
   let blks = top(blocks, no)
   assert n.blks = no report "XXXXXX arg"
   let rblk = processblk(blks, BR(noblocks - 1)),
   let firstblkargs = args.1#blks,
   if isstart.sym.1#blks then
    let newstack = push(pop.firstblkargs,-(regno + 1))
    let newcode = code.rblk + phiinst(regno.1^blks, [top.firstblkargs], phi.rblk, 1),
    next(last, s, newcode, lmap, noblocks, regno + 1, newstack, pop(blocks, no))
   else
    assert isloopblock.sym.1#blks report "Code Gen--not expecting first blk kind"
    let nopara2 = nopara.sym.1#blks
    {stack from top is kind, noexps, firstvar, exptypes, exps}
    let rt = undertop(firstblkargs, nopara2)
    let newstack = push(pop(firstblkargs, 2 * nopara2 + 1),-(regno + 1)),
    let newcode = code.rblk + phiinst(regno.1^blks, [rt], phi.rblk, 1),
    next(last, s, newcode, lmap, noblocks, regno + 1, newstack, pop(blocks, no))
 else if isBuiltin.s ∧ wordname.s ∈ "createthreadZ" then
  let types2 =
   tollvmtypelist(
    typedict
    , basesym(
     if isFref.lastLast then lastLast
     else
      let tmp = getCode(prg.m2, last),
      (n.tmp - 1)#tmp
    )
   )
  let typelist = types2 << 2 + 1#types2,
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
  next(last, s, newcode, lmap, noblocks, regno + 1, push(pop.argstk,-(regno + 1)), blocks)
 else if s = JumpOp then next(last, s, code, lmap, noblocks, regno, argstk, blocks)
 else
  let ee = findtemplate.s
  assert not.isempty.ee report
   "codegen error:no code template for^(s) in library"
    + library.module.s
    + "from"
    + %.sym.sd
  let m = 1#ee,
  let action = action.m,
  if action = 1#"CALL" then
   let noargs = arg.m
   let args = top(argstk, noargs),
   let c = usetemplate(m, regno, empty:seq.int) + CALLFINISH(regno + 1, [-1] + args),
   next(
    last
    , s
    , code + c
    , lmap
    , noblocks
    , regno + 1
    , push(pop(argstk, noargs),-(regno + 1))
    , blocks
   )
  else if action = 1#"ACTARG" then next(last, s, code, lmap, noblocks, regno, push(argstk, arg.m), blocks)
  else if action = 1#"TEMPLATE" then
   if length.m = 0 then next(last, s, code, lmap, noblocks, regno, argstk, blocks)
   else
    let newcode = usetemplate(m, regno, toseq.argstk)
    let noargs = arg.m,
    next(
     last
     , s
     , code + newcode
     , lmap
     , noblocks
     , regno + length.m
     , push(pop(argstk, noargs),-(regno + length.m))
     , blocks
    )
  else if action = 1#"SET" then next(last, s, code, lmap, noblocks, regno, argstk, blocks)
  else if action = 1#"LOOPBLOCK" then
   let varcount = arg.m
   let bodymap =
    for acc = lmap, @e ∈ arithseq(varcount, 1, 1)
    do addloopmapentry(acc, firstvar.m, regno, @e),
    acc
   for pushexptypes = argstk, e ∈ llvmtypelist.m
   do push(pushexptypes, typ.e)
   {stack from top is kind (2), noexps, firstvar, exptypes, exps}
   let exitblock = Lcode(code, s, noblocks, regno, pushexptypes, blocks),
   next(
    last
    , s
    , emptyinternalbc
    , bodymap
    , noblocks + 1
    , regno + varcount
    , empty:stack.int
    , push(blocks, exitblock)
   )
  else if action = 1#"SEQUENCE" then
   let fldbc = sequencecode(top(argstk, arg.m), 1#llvmtypelist.m, regno, false),
   next(
    last
    , s
    , code + bc.fldbc
    , lmap
    , noblocks
    , regno.fldbc
    , push(pop(argstk, arg.m),-(regno + 1))
    , blocks
   )
  else
   assert action = 1#"RECORD" report "code gen unknown" + action
   let fldbc = recordcode(top(argstk, arg.m), llvmtypelist.m, regno, false),
   next(
    last
    , s
    , code + bc.fldbc
    , lmap
    , noblocks
    , regno.fldbc
    , push(pop(argstk, arg.m),-(regno + 1))
    , blocks
   ),
BLOCKCOUNT(1, noblocks) + code + RET(r(regno + 1), slot.top.argstk)

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

type processblkresult is code:internalbc, phi:seq.int

function processblk(blks:seq.Lcode, exitbr:internalbc) processblkresult
for
 i = 1
 , code = emptyinternalbc
 , phi = empty:seq.int
 , tailphi = empty:seq.int
 , beginrun = 0
 , l ∈ blks
do
 assert n.toseq.args.l > 0 report "XXXXXX" + toword.n.blks + toword.i,
 if isExit.sym.l then
  assert n.toseq.args.l ≥ 1 report "check l",
  next(i + 1, code + code.l + exitbr, phi + [noblocks.l - 1] + top.args.l, tailphi, beginrun)
 else if isloopblock.sym.l then
  let noargs = nopara.sym.l
  let newtailphi = [noblocks.l - 1] + top(pop(args.l, 1 + noargs), noargs),
  next(i + 1, code, phi, newtailphi, beginrun)
 else if iscontinue.sym.l then
  assert isloopblock.sym.1#blks report "incorrect format on block"
  let noargs = nopara.sym.l
  let newtailphi = tailphi + [noblocks.l - 1] + top(args.l, noargs),
  let newcode = BR.noblocks.1#blks,
  next(i + 1, code + code.l + newcode, phi, newtailphi, beginrun)
 else if isstart.sym.l then next(i + 1, code + code.l, phi, tailphi, beginrun)
 else
  {br block}
  assert isbr.sym.l report "expecting br block^(sym.l)"
  let brt = brt.sym.l - 1
  let brf = brf.sym.l - 1,
  assert between(i + brt, 1, n.blks) ∧ between(i + brf, 1, n.blks) report "codegen error:jmp to unknown block",
  if n.toseq.args.l = 2 then {JumpOp} next(i + 1, code, phi, tailphi, i)
  else if beginrun > 0 then
   let endrun =
    if brf > 0 then true
    else
     let nextBlk = (i + 1)#blks,
     not.isbr.sym.nextBlk
     ∨ {a standard br2} top.args.nextBlk < 0
     ∨ {start another run} n.toseq.args.nextBlk = 2,
   if endrun then next(i + 1, code + Switch(blks, beginrun, i), phi, tailphi, 0)
   else next(i + 1, code, phi, tailphi, beginrun)
  else
   let newcode =
    CAST(r.regno.l, slot.top.args.l, i1, trunc)
     + BR(r(regno.l + 1), abs.noblocks.(i + brt)#blks, abs.noblocks.(i + brf)#blks, r.regno.l),
   next(i + 1, code + code.l + newcode, phi, tailphi, beginrun)
let firstblk = 1#blks
let code1 =
 if isloopblock.sym.firstblk then
  let noargs = nopara.sym.firstblk,
  code.firstblk
   + BR.noblocks.firstblk
   + phiinst(regno.firstblk, top(args.firstblk, noargs), tailphi, noargs)
   + code
 else code,
processblkresult(code1, phi)

function Switch(blks:seq.Lcode, begin:int, end:int) internalbc
{adding Switch only gave very slight improvement in performance}
let defaultBlk = noblocks.(end + brf.sym.end#blks - 1)#blks
let startBlk = begin#blks
let startargs = top(args.startBlk, 2)
for i2 = begin, switchArgs = empty:seq.int, l ∈ subseq(blks, begin, end)
do next(i2 + 1, switchArgs + [top.args.l, noblocks.(i2 + brt.sym.l - 1)#blks])
let new = SWITCH(r(regno.startBlk + 1), i64, slot.1#startargs, defaultBlk, switchArgs)
for code = code.startBlk + new, l ∈ subseq(blks, begin + 1, end)
do code + code.l + BR.defaultBlk,
code

function getloc(l:seq.localmap, localno:int, i:int) int
if localno.i#l = localno then regno.i#l else getloc(l, localno, i + 1)

function addloopmapentry(l:seq.localmap, baselocal:int, regbase:int, i:int) seq.localmap
[localmap(baselocal + i - 1,-regbase - i)] + l 