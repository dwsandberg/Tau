Module codegennew

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

use seq.int

use seq.seq.int

use stack.int

use internalbc

use seq.internalbc

use llvm

use llvmcode

use llvmconstants

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
let libnametype = array(length.b + 1, i8),
modulerecord(""
 , [toint.GLOBALVAR
  , typ.libnametype
  , 2
  , toint.DATA(libnametype, tointseq.b + 0) + 1
  , 3
  , toint.align8
  , 0]
 )

builtin basewords seq.seq.char

Function compilerback(m:midpoint, outname:filename, options:seq.word) seq.file
{OPTION XPROFILE}
let uses = extractValue(first.src.m, "uses")
let libname = first.extractValue(first.src.m, "Library")
let baselib = first.extractValue(first.src.m, "baselib")
let initprofile = 
 for acc = empty:seq.symbol, x ∈ libmods.m do
  if name.modname.x ∈ "initialize" then acc + exports.x else acc
 /do toseq.asset.acc
{assert libname /nin" common" report" SDF"+libname+%.initprofile}
let bcwordFilename = filename."+$(dirpath.outname + baselib).bcword"
let baselibwords = if isempty.uses then empty:seq.seq.char else basewords
let bcwords = if isempty.uses then empty:seq.char else getbcwords.bcwordFilename
let typedict = typedict.m
let isbase = isempty.uses
let prgX = prg.m
let t5a=getSymdef(prgX
  , symbol(moduleref.[libname, "entrypoint"_1]
   , "entrypoint"
   , typeref."UTF8 UTF8 *"
   , typeref."UTF8 UTF8 *")
  )
let t5 = if not.isempty.t5a then t5a else 
 getSymdef(prgX
  , symbol(moduleref.[libname, merge.[libname, "$EP"_1]]
   , "entrypoint"
   , typeref."UTF8 UTF8 *"
   , typeref."UTF8 UTF8 *")
  )
assert not.isempty.t5 report "CodeGen:cannot find entrypoint"
+for  txt="", p /in toseq.prgX do if name.sym.p /in "entrypoint" then 
 txt+%.sym.p else txt /do txt
let entrypointsym = sym.t5_1
let tobepatched = typ.conststype + toint.symboltableentry("list", conststype)
let discard0 = initwordref(baselibwords, bcwords)
let liblist = 
 {baselib will be first in list and this library last}
 for acc = empty:seq.slot
  , w ∈ if isempty.uses then uses else [baselib] + toseq(asset.uses \ asset.[baselib])
 do
  acc + symboltableentry([merge("liblib_" + w)], function.[ptr.i64])
 /do
  acc
  + modulerecord([merge("liblib_" + libname)]
   , [toint.FUNCTIONDEC, typ.function.[ptr.i64], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])
let discard1 = initmap5.liblist
let defines = stepone(typedict, prgX, libname, isbase, initprofile)
let symboladdress = symboladdress(prgX, typedict, libname, defines)
let stacktraceinfo = extractValue(first.src.m, "stacktrace")
assert length(stacktraceinfo >> 1) = 2 report "No stackTraceImp $(first.src.m)"
let stacktracesymbol = symbol(moduleref(stacktraceinfo >> 1), stacktraceinfo << 2, seqof.typeword)
let bodies = 
 for acc = empty:seq.internalbc, @e ∈ defines do
  acc
  + addfuncdef(m
   , if isInternal.sym.@e then
    let internalbody = 
     for acc2 = empty:seq.symbol, e9 ∈ arithseq(nopara.sym.@e, 1, 1) do
      acc2 + Local.e9
     /do acc2 + if name.sym.@e ∈ "stacktrace" then stacktracesymbol else sym.@e
    ,
    symdef4(sym.@e, internalbody, internalidx.sym.@e, "ThisLibrary $(getOptions.@e)")
   else
    @e
   )
 /do acc
assert length.defines = length.bodies report "proBLEM? $(length.defines) $(length.bodies)"
let f3a = 
 if isbase then
  modulerecord("initializewords"
   , [toint.FUNCTIONDEC
    , typ.function.[ptr.i64, i64]
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
    , 0]
   )
 else
  slot.0
let f4 = 
 modulerecord("entrypoint" + libname
  , [toint.FUNCTIONDEC
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
   , 0]
  )
let xxxx = {all other args to addliblib must be evaluated before this one} wordstoadd.baselibwords
let wordreps2 = wordreps2.if isbase then xxxx else empty:seq.encoding.word3
let liblib = slot.addobject2("liblib" + libname, symboladdress + wordreps2 + symboladdress)
let bodytxts = 
 [BLOCKCOUNT(1, 1) + RET(r.1, liblib)]
 + if isbase then bodies + initializeWordsBody(typedict, prgX, baselib, liblist) else bodies /if
 + entrypointbody(entrypointsym
  , typedict
  , prgX
  , libname
  , baselib
  , not.isempty.uses
  , fullname.bcwordFilename
  , initprofile)
let data = constdata
let patchlist = 
 [
  [toint.GLOBALVAR
   , typ.conststype
   , 2
   , toint.AGGREGATE.data + 1
   , 3
   , toint.align8 + 1
   , 0]
  ]
let trec = typerecords
let adjust = [trec_1, [toint.ARRAY, length.data, 0]] + subseq(trec, 3, length.trec)
let bcdata = llvm(patchlist, bodytxts, adjust)
let cw = commonwords.xxxx,
[file(outname, bcdata)
 , file(filename."+$(dirpath.outname + baselib).bcword", bytes.1 + bytes.length.cw + cw)]
+ if "info"_1 ∈ options then
 let extsymbols = 
  for acc = empty:seq.word, sd ∈ defines do
   acc + "$(mangledname(prgX, sym.sd, libname)) $(sym.sd)+/br"
  /do acc
 ,
 [file(filename."+$(dirpath.outname + merge.[libname, "info"_1]).html", extsymbols)]
else
 empty:seq.file

function initializeWordsBody(typedict:typedict, prgX:set.symdef, baselib:word, liblist:seq.slot) seq.internalbc
let typeseqofchar = seqof.typeref("char standard" + baselib)
let addwords = 
 symbol(moduleref([baselib] + "encoding", typeseqofchar)
  , "addencodings"
  , seqof.typeseqofchar
  , typeint)
assert not.isempty.getSymdef(prgX, addwords) report "No addencodings function"
let functyp2 = tollvmtype(typedict, addwords),
[
 BLOCKCOUNT(2, 1) + CALL(r.2, 0, 32768, function.[ptr.i64], last.liblist)
 + GEP(r.3, i64, r.2, C64.1)
 + LOAD(r.4, r.3, i64)
 + CAST(r.5, r.4, ptr.i64, inttoptr)
 + CALL(r.6
  , 0
  , 32768
  , functyp2
  , symboltableentry([mangledname(prgX, addwords, baselib)], functyp2)
  , r.1
  , r.5)
 + RETURN]

function entrypointbody(entrypointsym:symbol
 , typedict:typedict
 , prgX:set.symdef
 , libname:word
 , baselib:word
 , bcwords:boolean
 , bcwordFilename:word
 , initprofile:seq.symbol) seq.internalbc
[
 for acc = BLOCKCOUNT(1, 1), reg = 3, sym ∈ initprofile do
  if name.sym ∉ "initProfile" then
   next(acc, reg)
  else
   let functyp = tollvmtype(typedict, sym),
   next(
    acc
    + CALL(r.reg
     , 0
     , 32768
     , functyp
     , symboltableentry([mangledname(prgX, sym, libname)], functyp)
     , r.1)
    , reg + 1)
 /do
  let more = 
   if not.bcwords then
    acc
   else
    let bcchars = decodeword.bcwordFilename
    let bcwordfilenameslot = 
     nameslot(tocharseq([1, 0, 0, 0, 0, 0, 0, 0] + [length.bcchars, 0, 0, 0, 0, 0, 0, 0]) + bcchars)
    let addbcwords2 = symbol(moduleref([baselib] + "llvmcode"), "addbcwords", seqof.typebyte, typeint)
    assert not.isempty.getSymdef(prgX, addbcwords2) report "PROBLEM3"
    let functypA = tollvmtype(typedict, addbcwords2),
    acc + CAST(r.reg, CGEPi8(bcwordfilenameslot, 0), i64, ptrtoint)
    + CAST(r(reg + 1), r.reg, ptr.i64, inttoptr)
    + CALL(r(reg + 2)
     , 0
     , 32768
     , functypA
     , symboltableentry([mangledname(prgX, addbcwords2, libname)], functypA)
     , r.1
     , r(reg + 1))
  let offset = if bcwords then reg + 3 else reg
  let entryfunctyp = tollvmtype(typedict, entrypointsym),
  more
  + CALL(r.offset
   , 0
   , 32768
   , entryfunctyp
   , symboltableentry([mangledname(prgX, entrypointsym, libname)], entryfunctyp)
   , r.1
   , r.2)
  + RET(r(offset + 1), r(offset + 2))
 ]

function topackedbyteobject(x:seq.byte) int
for acc = [toint.C64.1, toint.C64.length.x], acc2 = 0x0, shift = 0, b ∈ x do
 let newacc2 = acc2 ∨ bits.toint.b << shift,
 if shift = 56 then
  next(acc + toint.C64.toint.newacc2, 0x0, 0)
 else
  next(acc, newacc2, shift + 8)
/do addobject.if shift > 0 then acc + toint.C64.toint.acc2 else acc

function symboladdress(prg:set.symdef, typedict:typedict, libname:word, defines:seq.symdef) seq.int
for addrsym = empty:seq.int, sd ∈ {toseq.prg} defines do
 if isAbstract.module.sym.sd ∨ isconst.sym.sd ∨ isBuiltin.sym.sd ∨ isGlobal.sym.sd then
  addrsym
 else
  let f1 = sym.sd
  let functyp = ptr.tollvmtype(typedict, f1)
  let frefslot = ptrtoint(functyp, symboltableentry([mangledname(prg, f1, libname)], functyp)),
  addrsym + addobject([toint.frefslot] + addsymbol.f1)
/do [addobject([toint.C64.0, toint.C64.length.addrsym] + addrsym)]

function addfuncdef(m2:midpoint, sd:symdef) internalbc
let typedict = typedict.m2
assert not.isempty.code.sd report "codegen with no definition $(sym.sd) in" + library.module.sym.sd
let nopara = nopara.sym.sd
let paramap = 
 for paramap = empty:seq.localmap, i ∈ arithseq(nopara,-1, nopara) do
  paramap + localmap(i,-i - 1)
 /do paramap
,
for lastfref = Lit.0
 , last = Lit.0
 , code = emptyinternalbc
 , lmap = paramap
 , noblocks = 1
 , regno = nopara + 1
 , argstk = empty:stack.int
 , blocks = empty:stack.Lcode
 , s ∈ code.sd
do
 if isconst.s ∧ not(isword.s ∨ iswords.s ∨ isrecordconstant.s ∨ isFref.s) then
  if isIntLit.s then
   next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.value.s), blocks)
  else if isRealLit.s then
   next(last, s, code, lmap, noblocks, regno, push(argstk, toint.Creal.value.s), blocks)
  else if s = Littrue then
   next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.1), blocks)
  else
   assert s = Litfalse report "gencode error5",
   next(last, s, code, lmap, noblocks, regno, push(argstk, toint.C64.0), blocks)
 else if isspecial.s ∧ not(isloopblock.s ∨ isRecord.s ∨ isSequence.s) then
  if islocal.s then
   next(last, s, code, lmap, noblocks, regno, push(argstk, getloc(lmap, value.s, 1)), blocks)
  else if isdefine.s then
   next(last
    , s
    , code
    , [localmap(value.s, top.argstk)] + lmap
    , noblocks
    , regno
    , pop(argstk, 1)
    , blocks)
  else if isbr.s then
   let newcode = CAST(r(regno + 1), slot.top.argstk, i1, trunc)
   let cond = Lcode(code + newcode, s, noblocks, regno + 1, argstk, blocks),
   next(last
    , s
    , emptyinternalbc
    , lmap
    , noblocks + 1
    , regno + 1
    , empty:stack.int
    , push(blocks, cond))
  else if isExit.s then
   assert length.toseq.argstk > 0 report "fail 5e"
   let exitblock = Lcode(code, s, noblocks, regno, argstk, blocks),
   next(last
    , s
    , emptyinternalbc
    , lmap
    , noblocks + 1
    , regno
    , empty:stack.int
    , push(blocks, exitblock))
  else if iscontinue.s then
   let exitblock = Lcode(code, s, noblocks, regno, argstk, blocks),
   next(last
    , s
    , emptyinternalbc
    , lmap
    , noblocks + 1
    , regno
    , empty:stack.int
    , push(blocks, exitblock))
  else if isstart.s then
   let exitblock = Lcode(code, s, noblocks, regno, push(argstk, typ.tollvmtype(typedict, resulttype.s)), blocks),
   next(last
    , s
    , emptyinternalbc
    , lmap
    , noblocks
    , regno
    , empty:stack.int
    , push(blocks, exitblock))
  else
   assert isblock.s report "codegen: Expecting block"
   let no = 
    for nodecount = 1, e ∈ reverse.toseq.blocks
    while not(isstart.sym.e ∨ isloopblock.sym.e)
    do
     nodecount + 1
    /do nodecount
   let blks = top(blocks, no)
   assert length.blks = no report "XXXXXX arg"
   let rblk = processblk(blks, BR(noblocks - 1))
   let firstblkargs = args.first.blks,
   if isstart.sym.first.blks then
    let newstack = push(pop.firstblkargs,-(regno + 1))
    let newcode = code.rblk + phiinst(regno.last.blks, [top.firstblkargs], phi.rblk, 1),
    next(last, s, newcode, lmap, noblocks, regno + 1, newstack, pop(blocks, no))
   else
    assert isloopblock.sym.first.blks report "Code Gen--not expecting first blk kind"
    let nopara2 = nopara.sym.first.blks
    {stack from top is kind, noexps, firstvar, exptypes, exps}
    let rt = undertop(firstblkargs, nopara2)
    let newstack = push(pop(firstblkargs, 2 * nopara2 + 1),-(regno + 1))
    let newcode = code.rblk + phiinst(regno.last.blks, [rt], phi.rblk, 1),
    next(last, s, newcode, lmap, noblocks, regno + 1, newstack, pop(blocks, no))
 else if isBuiltin.s ∧ wordname.s ∈ "createthreadZ" then
  let types2 = 
   tollvmtypelist(typedict
    , basesym.if isFref.lastfref then
     lastfref
    else
     let tmp = getCode(prg.m2, last),
     tmp_(length.tmp - 1)
    )
  let typelist = types2 << 2 + first.types2
  let newcode = 
   code
   + CALLSTART(regno + 1
    , 0
    , 32768
    , typ.function.[ptr.i64, i64, ptr.i64, i64]
    , toint.symboltableentry("createthread", function.[ptr.i64, i64, ptr.i64, i64])
    , 3)
   + CALLFINISH(regno + 1, [-1] + top.argstk + toint.C64.buildargcode.typelist)
  ,
  next(last
   , s
   , newcode
   , lmap
   , noblocks
   , regno + 1
   , push(pop.argstk,-(regno + 1))
   , blocks)
 else
  let ee = findtemplate.s
  assert not.isempty.ee
  report
   "codegen error:no code template for $(s) in library" + library.module.s + "from"
   + %.sym.sd
  let m = ee_1
  let action = action.m,
  if action = "CALL"_1 then
   let noargs = arg.m
   let args = top(argstk, noargs)
   let c = usetemplate(m, regno, empty:seq.int) + CALLFINISH(regno + 1, [-1] + args),
   next(last
    , s
    , code + c
    , lmap
    , noblocks
    , regno + 1
    , push(pop(argstk, noargs),-(regno + 1))
    , blocks)
  else if action = "ACTARG"_1 then
   next(last, s, code, lmap, noblocks, regno, push(argstk, arg.m), blocks)
  else if action = "TEMPLATE"_1 then
   if length.m = 0 then
    next(last, s, code, lmap, noblocks, regno, argstk, blocks)
   else
    let newcode = usetemplate(m, regno, toseq.argstk)
    let noargs = arg.m,
    next(last
     , s
     , code + newcode
     , lmap
     , noblocks
     , regno + length.m
     , push(pop(argstk, noargs),-(regno + length.m))
     , blocks)
  else if action = "SET"_1 then
   assert false report "in SET",
   next(last, s, code, lmap, noblocks, regno, argstk, blocks)
  else if action = "LOOPBLOCK"_1 then
   let varcount = arg.m
   let bodymap = 
    for acc = lmap, @e ∈ arithseq(varcount, 1, 1) do
     addloopmapentry(acc, firstvar.m, regno, @e)
    /do acc
   let pushexptypes = for acc = argstk, e ∈ llvmtypelist.m do push(acc, typ.e) /do acc
   {stack from top is kind (2), noexps, firstvar, exptypes, exps}
   let exitblock = Lcode(code, s, noblocks, regno, pushexptypes, blocks),
   next(last
    , s
    , emptyinternalbc
    , bodymap
    , noblocks + 1
    , regno + varcount
    , empty:stack.int
    , push(blocks, exitblock))
  else if action = "SEQUENCE"_1 then
   let fldbc = sequencecode(top(argstk, arg.m), first.llvmtypelist.m, regno, false),
   next(last
    , s
    , code + bc.fldbc
    , lmap
    , noblocks
    , regno.fldbc
    , push(pop(argstk, arg.m),-(regno + 1))
    , blocks)
  else
   assert action = "RECORD"_1 report "code gen unknown" + action
   let fldbc = recordcode(top(argstk, arg.m), llvmtypelist.m, regno, false),
   next(last
    , s
    , code + bc.fldbc
    , lmap
    , noblocks
    , regno.fldbc
    , push(pop(argstk, arg.m),-(regno + 1))
    , blocks)
/do BLOCKCOUNT(1, noblocks) + code + RET(r(regno + 1), slot.top.argstk)

type Lcode is code:internalbc
 , sym:symbol
 , noblocks:int
 , regno:int
 , args:stack.int
 , blocks:stack.Lcode

type localmap is localno:int, regno:int

function buildargcode(l:seq.llvmtype) int
{needed because the call interface implementation for reals is different than other types is some implementations
 }
for acc = 1, typ ∈ l do
 acc * 2 + if typ.typ = typ.double then 1 else 0
/do acc

type processblkresult is code:internalbc, phi:seq.int

function processblk(blks:seq.Lcode, exitbr:internalbc) processblkresult
for i = 1
 , code = emptyinternalbc
 , phi = empty:seq.int
 , tailphi = empty:seq.int
 , l ∈ blks
do
 assert length.toseq.args.l > 0 report "XXXXXX" + toword.length.blks + toword.i,
 if isExit.sym.l then
  assert length.toseq.args.l ≥ 1 report "check l",
  next(i + 1
   , code + code.l + exitbr
   , phi + [noblocks.l - 1] + top.args.l
   , tailphi)
 else if isloopblock.sym.l then
  let noargs = nopara.sym.l
  let newtailphi = [noblocks.l - 1] + top(pop(args.l, 1 + noargs), noargs),
  next(i + 1, code, phi, newtailphi)
 else if iscontinue.sym.l then
  assert isloopblock.sym.blks_1 report "incorrect format on block"
  let noargs = nopara.sym.l
  let newtailphi = tailphi + [noblocks.l - 1] + top(args.l, noargs)
  let newcode = BR.noblocks.blks_1,
  next(i + 1, code + code.l + newcode, phi, newtailphi)
 else if isstart.sym.l then
  next(i + 1, code + code.l, phi, tailphi)
 else
  {br block}
  assert isbr.sym.l report "expecting br block $(sym.l)"
  let brt = brt.sym.l - 1
  let brf = brf.sym.l - 1
  assert between(i + brt, 1, length.blks) ∧ between(i + brf, 1, length.blks)
  report "codegen error:jmp to unknown block"
  let newcode = BR(r(regno.l + 1), noblocks.blks_(i + brt), noblocks.blks_(i + brf), r.regno.l),
  next(i + 1, code + code.l + newcode, phi, tailphi)
/do
 let firstblk = blks_1
 let code1 = 
  if isloopblock.sym.firstblk then
   let noargs = nopara.sym.firstblk,
   code.firstblk + BR.noblocks.firstblk
   + phiinst(regno.firstblk, top(args.firstblk, noargs), tailphi, noargs)
   + code
  else
   code
 ,
 processblkresult(code1, phi)

function getloc(l:seq.localmap, localno:int, i:int) int
if localno.l_i = localno then regno.l_i else getloc(l, localno, i + 1)

function addloopmapentry(l:seq.localmap, baselocal:int, regbase:int, i:int) seq.localmap
[localmap(baselocal + i - 1,-regbase - i)] + l 