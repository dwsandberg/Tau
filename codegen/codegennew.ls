Module codegennew

use seq.Lcode2

use stack.Lcode2

use UTF8

use bits

use seq.byte

use codetemplates

use codetemplates2

use file

use impDependent

use seq.int

use seq.seq.int

use stack.int

use internalbc

use seq.internalbc

use llvm

use llvmconstants

use seq.llvmtype

use seq.localmap

use seq.match5

use mytype

use seq.mytype

use persistant

use seq.slot

use standard

use symbol

use otherseq.symbol

use symbol2

use set.symdef

use seq.seq.word

use encoding.word3

use seq.encoding.word3

Function starmap(m:midpoint) midpoint
{if symbol with * match symbol in uses then use that one else match current library}
let uses = extractValue(first.src.m, "uses")
let libname = first.extractValue(first.src.m, "Library")
{???? find different way of determining baselib without using last}
let baselib = if isempty.uses then libname else last.uses
let typedict = typedict.m
for acc = empty:set.symdef, sd ∈ toseq.prg.m do
 for acc2 = empty:seq.symbol, sy ∈ code.sd do
  acc2 + clearrequiresbit.replacestar(sy, baselib, libname)
 /for (
  let newsym = replacestar(sym.sd, baselib, libname)
  acc
  + if isInternal.sym.sd then
   symdef4(newsym, acc2, internalidx.sym.sd, "ThisLibrary $(getOptions.sd)")
  else
   symdef4(newsym, acc2, externalNo.sd, getOptionsBits.sd)
 )
/for (midpoint("X", acc, templates.m, typedict.m, libmods.m, src.m))

Function compilerback(m:midpoint, outname:filename) seq.file
{OPTION PROFILE}
let uses = extractValue(first.src.m, "uses")
let baselibwords = dependentwords.uses
let libname = first.extractValue(first.src.m, "Library")
let baselib = if isempty.uses then libname else last.uses
let addresssymbolrefdecode = 
 for addresses = empty:seq.symbol, sd ∈ toseq.prg.m do
  if isAbstract.module.sym.sd ∨ isconst.sym.sd ∨ isBuiltin.sym.sd ∨ isGlobal.sym.sd then
   addresses
  else
   addresses + clearrequiresbit.replacestar(sym.sd, baselib, libname)
 /for (addresses)
let typedict = typedict.m
let isbase = isempty.uses
let prgX = prg.m
let tobepatched = 
 typ.conststype + typ.profiletype + toint.symboltableentry("list", conststype)
 + toint.symboltableentry("profiledata", profiletype)
let discard0 = initwordref.baselibwords
let stepone = stepone(typedict, prgX, libname, isbase)
let defines = defines.stepone
let symboladdress = symboladdress(addresssymbolrefdecode, typedict, prgX, libname, defines)
let stacktraceinfo = extractValue(first.src.m, "stacktrace")
let stacktracesymbol = symbol(moduleref(stacktraceinfo >> 1), stacktraceinfo << 2, seqof.typeword)
let bodies = 
 for acc = empty:seq.internalbc, @e ∈ defines do
  let internalbody = 
   for acc2 = empty:seq.symbol, e9 ∈ arithseq(nopara.sym.@e, 1, 1) do
    acc2 + Local.e9
   /for (acc2 + if name.sym.@e ∈ "stacktrace" then stacktracesymbol else sym.@e)
  acc
  + addfuncdef(geninfo(prgX, libname)
   , if isInternal.sym.@e then
    symdef4(sym.@e, internalbody, externalNo.@e, "ThisLibrary $(getOptions.@e)")
   else
    @e
   )
 /for (acc)
let f2 = 
 modulerecord([merge("init_" + libname)]
  , [toint.FUNCTIONDEC, typ.function.[VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])
let entryfunctyp = function.[ptr.i64, i64, ptr.i64]
let f3 = 
 modulerecord("entrypoint" + libname
  , [toint.FUNCTIONDEC, typ.entryfunctyp, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])
let profiledata = [C64.0, C64.0]
let tmpname = addwordseq.[libname]
let moreargs = 
 [toint.ptrtoint(ptr.entryfunctyp, symboltableentry("entrypoint" + libname, ptr.entryfunctyp))
  ]
 + symboladdress
let xxxx = {all other args to addliblib must be evaluated before this one} wordstoadd.baselibwords
let liblib = slot.addliblib(libname, tmpname, if isbase then xxxx else empty:seq.encoding.word3, moreargs)
let libnametype = array(length.decodeword.libname + 1, i8)
let libslot = 
 modulerecord(""
  , [toint.GLOBALVAR
   , typ.libnametype
   , 2
   , toint.DATA(libnametype, tointseq.decodeword.libname + 0) + 1
   , 3
   , toint.align8
   , 0]
  )
let bodytxts = 
 bodies
 + [
  BLOCKCOUNT(1, 1)
  + CALL(r.1
   , 0
   , 32768
   , function.[i64, ptr.i8, ptr.i64, i64]
   , symboltableentry("initlib5", function.[i64, ptr.i8, ptr.i64, i64])
   , CGEPi8(libslot, 0)
   , [liblib
    , if isbase then
     let f1 = 
      symbol(moduleref([libname] + "impDependent")
       , "addlibwords"
       , typeref("debuginfo impDependent" + libname)
       , typeint)
     assert not.isempty.getCode(prgX, f1) report "PROBLEM"
     let functyp = ptr.tollvmtype(typedict, f1)
     ptrtoint(functyp, symboltableentry([mangledname(prgX, f1, libname)], functyp))
    else
     C64.0
    ]
   )
  + RETURN]
 + [
  BLOCKCOUNT(2, 1) + CALL(r.3, 0, 32768, entryfunctyp, entrypoint.stepone, r.1, r.2)
  + RET(r.4, r.3)]
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
  , [toint.GLOBALVAR
   , typ.profiletype
   , 2
   , toint.AGGREGATE.profiledata + 1
   , 3
   , toint.align8 + 1
   , 0]
  ]
let trec = typerecords
let adjust = 
 [trec_1, [toint.ARRAY, length.data, 0], [toint.ARRAY, 2 + 0, 0]]
 + subseq(trec, 4, length.trec)
let bcdata = llvm(patchlist, bodytxts, adjust)
let cw = commonwords.xxxx
[file(outname, bcdata)
 , file(filename."+$(dirpath.outname + baselib).bcword", bytes.1 + bytes.length.cw + cw)]

function topackedbyteobject(x:seq.byte) int
for acc = [toint.C64.1, toint.C64.length.x], acc2 = 0x0, shift = 0, b ∈ x do
 let newacc2 = acc2 ∨ bits.toint.b << shift
 if shift = 56 then
  next(acc + toint.C64.toint.newacc2, 0x0, 0)
 else
  next(acc, newacc2, shift + 8)
/for (addobject.if shift > 0 then acc + toint.C64.toint.acc2 else acc)

function symboladdress(addressmap:seq.symbol
 , typedict:typedict
 , extnames:set.symdef
 , libname:word
 , defines:seq.symdef) seq.int
for addrsym = [toint.C64.0, toint.C64.length.addressmap], f1 ∈ addressmap do
 let functyp = ptr.tollvmtype(typedict, f1)
 let frefslot = ptrtoint(functyp, symboltableentry([mangledname(extnames, f1, libname)], functyp))
 addrsym + addobject([toint.frefslot] + addsymbol.f1)
/for ([addobject.addrsym])

type geninfo is extnames:set.symdef, libname:word

function addfuncdef(geninfo:geninfo, sd:symdef) internalbc
let e = findtemplate.sym.sd
assert not.isempty.e report "LL addfuncdef $(sym.sd)"
let m = e_1
let code = code.sd
assert not.isempty.code report "codegen with no definition $(sym.sd) in" + library.module.sym.sd
let nopara = arg.m
let linit = 
 Lcode2(emptyinternalbc
  , paramap(nopara, empty:seq.localmap)
  , 1
  , nopara + 1
  , empty:stack.int
  , empty:stack.Lcode2)
let r = for l = linit, s ∈ code do processnext(l, sym.sd, geninfo, s) /for (l)
BLOCKCOUNT(1, noblocks.r) + code.r + RET(r(regno.r + 1), slot.top.args.r)

type Lcode2 is code:internalbc
 , lmap:seq.localmap
 , noblocks:int
 , regno:int
 , args:stack.int
 , blocks:stack.Lcode2

type localmap is localno:int, regno:int

function paramap(i:int, result:seq.localmap) seq.localmap
if i = 0 then result else paramap(i - 1, result + localmap(i,-i - 1))

function length(s:stack.int) int length.toseq.s

function processnext(l:Lcode2, caller:symbol, geninfo:geninfo, s:symbol) Lcode2
let ee = findtemplate.s
assert not.isempty.ee
report
 "codegen error:no code template for $(s) in library" + library.module.s + "from"
 + %.caller
 + for txt = "", s5 ∈ templatesyms do
  if not.isconst.s5 ∧ name.s5 = name.s then
   txt + "/br" + library.module.s5 + %.s5 + "/" + fullprint.para.module.s5 + "/"
   + fullprint.para.module.s
   + if module.s = module.s5 ∧ name.s5 = name.s
   ∧ abstracttype.first.paratypes.s5 = abstracttype.first.paratypes.s then
    "match"
   else
    ""
  else
   txt
 /for (txt)
let m = ee_1
let action = action.m
if action = "CALL"_1 then
 let noargs = arg.m
 let args = top(args.l, noargs)
 let c = usetemplate(m, regno.l, empty:seq.int) + CALLFINISH(regno.l + 1, [-1] + args)
 Lcode2(code.l + c
  , lmap.l
  , noblocks.l
  , regno.l + 1
  , push(pop(args.l, noargs),-(regno.l + 1))
  , blocks.l)
else if action = "ACTARG"_1 then
 Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, arg.m), blocks.l)
else if action = "LOCAL"_1 then
 Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, getloc(lmap.l, arg.m, 1)), blocks.l)
else if action = "TEMPLATE"_1 then
 if length.m = 0 then
  l
 else
  let newcode = usetemplate(m, regno.l, toseq.args.l)
  let noargs = arg.m
  Lcode2(code.l + newcode
   , lmap.l
   , noblocks.l
   , regno.l + length.m
   , push(pop(args.l, noargs),-(regno.l + length.m))
   , blocks.l)
else if action = "EXITBLOCK"_1 then
 assert length.toseq.args.l > 0 report "fail 5e"
 let exitblock = Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, 0), blocks.l)
 Lcode2(emptyinternalbc
  , lmap.l
  , noblocks.l + 1
  , regno.l
  , empty:stack.int
  , push(blocks.l, exitblock))
else if action = "BR2"_1 then
 let newargs = push(push(push(args.l, brt.m - 1), brf.m - 1), 1)
 let newcode = CAST(r(regno.l + 1), slot.top.args.l, i1, trunc)
 let cond = Lcode2(code.l + newcode, lmap.l, noblocks.l, regno.l + 1, newargs, blocks.l)
 Lcode2(emptyinternalbc
  , lmap.l
  , noblocks.l + 1
  , regno.l + 1
  , empty:stack.int
  , push(blocks.l, cond))
else if action = "BLOCK"_1 then
 let no = countnodes.blocks.l
 let blks = top(blocks.l, no)
 assert length.blks = no report "XXXXXX arg"
 let rblk = processblk(blks, 1, empty:seq.localmap, BR(noblocks.l - 1))
 let firstblkargs = args.blks_1
 let kind = top.firstblkargs
 let popno = 
  if kind = 55 then
   {stack from top is kind resulttype} 2
  else
   assert top.firstblkargs = 2 report "Code Gen--not expecting first blk kind" + toword.kind
   {stack from top is kind, noexps, firstvar, exptypes, exps} 2 * top.pop.firstblkargs + 3
 let rt = 
  if kind = 55 then
   top.pop.args.blks_1
  else
   undertop(firstblkargs, top.pop.firstblkargs + 2)
 let newstack = push(pop(firstblkargs, popno),-(regno.l + 1))
 let newcode = code.rblk + phiinst(regno.last.blks, [rt], phi.rblk, 1)
 Lcode2(newcode, lmap.l, noblocks.l, regno.l + 1, newstack, pop(blocks.l, no))
else if action = "DEFINE"_1 then
 Lcode2(code.l
  , [localmap(arg.m, top.args.l)] + lmap.l
  , noblocks.l
  , regno.l
  , pop(args.l, 1)
  , blocks.l)
else if action = "SET"_1 then
 assert false report "in SET"
 l
else if action = "LOOPBLOCK"_1 then
 let varcount = arg.m
 let argstk = {this value added is never used} push(args.l, 0)
 let bodymap = 
  for acc = lmap.l, @e ∈ arithseq(varcount, 1, 1) do
   addloopmapentry(acc, firstvar.m, regno.l, @e)
  /for (acc)
 let pushexptypes = for acc = args.l, e ∈ llvmtypelist.m do push(acc, typ.e) /for (acc)
 let newstk = push(push(pushexptypes, varcount), 2)
 {stack from top is kind, noexps, firstvar, exptypes, exps}
 let exitblock = Lcode2(code.l, lmap.l, noblocks.l, regno.l, newstk, blocks.l)
 Lcode2(emptyinternalbc
  , bodymap
  , noblocks.l + 1
  , regno.l + varcount
  , empty:stack.int
  , push(blocks.l, exitblock))
else if action = "Start"_1 then
 let exitblock = 
  Lcode2(code.l
   , lmap.l
   , noblocks.l
   , regno.l
   , push(push(args.l, typ.first.llvmtypelist.m), 55)
   , blocks.l)
 Lcode2(emptyinternalbc, lmap.l, noblocks.l, regno.l, empty:stack.int, push(blocks.l, exitblock))
else if action = "CONTINUE"_1 then
 let exitblock = Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, 3), blocks.l)
 Lcode2(emptyinternalbc
  , lmap.l
  , noblocks.l + 1
  , regno.l
  , empty:stack.int
  , push(blocks.l, exitblock))
else if action = "SEQUENCE"_1 then
 let fldbc = sequencecode(top(args.l, arg.m), first.llvmtypelist.m, regno.l, false)
 Lcode2(code.l + bc.fldbc
  , lmap.l
  , noblocks.l
  , regno.fldbc
  , push(pop(args.l, arg.m),-(regno.l + 1))
  , blocks.l)
else if action = "createthreadY"_1 then
 let fldbc = recordcode(top(args.l, arg.m - 3), llvmtypelist.m >> 1, regno.l, false)
 let newargs = push(pop(args.l, arg.m - 3),-(regno.l + 1))
 let call = 
  CALLSTART(regno.fldbc + 1
   , 0
   , 32768
   , typ.function.[ptr.i64, i64, i64, i64, i64, ptr.i64, i64]
   , toint.symboltableentry("createthread", function.[ptr.i64, i64, i64, i64, i64, ptr.i64, i64])
   , 6)
  + CALLFINISH(regno.fldbc + 1, [-1] + top(newargs, 4) + toint.C64.buildargcode.llvmtypelist.m)
 Lcode2(code.l + bc.fldbc + call
  , lmap.l
  , noblocks.l
  , regno.fldbc + 1
  , push(pop(args.l, arg.m),-(regno.fldbc + 1))
  , blocks.l)
else
 assert action = "RECORD"_1 report "code gen unknown" + action
 let fldbc = recordcode(top(args.l, arg.m), llvmtypelist.m, regno.l, false)
 Lcode2(code.l + bc.fldbc
  , lmap.l
  , noblocks.l
  , regno.fldbc
  , push(pop(args.l, arg.m),-(regno.l + 1))
  , blocks.l)

function buildargcode(l:seq.llvmtype) int
{needed because the call interface implementation for reals is different than other types is some implementations
 }
for acc = 1, typ ∈ l do acc * 2 + if typ.typ = typ.double then 1 else 0 /for (acc)

function countnodes(s:stack.Lcode2) int
if top.args.top.s ∈ [55, 2] then 1 else 1 + countnodes.pop.s

function processblk(blks:seq.Lcode2, i:int, map:seq.localmap, exitbr:internalbc) processblkresult
processblk(blks, 1, exitbr, emptyinternalbc, 1, empty:seq.int, empty:seq.int)

function kind(a:Lcode2) word toword.top.args.a

type processblkresult is code:internalbc, phi:seq.int

function processblk(blks:seq.Lcode2
 , i:int
 , exitbr:internalbc
 , code:internalbc
 , varcount:int
 , phi:seq.int
 , tailphi:seq.int) processblkresult
if i > length.blks then
 let firstblk = blks_1
 let code1 = 
  if top.args.firstblk = {loopblock} 2 then
   let noargs = top.pop.args.firstblk
   code.firstblk + BR.noblocks.firstblk
   + phiinst(regno.firstblk, top(args.firstblk, noargs + 2), tailphi, noargs)
   + code
  else
   code
 processblkresult(code1, phi)
else
 let l = blks_i
 assert length.toseq.args.l > 0 report "XXXXXX" + toword.length.blks + toword.i
 let kind = top.args.l
 if kind = 0 then
  {exit block}
  assert length.args.l ≥ 2 report "check l"
  let t = top(args.l, varcount + 1)
  let t2 = subseq(t, 1, varcount)
  processblk(blks
   , i + 1
   , exitbr
   , code + code.l + exitbr
   , varcount
   , phi + [noblocks.l - 1] + t2
   , tailphi)
 else if kind = 2 then
  {LOOPBLOCK}
  let noargs = top.pop.args.l
  let newtailphi = [noblocks.l - 1] + top(pop(args.l, 3 + noargs), noargs)
  processblk(blks, i + 1, exitbr, code, varcount, phi, newtailphi)
 else if kind = 3 then
  {CONTINUE}
  assert kind.blks_1 = "2"_1 report "incorrect format on block"
  let noargs = top.pop.args.blks_1
  let newtailphi = tailphi + [noblocks.l - 1] + top(pop.args.l, noargs)
  let newcode = BR.noblocks.blks_1
  processblk(blks, i + 1, exitbr, code + code.l + newcode, varcount, phi, newtailphi)
 else if kind = 55 then
  {Start} processblk(blks, i + 1, exitbr, code + code.l, varcount, phi, tailphi)
 else
  {br block}
  assert kind = 1 report "expecting br block" + toword.kind
  assert length.args.l > 3
  report
   "check m $(for acc = "", @e ∈ [kind] + toseq.args.l do acc + toword.@e /for (acc))
    "
  let args = top(args.l, 4)
  assert between(i + args_2, 1, length.blks) ∧ between(i + args_3, 1, length.blks)
  report "codegen error:jmp to unknown block"
  let newcode = 
   BR(r(regno.l + 1)
    , noblocks.blks_(i + args_2)
    , noblocks.blks_(i + args_3)
    , r.regno.l)
  processblk(blks, i + 1, exitbr, code + code.l + newcode, varcount, phi, tailphi)

function getloc(l:seq.localmap, localno:int, i:int) int
if localno.l_i = localno then regno.l_i else getloc(l, localno, i + 1)

function addloopmapentry(l:seq.localmap, baselocal:int, regbase:int, i:int) seq.localmap
[localmap(baselocal + i - 1,-regbase - i)] + l 