Module codegennew

use UTF8

use bits

use codetemplates

use internalbc

use llvm

use llvmconstants

use standard

use symbol

use program

use textio

use seq.Lcode2

use stack.Lcode2

use seq.bits

use stack.int

use seq.internalbc

use seq.llvmtype

use seq.localmap

use seq.match5

use seq.slot

use encoding.stat5

use seq.stat5

use seq.symbol

use set.symbol

use seq.seq.bits

use seq.seq.int

use seq.encodingpair.stat5

use seq.seq.seq.int

Function codegen(theprg:program, definesWithBuiltins:seq.symbol, uses:set.symbol, thename:word, libdesc:symbol, alltypes:typedict, isbase:boolean)seq.bits
let defines = for acc = empty:seq.symbol, ele = definesWithBuiltins do
let d = getCode(theprg, ele)
if isempty.d then { sym not defined in this library }acc
 else if"BUILTIN"_1 ∉ getoption.d then acc + ele
 else
  { if builtin not implement with external function. Must define an internal one }
  if inmodule(ele,"real") ∧ wordname.ele ∈ "+-* / ? representation casttoreal toreal intpart"then
   acc + ele
  else if inmodule(ele,"standard") ∧ wordname.ele ∈ "+-* / ? true false = > not"then
   acc + ele
  else if inmodule(ele,"bits") ∧ wordname.ele ∈ ">> << ∧ ∨ xor toint"then acc + ele
  else if inmodule(ele,"interpreter") ∧ wordname.ele ∈ "GEP bitcast"then acc + ele
  else if inmodule(ele,"fileio") ∧ wordname.ele ∈ "tocstr"then acc + ele
  else if inmodule(ele,"tausupport") ∧ wordname.ele ∈ "bitcast getseqlength getseqtype"then acc + ele
  else { implemented by external funciton }acc
/for(acc)
let tobepatched = typ.conststype + typ.profiletype + toint.symboltableentry("list", conststype) + toint.symboltableentry("profiledata", profiletype)
let discard4 = for acc = 0, @e = defines do acc + funcdec(alltypes, @e)/for(acc)
let match5map = match5map(theprg, uses, alltypes)
let libmods2 = arg.match5map_libdesc
 { let zx2c = createfile("stat.txt", ["in codegen0.3"])}
 let discard3 = modulerecord("spacecount", [ toint.GLOBALVAR, typ.i64, 2, 0, 0, toint.align8 + 1, 0])
 let bodies = for acc = empty:seq.internalbc, @e = defines do acc + addfuncdef(match5map, @e)/for(acc)
 let xxx = profiledata
 let liblib = slot.addliblib([ thename], libmods2, toint.ptrtoint(ptr.i64, CGEP(symboltableentry("profiledata", profiletype), 0)), isbase)
 let libnametype = array(length.decodeword.thename + 1, i8)
 let libslot = modulerecord(""
 , [ toint.GLOBALVAR, typ.libnametype, 2, toint.DATA(libnametype, tointseq.decodeword.thename + 0) + 1, 3, toint.align8, 0]
 )
 let f2 = modulerecord("init22", [ toint.FUNCTIONDEC, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])
 let bodytxts = bodies
 + [ BLOCKCOUNT(1, 1)
 + CALL(r.1, 0, 32768, function.[ i64, ptr.i8, ptr.i64, i64], symboltableentry("initlib5", function.[ i64, ptr.i8, ptr.i64, i64]), CGEPi8(libslot, 0), [ liblib, if isbase then C64.1 else C64.0])
 + RETURN
 ]
 let data = constdata
 let patchlist = [ [ toint.GLOBALVAR, typ.conststype, 2, toint.AGGREGATE.data + 1, 3, toint.align8 + 1, 0], [ toint.GLOBALVAR, typ.profiletype, 2, toint.xxx + 1, 3, toint.align8 + 1, 0]]
 let trec = typerecords
 let adjust = [ trec_1, [ toint.ARRAY, length.data, 0], [ toint.ARRAY, profiledatalen, 0]] + subseq(trec, 4, length.trec)
 llvm(patchlist, bodytxts, adjust)

function addfuncdef(match5map:seq.match5, i:symbol)internalbc
 { let hh = process.subaddfuncdef(match5map, i)assert not.aborted.hh report"fail get"+ print.i + message.hh result.hh use process.internalbc function subaddfuncdef(match5map:seq.match5, i:symbol)internalbc }
 let m = match5map_i
 let options = options(match5map, m)
 let codet = if length.options > 0 then
  { assert"PROFILE"_1 in options report"PROFILE PROBLEM"+ options }
  subseq(code.m, 1, length.code.m - 2)
 else code.m
 let code = if isempty.codet then
  for acc = empty:seq.symbol, e9 = arithseq(nopara.i, 1, 1)do acc + Local.e9 /for(acc)
  + i
 else codet
  { assert not.isempty.code.m report"xxxx"+ print.i }
  let nopara = arg.m
  let l = Lcode2(emptyinternalbc, paramap(nopara, empty:seq.localmap), 1, nopara + 1, empty:stack.int, empty:stack.Lcode2)
  let g5 = if"PROFILE"_1 ∈ options then mangledname.i else"noprofile"_1
  let r = for acc = l, @e = code do processnext(acc, g5, match5map, @e)/for(acc)
  BLOCKCOUNT(1, noblocks.r) + code.r
   + RET(r(regno.r + 1), slot.top.args.r)

type Lcode2 is code:internalbc, lmap:seq.localmap, noblocks:int, regno:int, args:stack.int, blocks:stack.Lcode2

type localmap is localno:int, regno:int

function paramap(i:int, result:seq.localmap)seq.localmap
 if i = 0 then result else paramap(i - 1, result + localmap(i,-i - 1))

function length(s:stack.int)int length.toseq.s

function processnext(l:Lcode2, profile:word, match5map:seq.match5, s:symbol)Lcode2
let m = match5map_s
let action = action.m
 if action = "CALL"_1 then
 let callee = mangledname.s
 let noargs = arg.m
 let args = top(args.l, noargs)
 if profile = "noprofile"_1 ∨ profile = callee then
  let c = usetemplate(m, regno.l, empty:seq.int) + CALLFINISH(regno.l + 1, [-1] + args)
  Lcode2(code.l + c, lmap.l, noblocks.l, regno.l + 1, push(pop(args.l, noargs),-(regno.l + 1)), blocks.l)
  else profilecall(l, args, symboltableentry(callee, functype.m), profile(profile, callee), functype.m)
 else if action = "CALLE"_1 then
 let noargs = arg.m
 let args = top(args.l, noargs)
 let c = usetemplate(m, regno.l, empty:seq.int) + CALLFINISH(regno.l + 1, args)
 Lcode2(code.l + c, lmap.l, noblocks.l, regno.l + 1, push(pop(args.l, noargs),-(regno.l + 1)), blocks.l)
 else if action = "ACTARG"_1 then
  Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, arg.m), blocks.l)
 else if action = "LOCAL"_1 then
  Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, getloc(lmap.l, arg.m, 1)), blocks.l)
 else if action = "TEMPLATE"_1 then
  if length.m = 0 then l
  else
   let newcode = usetemplate(m, regno.l, toseq.args.l)
   let noargs = arg.m
    Lcode2(code.l + newcode, lmap.l, noblocks.l, regno.l + length.m, push(pop(args.l, noargs),-(regno.l + length.m)), blocks.l)
 else if action = "EXITBLOCK"_1 then
  assert length.toseq.args.l > 0 report"fail 5e"
  let exitblock = Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, 0), blocks.l)
  Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l, empty:stack.int, push(blocks.l, exitblock))
 else if action = "BR2"_1 then
 let newargs = push(push(push(args.l, brt.m - 1), brf.m - 1), 1)
 let newcode = CAST(r(regno.l + 1), slot.top.args.l, i1, trunc)
 let cond = Lcode2(code.l + newcode, lmap.l, noblocks.l, regno.l + 1, newargs, blocks.l)
 Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l + 1, empty:stack.int, push(blocks.l, cond))
 else if action = "BLOCK"_1 then
 let no = { arg.m }countnodes.blocks.l
 let blks = top(blocks.l, no)
 assert length.blks = no report"XXXXXX arg" + profile
  let rblk = processblk(blks, 1, empty:seq.localmap, BR(noblocks.l - 1))
  { assert length.phi.rblk > 3 report"phi"+ @(+, toword,"", phi.rblk)}
   let firstblkargs = args.blks_1
   let kind = top.firstblkargs
   let popno = if kind = 55 then { stack from top is kind resulttype }2
   else
    assert top.firstblkargs = 2 report"Code Gen--not expecting first blk kind" + toword.kind + profile
     { stack from top is kind, noexps, firstvar, exptypes, exps }2 * top.pop.firstblkargs + 3
   let rt = if kind = 55 then top.pop.args.blks_1 else undertop(firstblkargs, top.pop.firstblkargs + 2)
   let newstack = push(pop(firstblkargs, popno),-(regno.l + 1))
   let newcode = code.rblk + phiinst(regno.last.blks, [ rt], phi.rblk, 1)
   Lcode2(newcode, lmap.l, noblocks.l, regno.l + 1, newstack, pop(blocks.l, no))
 else if action = "DEFINE"_1 then
  Lcode2(code.l, [ localmap(arg.m, top.args.l)] + lmap.l, noblocks.l, regno.l, pop(args.l, 1), blocks.l)
 else if action = "SET"_1 then assert false report"in SET"
 l
 else if action = "LOOPBLOCK"_1 then
 let varcount = arg.m
 let argstk = { this value added is never used }push(args.l, 0)
 let bodymap = for acc = lmap.l, @e = arithseq(varcount, 1, 1)do addloopmapentry(acc, firstvar.m, regno.l, @e)/for(acc)
 let pushexptypes = for acc = args.l, e = llvmtypelist.m do push(acc, typ.e)/for(acc)
 let newstk = push(push(pushexptypes, varcount), 2)
 { stack from top is kind, noexps, firstvar, exptypes, exps }
  let exitblock = Lcode2(code.l, lmap.l, noblocks.l, regno.l, newstk, blocks.l)
  Lcode2(emptyinternalbc, bodymap, noblocks.l + 1, regno.l + varcount, empty:stack.int, push(blocks.l, exitblock))
 else if action = "Start"_1 then
 let exitblock = Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(push(args.l, typ.first.llvmtypelist.m), 55), blocks.l)
 Lcode2(emptyinternalbc, lmap.l, noblocks.l, regno.l, empty:stack.int, push(blocks.l, exitblock))
 else if action = "CONTINUE"_1 then
 let exitblock = Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, 3), blocks.l)
 Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l, empty:stack.int, push(blocks.l, exitblock))
 else if action = "SEQUENCE"_1 then
 let fldbc = sequencecode(top(args.l, arg.m), first.llvmtypelist.m, regno.l, false)
 Lcode2(code.l + bc.fldbc, lmap.l, noblocks.l, regno.fldbc, push(pop(args.l, arg.m),-(regno.l + 1)), blocks.l)
 else if action = "createthreadY"_1 then
 let fldbc = recordcode(top(args.l, arg.m - 3), llvmtypelist.m >> 1, regno.l, false)
 let newargs = push(pop(args.l, arg.m - 3),-(regno.l + 1))
 let call = CALLSTART(regno.fldbc + 1, 0, 32768, typ.function.[ ptr.i64, i64, i64, i64, i64, ptr.i64, i64], toint.symboltableentry("createthread", function.[ ptr.i64, i64, i64, i64, i64, ptr.i64, i64]), 6)
 + CALLFINISH(regno.fldbc + 1, [-1] + top(newargs, 4) + toint.C64.buildargcode.llvmtypelist.m)
 Lcode2(code.l + bc.fldbc + call, lmap.l, noblocks.l, regno.fldbc + 1, push(pop(args.l, arg.m),-(regno.fldbc + 1)), blocks.l)
 else
  assert action = "RECORD"_1 report"code gen unknown" + action
  let fldbc = recordcode(top(args.l, arg.m), llvmtypelist.m, regno.l, false)
  Lcode2(code.l + bc.fldbc, lmap.l, noblocks.l, regno.fldbc, push(pop(args.l, arg.m),-(regno.l + 1)), blocks.l)

function buildargcode(l:seq.llvmtype)int
 { needed because the call interface implementation for reals is different than other types is some implementations }
 for acc = 1, typ = l do
  acc * 2 + if typ.typ = typ.double then 1 else 0
 /for(acc)

function countnodes(s:stack.Lcode2)int
 if top.args.top.s ∈ [ 55, 2]then 1 else 1 + countnodes.pop.s

function processblk(blks:seq.Lcode2, i:int, map:seq.localmap, exitbr:internalbc)processblkresult
 processblk(blks, 1, exitbr, emptyinternalbc, 1, empty:seq.int, empty:seq.int)

function kind(a:Lcode2)word toword.top.args.a

type processblkresult is code:internalbc, phi:seq.int

function processblk(blks:seq.Lcode2, i:int, exitbr:internalbc, code:internalbc, varcount:int, phi:seq.int, tailphi:seq.int)processblkresult
 if i > length.blks then
 let firstblk = blks_1
 let code1 = if top.args.firstblk = { loopblock }2 then
 let noargs = top.pop.args.firstblk
  code.firstblk + BR.noblocks.firstblk + phiinst(regno.firstblk, top(args.firstblk, noargs + 2), tailphi, noargs)
  + code
 else code
  processblkresult(code1, phi)
 else
  let l = blks_i
   assert length.toseq.args.l > 0 report"XXXXXX" + toword.length.blks + toword.i
   let kind = top.args.l
    if kind = 0 then
     { exit block }
     assert length.args.l ≥ 2 report"check l"
     let t = top(args.l, varcount + 1)
     let t2 = subseq(t, 1, varcount)
     processblk(blks, i + 1, exitbr, code + code.l + exitbr, varcount, phi + [ noblocks.l - 1] + t2, tailphi)
    else if kind = 2 then
     { LOOPBLOCK }
     { assert false report"L"+ @(+, toword,"", args.l)}
     let noargs = top.pop.args.l
      { let firstvar = top.pop.args.l }
      let newtailphi = [ noblocks.l - 1] + top(pop(args.l, 3 + noargs), noargs)
      processblk(blks, i + 1, exitbr, code, varcount, phi, newtailphi)
    else if kind = 3 then
     { CONTINUE }
     assert kind.blks_1 = "2"_1 report"incorrect format on block"
     { + for e10 ∈ blks, oldacc ="",,, oldacc + kind.e10 }
      let noargs = top.pop.args.blks_1
       { assert false report"C"+ @(+, toword,"", args.blks_1)+"noargs:"+ toword.noargs }
       let newtailphi = tailphi + [ noblocks.l - 1] + top(pop.args.l, noargs)
       let newcode = BR.noblocks.blks_1
        processblk(blks, i + 1, exitbr, code + code.l + newcode, varcount, phi, newtailphi)
    else if kind = 55 then { Start }processblk(blks, i + 1, exitbr, code + code.l, varcount, phi, tailphi)
    else
     { br block }
     assert kind = 1 report"expecting br block" + toword.kind
      assert length.args.l > 3 report"check m"
      + for acc ="", @e = [ kind] + toseq.args.l do acc + toword.@e /for(acc)
      let args = top(args.l, 4)
      assert between(i + args_2, 1, length.blks) ∧ between(i + args_3, 1, length.blks)report"codegen error:jmp to unknown block"
       let newcode = BR(r(regno.l + 1), noblocks.blks_(i + args_2), noblocks.blks_(i + args_3), r.regno.l)
       processblk(blks, i + 1, exitbr, code + code.l + newcode, varcount, phi, tailphi)

function getloc(l:seq.localmap, localno:int, i:int)int
 if localno.l_i = localno then regno.l_i else getloc(l, localno, i + 1)

function addloopmapentry(l:seq.localmap, baselocal:int, regbase:int, i:int)seq.localmap
 [ localmap(baselocal + i - 1,-regbase - i)] + l

function profilecall(l:Lcode2, args:seq.int, callee:slot, idx:int, functype:llvmtype)Lcode2
let base = regno.l
let block = noblocks.l
let pcount = toint.CGEP(symboltableentry("profiledata", ptr.profiletype), 2 + 6 * (idx - 2) + 2)
let p1 = { pclocks }
toint.CGEP(symboltableentry("profiledata", ptr.profiletype), 2 + 6 * (idx - 2) + 3)
let pspace = toint.CGEP(symboltableentry("profiledata", ptr.profiletype), 2 + 6 * (idx - 2) + 4)
let prefs = toint.CGEP(symboltableentry("profiledata", ptr.profiletype), 2 + 6 * (idx - 2) + 5)
let c = GEP(r(base + 1), profiletype, symboltableentry("profiledata", ptr.profiletype))
+ LOAD(r(base + 2), slot.prefs, i64)
+ BINOP(r(base + 3), r(base + 2), C64.1, add)
+ STORE(r(base + 4), slot.prefs, r(base + 3))
+ CMP2(r(base + 4), r(base + 2), C64.0, 32)
+ BR(r(base + 5), block, block + 1, r(base + 4))
+ CALL(r(base + 5), 0, 32768, function.[ i64], symboltableentry("clock", function.[ i64]))
+ LOAD(r(base + 6), symboltableentry("spacecount", i64), i64)
+ CALL(r(base + 7), 0, 32768, functype, callee, r.1, for acc = empty:seq.slot, @e = args do acc + slot.@e /for(acc))
+ CALL(r(base + 8), 0, 32768, function.[ i64], symboltableentry("clock", function.[ i64]))
+ LOAD(r(base + 9), symboltableentry("spacecount", i64), i64)
+ BINOP(r(base + 10), r(base + 8), r(base + 5), sub)
+ BINOP(r(base + 11), r(base + 9), r(base + 6), sub)
+ LOAD(r(base + 12), slot.p1, i64)
+ BINOP(r(base + 13), r(base + 12), r(base + 10), add)
+ STORE(r(base + 14), slot.p1, r(base + 13))
+ LOAD(r(base + 14), slot.pspace, i64)
+ BINOP(r(base + 15), r(base + 14), r(base + 11), add)
+ STORE(r(base + 16), slot.pspace, r(base + 15))
+ LOAD(r(base + 16), slot.pcount, i64)
+ BINOP(r(base + 17), r(base + 16), C64.1, add)
+ STORE(r(base + 18), slot.pcount, r(base + 17))
+ BR(block + 2)
+ CALL(r(base + 18), 0, 32768, functype, callee, r.1, for acc = empty:seq.slot, @e = args do acc + slot.@e /for(acc))
+ BR(block + 2)
+ PHI(r(base + 19), returntype.functype, r(base + 7), block, r(base + 18), block + 1)
+ LOAD(r(base + 20), slot.prefs, i64)
+ BINOP(r(base + 21), r(base + 20), C64.1, sub)
+ STORE(r(base + 22), slot.prefs, r(base + 21))
Lcode2(code.l + c, lmap.l, noblocks.l + 3, regno.l + 21, push(pop(args.l, length.args),-base - 19), blocks.l)

type stat5 is caller:word, callee:word

function profiledata slot let d = encoding:seq.encodingpair.stat5
let data = for acc = [ C64.1, C64.length.d], @e = d do
 acc
 + [ slot.wordref.caller.data.@e, slot.wordref.callee.data.@e, C64.0, C64.0, C64.0, C64.0]
/for(acc)
AGGREGATE.data

function profiledatalen int length.encoding:seq.encodingpair.stat5 * 6 + 2

function assignencoding(p:seq.encodingpair.stat5, a:stat5)int length.p + 1

function hash(s:stat5)int abs(hash.caller.s + hash.callee.s)

function =(a:stat5, b:stat5)boolean caller.a = caller.b ∧ callee.a = callee.b

Function profile(caller:word, callee:word)int
 if caller = callee ∨ caller = "noprofile"_1 then 0
 else valueofencoding.encode.stat5(caller, callee) + 1 