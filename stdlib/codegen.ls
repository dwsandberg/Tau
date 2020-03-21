Module codegen

use bitpackedseq.bit

use codetemplates

use encoding.stat5

use intercode

use internalbc

use ipair.Lcode

use ipair.internalbc

use ipair.linklists2

use libscope

use llvm

use seq.Lcode

use seq.inst

use seq.internalbc

use seq.libsym

use seq.linklists2

use seq.llvmconst

use seq.llvmtype

use seq.localmap

use seq.match5

use seq.seq.bits

use seq.seq.int

use seq.seq.seq.int

use seq.stat5

use stacktrace

use stdlib

use textio

use bits

use seq.bits

use otherseq.llvmtype

use UTF8

function funcdec(f:inst)seq.int
 let discard = C.mangledname.f
  [ MODULECODEFUNCTION, typ.function.constantseq(nopara.f + 2, i64), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

Function codegen5(fs:intercode, thename:word, libdesc:liblib)seq.bits
 let symlist ="libname initlib5 list profcounts profclocks profspace profrefs profstat spacecount" + merge.[ thename,"$profileresult"_1] + "init22 PROCESS2 HASH"
 + merge."llvm.sqrt.f64"
 + merge."llvm.sin.f64"
 + merge."llvm.cos.f64"
  // let conststype = array(-2, i64)//
  let cxx = conststype
  let discard = profiletype
  let declist = @(+,_.coding.fs, empty:seq.inst, defines.fs)
  let discard2 = @(+, C, 0, @(+, mangledname, symlist, declist))
  let xy = table
   // let zx2a = createfile("stat.txt", ["in codegen0.1"])//
   let aa = @(+, towords, empty:seq.seq.word, coding.fs)
    // let zx2b = createfile("stat.txt", ["in codegen0.2"]+ aa)//
    let match5map = @(buildtemplates, identity, inittemppair, aa)
     // let zx2c = createfile("stat.txt", ["in codegen0.3"])//
     // assert false report checkmap.match5map //
     let bodies = @(+, addfuncdef(templates.match5map, coding.fs, codes.fs), empty:seq.internalbc, defines.fs)
     let profilearcs2 = profilearcs
     let noprofileslots = length.profilearcs2 / 2
      // let libsyms = @(+, tolibsym(coding.fs, codes.fs), empty:seq.libsym, defines.fs)//
      let profilearcs3 = addwordseq(consts.match5map, profilearcs2)
      let liblib = addliblib(value.profilearcs3, libdesc)
      let data = value.liblib
      let x = C(array(4, i64)
      , [ AGGREGATE, C(i64, [ CONSTCECAST, 9, typ.ptr.i64, getelementptr(conststype,"list", index.profilearcs3 + 1)]), C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profcounts"]), C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profclocks"]), C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profspace"])])
      let adjust = [ 0, // consttype // length.a.data + 5 + 2, // profiletype // noprofileslots + 2 + 3]
      let libnametype = array(length.decodeword.thename + 1, i8)
      let libnameptr = C(ptr.i8, [ CONSTGEP, typ.libnametype, typ.ptr.libnametype, C."libname", typ.i32, C32.0, typ.i32, C32.0])
      let deflist = [ // libname //
      [ MODULECODEGLOBALVAR, typ.libnametype, 2, C(libnametype, [ CONSTDATA] + tointseq.decodeword.thename + 0) + 1, 3, align4, 0]
      , // lnitlib 5 //
      [ MODULECODEFUNCTION, typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // list // [ MODULECODEGLOBALVAR, typ.conststype, 2, initializer(conststype, data), 3, align8 + 1, 0]
      , // profcounts // [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL]) + 1, 3, align8 + 1, 0]
      , // profclocks // [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL]) + 1, 3, align8 + 1, 0]
      , // profspace // [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL]) + 1, 3, align8 + 1, 0]
      , // profrefs // [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL]) + 1, 3, align8 + 1, 0]
      , // profstat // [ MODULECODEGLOBALVAR, typ.array(4, i64), 2, x + 1, 3, align8 + 1, 0]
      , // spacecount // [ MODULECODEGLOBALVAR, typ.i64, 2, 0, 0, align8 + 1, 0]
      , // profileresult // [ MODULECODEFUNCTION, typ.function.[ i64], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // init22 // [ MODULECODEFUNCTION, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // PROCESS2 // [ MODULECODEFUNCTION, typ.function.[ i64, i64, i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // hash // [ MODULECODEFUNCTION, typ.function.[ i64, i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // llvm.sqrt.f64 // [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // llvm.sin.f64 // [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // llvm.cos.f64 // [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
      + @(+, funcdec, empty:seq.seq.int, declist)
      let bodytxts = [ BLOCKCOUNT(1, 1)
      + RET(1, C(i64, [ CONSTCECAST, 9, typ.ptr.array(4, i64), C."profstat"]))
      , BLOCKCOUNT(1, 1)
      + CALL(1, 0, 32768, typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64], C."initlib5", libnameptr, getelementptr(conststype,"list", 0), getelementptr(conststype,"list", index.liblib + 1))
      + GEP(2, 1, typ.profiletype, C."profclocks", C64.0, C64.1)
      + STORE(3, -2, C64.noprofileslots, align8, 0)
      + GEP(3, 1, typ.profiletype, C."profspace", C64.0, C64.1)
      + STORE(4, -3, C64.noprofileslots, align8, 0)
      + GEP(4, 1, typ.profiletype, C."profcounts", C64.0, C64.1)
      + STORE(5, -4, C64.noprofileslots, align8, 0)
      + GEP(5, 1, typ.profiletype, C."profrefs", C64.0, C64.1)
      + STORE(6, -5, C64.noprofileslots, align8, 0)
      + RET.6]
      + bodies
       llvm(deflist, bodytxts, adjust(typerecords, adjust, 1))

function profiletype llvmtype array(-3, i64)

Function addfuncdef(match5map:seq.match5, coding:seq.inst, codes:seq.seq.int, i:int)internalbc
 let f = coding_i
 let l = Lcode(emptyinternalbc, empty:seq.localmap, 1, nopara.f + 1, empty:seq.int, empty:seq.Lcode, empty:seq.int, 0)
 let g5 = if"PROFILE"_1 in flags.f then mangledname.f else"noprofile"_1
 let r = @(processnext.g5,_.match5map, l, codes_i)
  BLOCKCOUNT(1, noblocks.r) + code.r + RET(regno.r + 1, last.args.r)

type Lcode is record code:internalbc, lmap:seq.localmap, noblocks:int, regno:int, args:seq.int, blocks:seq.Lcode, tailphi:seq.int, loopblock:int

type localmap is record localno:int, regno:int

function push(l:Lcode, code:internalbc, regno:int, arg:int)Lcode
 Lcode(code, lmap.l, noblocks.l, regno, args.l + [ arg], blocks.l, tailphi.l, loopblock.l)

function push(l:Lcode, arg:int)Lcode
 Lcode(code.l, lmap.l, noblocks.l, regno.l, args.l + [ arg], blocks.l, tailphi.l, loopblock.l)

function processnext(profile:word, l:Lcode, m:match5)Lcode
 let inst = inst.m
 let instarg = instarg.m
 let action = action.m
  if action = "CALL"_1 then
  let noargs = arg.m
   let args = top(args.l, noargs)
    if profile = "noprofile"_1 ∨ profile = inst then
    let c = usetemplate(m, regno.l, empty:seq.int) + CALLFINISH(regno.l + 1, [ -1] + args)
      Lcode(code.l + c, lmap.l, noblocks.l, regno.l + 1, poppush(args.l, noargs,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l)
    else
     // if callee ="PROCESS2"_1 then let discard = if noargs = 1 ∧ nosons(t_1)= 5 then profile(profile, arg.label(t_1_3))else Case of CONST insteand of record as arg 0 addcode(l.sons, c,-(regno.l.sons + 1), 1)else //
     profilecall(profiletype, l, args, C.[ inst], profile(profile, inst))
  else if action = "ACTARG"_1 then push(l, arg.m)
  else if action = "LOCAL"_1 then push(l, getloc(lmap.l, toint.instarg, 1))
  else if action = "TEMPLATE"_1 then
  let newcode = usetemplate(m, regno.l, args.l)
    // assert inst ≠"CALLIDX"_1 report astext.addtobitstream(10000, empty:bitpackedseq.bit, newcode)//
    let noargs = arg.m
     Lcode(code.l + newcode, lmap.l, noblocks.l, regno.l + length.m, poppush(args.l, noargs,-(regno.l + length.m)), blocks.l, tailphi.l, loopblock.l)
  else
   assert action = "SPECIAL"_1 report"UNKNOWN ACTION" + action
    if inst = "ELSEBLOCK"_1 then
    Lcode(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l, empty:seq.int, [ l] + blocks.l, tailphi.l, loopblock.l)
    else if inst = "THENBLOCK"_1 then
    let newcode = CAST(regno.l + 1, last.args.l, typ.i1, CASTTRUNC)
     let cond = Lcode(code.l + newcode, lmap.l, noblocks.l, regno.l + 1, poppush(args.l, 1,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l)
      Lcode(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l + 1, empty:seq.int, [ cond] + blocks.l, tailphi.l, loopblock.l)
    else if inst = "if"_1 then
    let varcount = if instarg = "3"_1 then 1 else last.args.l
     let exp3 = l
     let exp1 =(blocks.l)_2
     let exp2 =(blocks.l)_1
     let br = BR(regno.exp1 + 1, noblocks.exp1, noblocks.exp2, last.args.exp1)
     let br1 = BR(regno.exp3, noblocks.exp3)
     let phi = phiinst(regno.exp3, typ.i64, [ noblocks.exp2 - 1] + top(args.exp2, varcount) + [ noblocks.exp3 - 1]
     + if varcount = 1 then [ last.args.exp3]else subseq(top(args.exp3, varcount + 1), 1, varcount), varcount)
     let newcode = code.exp1 + br + code.exp2 + br1 + code.exp3 + br1 + phi
     let newstack = subseq(args.exp1, 1, length.args.exp1 - 1)
     + arithseq(varcount, -1,-(regno.exp3 + 1))
      Lcode(newcode, lmap.l, noblocks.l + 1, regno.exp3 + varcount, // poppush(args.exp1, 1,-(regno.exp3 + 1))// newstack, subseq(blocks.l, 3, length.blocks.l), tailphi.l, loopblock.l)
    else if inst = "DEFINE"_1 then
    Lcode(code.l, lmap.l + localmap(toint.instarg, last.args.l), noblocks.l, regno.l, subseq(args.l, 1, length.args.l - 1), [ l] + blocks.l, tailphi.l, loopblock.l)
    else if inst = "SET"_1 then
    Lcode(code.l, lmap.(blocks.l)_1, noblocks.l, regno.l, args.l, subseq(blocks.l, 2, length.blocks.l), tailphi.l, loopblock.l)
    else if inst = "LOOPBLOCK"_1 then
    let varcount = toint.instarg - 1
     let firstvar = last.args.l
     let bodymap = @(+, loopmapentry(firstvar, regno.l), lmap.l, arithseq(varcount, 1, 1))
     let tailphi = [ noblocks.l - 1]
     + subseq(args.l, length.args.l - varcount, length.args.l - 1)
     let k = Lcode(code.l, lmap.l, noblocks.l, regno.l, subseq(args.l, 1, length.args.l - varcount - 1), blocks.l, tailphi.l, loopblock.l)
      Lcode(emptyinternalbc, bodymap, noblocks.l + 1, regno.l + varcount, [ varcount], [ k] + blocks.l, tailphi, noblocks.l)
    else if inst = "FINISHLOOP"_1 then
    let b =(blocks.l)_1
     let varcount =(args.l)_(length.args.l - 1)
     let newcode = BR(regno.b + 1, loopblock.l) + phiinst(regno.b, typ.i64, tailphi.l, varcount)
     + code.l
      Lcode(code.b + newcode, lmap.b, noblocks.l, regno.l, args.b + [ last.args.l], subseq(blocks.l, 2, length.blocks.l), tailphi.b, loopblock.b)
    else if inst = "CONTINUE"_1 then
    let noargs = toint.instarg
     let block = noblocks.l
     let tailphi = tailphi.l + [ block - 1]
     + subseq(args.l, length.args.l - noargs + 1, length.args.l)
      Lcode(code.l + BR(regno.l, loopblock.l), lmap.l, block + 1, regno.l, poppush(args.l, noargs, -1), blocks.l, tailphi, loopblock.l)
    else if inst = "MRECORD"_1 then
    let noargs = last.args.l
     let args = subseq(top(args.l, noargs + 1), 1, noargs)
     let newcode = CALL(regno.l + 1, 0, 32768, typ.function.[ i64, i64, i64], C."allocatespaceZbuiltinZint", -1, C64.noargs)
     + CAST(regno.l + 2,-(regno.l + 1), typ.ptr.i64, CASTINTTOPTR)
      Lcode(value.@(setnextfld, identity, ipair(regno.l + 2, code.l + newcode), args), lmap.l, noblocks.l, regno.l + 2 + noargs, poppush(args.l, noargs + 1,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l)
    else if inst = "MSET"_1 then l
    else
     assert inst = "RECORD"_1 report"SPECIAL" + inst
     let noargs = toint.instarg
     let args = top(args.l, noargs)
     let newcode = CALL(regno.l + 1, 0, 32768, typ.function.[ i64, i64, i64], C."allocatespaceZbuiltinZint", -1, C64.noargs)
     + CAST(regno.l + 2,-(regno.l + 1), typ.ptr.i64, CASTINTTOPTR)
      Lcode(value.@(setnextfld, identity, ipair(regno.l + 2, code.l + newcode), args), lmap.l, noblocks.l, regno.l + 2 + noargs, poppush(args.l, noargs,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l)

Function setnextfld(p:ipair.internalbc, arg:int)ipair.internalbc
 let regno = index.p
  ipair(regno + 1, value.p + STORE(regno + 1,-regno, arg, align8, 0)
  + GEP(regno + 1, 1, typ.i64,-regno, C64.1))

function getloc(l:seq.localmap, localno:int, i:int)int
 if localno.l_i = localno then regno.l_i else getloc(l, localno, i + 1)

function poppush(a:seq.int, pop:int, new:int)seq.int subseq(a, 1, length.a - pop) + [ new]

function top(a:seq.int, n:int)seq.int subseq(a, length.a - n + 1, length.a)

exp1 exp2 exp2 FIRSTVAR <firstvar> LOOPBLOCK 4 <loop body> FINISHLOOP 2

function loopmapentry(baselocal:int, regbase:int, i:int)localmap localmap(baselocal + i - 1,-regbase - i)

function profilecall(profiletype2:llvmtype, l:Lcode, args:seq.int, callee:int, idx:int)Lcode
 let base = regno.l
 let block = noblocks.l
 let p1 = C(ptr.i64, [ CONSTGEP, typ.profiletype2, typ.ptr.profiletype2, C."profclocks", typ.i32, C32.0, typ.i64, C64.idx])
 let pspace = C(ptr.i64, [ CONSTGEP, typ.profiletype2, typ.ptr.profiletype2, C."profspace", typ.i32, C32.0, typ.i64, C64.idx])
 let pcount = C(ptr.i64, [ CONSTGEP, typ.profiletype2, typ.ptr.profiletype2, C."profcounts", typ.i32, C32.0, typ.i64, C64.idx])
 let c = GEP(base + 1, 1, typ.profiletype2, C."profrefs", C64.0, C64.idx)
 + LOAD(base + 2,-base - 1, typ.i64, align8, 0)
 + BINOP(base + 3,-base - 2, C64.1, 0, typ.i64)
 + STORE(base + 4,-base - 1,-base - 3, align8, 0)
 + CMP2(base + 4,-base - 2, C64.0, 32)
 + BR(base + 5, block, block + 1,-base - 4)
 + CALL(base + 5, 0, 32768, typ.function.[ i64], C."clock")
 + LOAD(base + 6, C."spacecount", typ.i64, align8, 0)
 + CALL(base + 7, 0, 32768, typ.function.constantseq(length.args + 2, i64), callee, -1, args)
 + CALL(base + 8, 0, 32768, typ.function.[ i64], C."clock")
 + LOAD(base + 9, C."spacecount", typ.i64, align8, 0)
 + BINOP(base + 10,-base - 8,-base - 5, 1, typ.i64)
 + BINOP(base + 11,-base - 9,-base - 6, 1, typ.i64)
 + LOAD(base + 12, p1, typ.i64, align8, 0)
 + BINOP(base + 13,-base - 12,-base - 10, 0, typ.i64)
 + STORE(base + 14, p1,-base - 13, align8, 0)
 + LOAD(base + 14, pspace, typ.i64, align8, 0)
 + BINOP(base + 15,-base - 14,-base - 11, 0, typ.i64)
 + STORE(base + 16, pspace,-base - 15, align8, 0)
 + LOAD(base + 16, pcount, typ.i64, align8, 0)
 + BINOP(base + 17,-base - 16, C64.1, 0, typ.i64)
 + STORE(base + 18, pcount,-base - 17, align8, 0)
 + BR(base + 18, block + 2)
 + CALL(base + 18, 0, 32768, typ.function.constantseq(length.args + 2, i64), callee, -1, args)
 + BR(base + 19, block + 2)
 + PHI(base + 19, typ.i64,-base - 7, block,-base - 18, block + 1)
 + LOAD(base + 20,-base - 1, typ.i64, align8, 0)
 + BINOP(base + 21,-base - 20, C64.1, 1, typ.i64)
 + STORE(base + 22,-base - 1,-base - 21, align8, 0)
  Lcode(code.l + c, lmap.l, noblocks.l + 3, regno.l + 21, poppush(args.l, length.args,-base - 19), blocks.l, tailphi.l, loopblock.l)

Function encode(erecord.stat5, stat5)encoding.stat5 export

type statencoding is encoding stat5

type stat5 is record caller:word, callee:word, index:int

function stat5(caller:word, callee:word)stat5 stat5(caller, callee, 0)

function addindex(s:stat5, i:int)stat5 stat5(caller.s, callee.s, i)

function hash(s:stat5)int abs(hash.caller.s + hash.callee.s)

function =(a:stat5, b:stat5)boolean caller.a = caller.b ∧ callee.a = callee.b

Function profile(caller:word, callee:word)int
 if caller = callee ∨ caller = "noprofile"_1 then 0
 else findindex(statencoding, stat5(caller, callee)) + 1

function callarc(a:stat5)seq.word [ caller.a, callee.a]

Function profilearcs seq.word @(+, callarc,"", orderadded.statencoding)

/type debug is encoding ipair.Lcode

/function hash(i:ipair.Lcode)int index.i

/function =(a:ipair.Lcode, b:ipair.Lcode)boolean index.a = index.b

/function print(p:ipair.Lcode)seq.word let l = value.p {"&br"+ state.l +"regno ="+ toword.regno.l + @(+, toword,"", args.l)+ @(+, printL,"", blocks.l)}

+"code"+ print.code.l }

/function printL(x:Lcode)seq.word @(+, toword,"[", args.x)+"]"

/Function dump seq.word @(+, print,"", mapping.debug)


   
   
