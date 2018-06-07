module altgen

use bitpackedseq.bit

use codetemplates

use internalbc

use ipair.Lcode

use ipair.internalbc

use llvm

use passcommon

use seq.Lcode

use seq.encoding.llvmtype

use seq.inst

use seq.int

use seq.internalbc

use seq.ipair.Lcode

use seq.llvmconst

use seq.localmap

use seq.match5

use seq.seq.int

use seq.stat5

use stdlib

function profiletype encoding.llvmtype array(-3, i64)

Function addfuncdef(match5map:seq.match5, coding:seq.inst, codes:seq.seq.int, i:int)internalbc 
 let f = coding_i 
  let l = Lcode(emptyinternalbc, empty:seq.localmap, 1, nopara.f + 1, empty:seq.int, empty:seq.Lcode, empty:seq.int, 0)
  let g5 = if"PROFILE"_1 in flags.f then mangledname.f else"noprofile"_1 
  let r = @(processnext.g5,_.match5map, l, codes_i)
  // assert length.done.code.r < 100 report [ mangledname.f]+ astext.addtobitstream(10000, empty:bitpackedseq.bit, code.r)+ @(+, toword,"??", done.code.r)print.code.r // 
   BLOCKCOUNT(1, noblocks.r)+ code.r + RET(regno.r + 1, last.args.r)

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
  if action ="CALL"_1 
  then let noargs = arg.m 
   let args = top(args.l, noargs)
   if profile ="noprofile"_1 ∨ profile = inst 
   then let c = usetemplate(m, regno.l, empty:seq.int)+ CALLFINISH(regno.l + 1, [ -1]+ args)
    Lcode(code.l + c, lmap.l, noblocks.l, regno.l + 1, poppush(args.l, noargs,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l)
   else // if callee ="PROCESS2"_1 then let discard = if noargs = 1 ∧ nosons(t_1)= 5 then profile(profile, arg.label(t_1_3))else Case of CONST insteand of record as arg 0 addcode(l.sons, c,-(regno.l.sons + 1), 1)else // 
   profilecall(profiletype, l, args, C.[ inst], profile(profile, inst))
  else if action ="ACTARG"_1 
  then push(l, arg.m)
  else if action ="LOCAL"_1 
  then push(l, getloc(lmap.l, toint.instarg, 1))
  else if action ="TEMPLATE"_1 
  then let newcode = usetemplate(m, regno.l, args.l)
   // assert inst ≠"CALLIDX"_1 report astext.addtobitstream(10000, empty:bitpackedseq.bit, newcode)// 
   let noargs = arg.m 
   Lcode(code.l + newcode, lmap.l, noblocks.l, regno.l + length.m, poppush(args.l, noargs,-(regno.l + length.m)), blocks.l, tailphi.l, loopblock.l)
  else assert action ="SPECIAL"_1 report"UNKNOWN ACTION"+ action 
  if inst ="ELSEBLOCK"_1 
  then Lcode(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l, empty:seq.int, [ l]+ blocks.l, tailphi.l, loopblock.l)
  else if inst ="THENBLOCK"_1 
  then let newcode = CAST(regno.l + 1, last.args.l, typ.i1, CASTTRUNC)
   let cond = Lcode(code.l + newcode, lmap.l, noblocks.l, regno.l + 1, poppush(args.l, 1,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l)
   Lcode(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l + 1, empty:seq.int, [ cond]+ blocks.l, tailphi.l, loopblock.l)
  else if inst ="if"_1 
  then let varcount = if instarg ="3"_1 then 1 else last.args.l 
   let exp3 = l 
   let exp1 = blocks(l)_2 
   let exp2 = blocks(l)_1 
   let br = BR(regno.exp1 + 1, noblocks.exp1, noblocks.exp2, last.args.exp1)
   let br1 = BR(regno.exp3, noblocks.exp3)
   let phi = phiinst(regno.exp3, typ.i64, [ noblocks.exp2 - 1]+ top(args.exp2, varcount)+ [ noblocks.exp3 - 1]+ if varcount = 1 then [ last.args.exp3]else subseq(top(args.exp3, varcount + 1), 1, varcount), varcount)
   let newcode = code.exp1 + br + code.exp2 + br1 + code.exp3 + br1 + phi 
   let newstack = subseq(args.exp1, 1, length.args.exp1 - 1)+ arithseq(varcount, -1,-(regno.exp3 + 1))
   Lcode(newcode, lmap.l, noblocks.l + 1, regno.exp3 + varcount, // poppush(args.exp1, 1,-(regno.exp3 + 1))// newstack, subseq(blocks.l, 3, length.blocks.l), tailphi.l, loopblock.l)
  else if inst ="DEFINE"_1 
  then Lcode(code.l, lmap.l + localmap(toint.instarg, last.args.l), noblocks.l, regno.l, subseq(args.l, 1, length.args.l - 1), [ l]+ blocks.l, tailphi.l, loopblock.l)
  else if inst ="SET"_1 
  then Lcode(code.l, lmap(blocks(l)_1), noblocks.l, regno.l, args.l, subseq(blocks.l, 2, length.blocks.l), tailphi.l, loopblock.l)
  else if inst ="LOOPBLOCK"_1 
  then let varcount = toint.instarg - 1 
   let firstvar = last.args.l 
   let bodymap = @(+, loopmapentry(firstvar, regno.l), lmap.l, arithseq(varcount, 1, 1))
   let tailphi = [ noblocks.l - 1]+ subseq(args.l, length.args.l - varcount, length.args.l - 1)
   let k = Lcode(code.l, lmap.l, noblocks.l, regno.l, subseq(args.l, 1, length.args.l - varcount - 1), blocks.l, tailphi.l, loopblock.l)
   Lcode(emptyinternalbc, bodymap, noblocks.l + 1, regno.l + varcount, [ varcount], [ k]+ blocks.l, tailphi, noblocks.l)
  else if inst ="FINISHLOOP"_1 
  then let b = blocks(l)_1 
   let varcount = args(l)_(length.args.l - 1)
   let newcode = BR(regno.b + 1, loopblock.l)+ phiinst(regno.b, typ.i64, tailphi.l, varcount)+ code.l 
   Lcode(code.b + newcode, lmap.b, noblocks.l, regno.l, args.b + [ last.args.l], subseq(blocks.l, 2, length.blocks.l), tailphi.b, loopblock.b)
  else if inst ="CONTINUE"_1 
  then let noargs = toint.instarg 
   let block = noblocks.l 
   let tailphi = tailphi.l + [ block - 1]+ subseq(args.l, length.args.l - noargs + 1, length.args.l)
   Lcode(code.l + BR(regno.l, loopblock.l), lmap.l, block + 1, regno.l, poppush(args.l, noargs, -1), blocks.l, tailphi, loopblock.l)
  else if inst ="MRECORD"_1 
  then let noargs = last.args.l 
   let args = subseq(top(args.l, noargs + 1), 1, noargs)
   let newcode = CALL(regno.l + 1, 0, 32768, typ.function.[ i64, i64, i64], C."allocatespaceZbuiltinZint", -1, C64.noargs)+ CAST(regno.l + 2,-(regno.l + 1), typ.ptr.i64, CASTINTTOPTR)
   Lcode(value.@(setnextfld, identity, ipair(regno.l + 2, code.l + newcode), args), lmap.l, noblocks.l, regno.l + 2 + noargs, poppush(args.l, noargs + 1,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l)
  else if inst ="MSET"_1 
  then l 
  else assert inst ="RECORD"_1 report"SPECIAL"+ inst 
  let noargs = toint.instarg 
  let args = top(args.l, noargs)
  let newcode = CALL(regno.l + 1, 0, 32768, typ.function.[ i64, i64, i64], C."allocatespaceZbuiltinZint", -1, C64.noargs)+ CAST(regno.l + 2,-(regno.l + 1), typ.ptr.i64, CASTINTTOPTR)
  Lcode(value.@(setnextfld, identity, ipair(regno.l + 2, code.l + newcode), args), lmap.l, noblocks.l, regno.l + 2 + noargs, poppush(args.l, noargs,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l)

exp1 exp2 exp2 FIRSTVAR <firstvar> LOOPBLOCK 4 <loop body> FINISHLOOP 2

cegiczCyJqp6EKTm

Function setnextfld(p:ipair.internalbc, arg:int)ipair.internalbc 
 let regno = index.p 
  ipair(regno + 1, value.p + STORE(regno + 1,-regno, arg, align8, 0)+ GEP(regno + 1, 1, typ.i64,-regno, C64.1))

function getloc(l:seq.localmap, localno:int, i:int)int 
 if localno(l_i)= localno then regno(l_i)else getloc(l, localno, i + 1)

function poppush(a:seq.int, pop:int, new:int)seq.int subseq(a, 1, length.a - pop)+ [ new]

function top(a:seq.int, n:int)seq.int subseq(a, length.a - n + 1, length.a)

exp1 exp2 exp2 FIRSTVAR <firstvar> LOOPBLOCK 4 <loop body> FINISHLOOP 2

function loopmapentry(baselocal:int, regbase:int, i:int)localmap localmap(baselocal + i - 1,-regbase - i)

function profilecall(profiletype2:encoding.llvmtype, l:Lcode, args:seq.int, callee:int, idx:int)Lcode 
 let base = regno.l 
  let block = noblocks.l 
  let p1 = C(ptr.i64, [ CONSTGEP, 
  typ.profiletype2, 
  typ.ptr.profiletype2, 
  C."profclocks", 
  typ.i32, 
  C32.0, 
  typ.i64, 
  C64.idx])
  let pspace = C(ptr.i64, [ CONSTGEP, 
  typ.profiletype2, 
  typ.ptr.profiletype2, 
  C."profspace", 
  typ.i32, 
  C32.0, 
  typ.i64, 
  C64.idx])
  let pcount = C(ptr.i64, [ CONSTGEP, 
  typ.profiletype2, 
  typ.ptr.profiletype2, 
  C."profcounts", 
  typ.i32, 
  C32.0, 
  typ.i64, 
  C64.idx])
  let c = GEP(base + 1, 1, typ.profiletype2, C."profrefs", C64.0, C64.idx)+ LOAD(base + 2,-base - 1, typ.i64, align8, 0)+ BINOP(base + 3,-base - 2, C64.1, 0, typ.i64)+ STORE(base + 4,-base - 1,-base - 3, align8, 0)+ CMP2(base + 4,-base - 2, C64.0, 32)+ BR(base + 5, block, block + 1,-base - 4)+ CALL(base + 5, 0, 32768, typ.function.[ i64], C."clock")+ LOAD(base + 6, C."spacecount", typ.i64, align8, 0)+ CALL(base + 7, 0, 32768, typ.function.constantseq(length.args + 2, i64), callee, -1, args)+ CALL(base + 8, 0, 32768, typ.function.[ i64], C."clock")+ LOAD(base + 9, C."spacecount", typ.i64, align8, 0)+ BINOP(base + 10,-base - 8,-base - 5, 1, typ.i64)+ BINOP(base + 11,-base - 9,-base - 6, 1, typ.i64)+ LOAD(base + 12, p1, typ.i64, align8, 0)+ BINOP(base + 13,-base - 12,-base - 10, 0, typ.i64)+ STORE(base + 14, p1,-base - 13, align8, 0)+ LOAD(base + 14, pspace, typ.i64, align8, 0)+ BINOP(base + 15,-base - 14,-base - 11, 0, typ.i64)+ STORE(base + 16, pspace,-base - 15, align8, 0)+ LOAD(base + 16, pcount, typ.i64, align8, 0)+ BINOP(base + 17,-base - 16, C64.1, 0, typ.i64)+ STORE(base + 18, pcount,-base - 17, align8, 0)+ BR(base + 18, block + 2)+ CALL(base + 18, 0, 32768, typ.function.constantseq(length.args + 2, i64), callee, -1, args)+ BR(base + 19, block + 2)+ PHI(base + 19, typ.i64,-base - 7, block,-base - 18, block + 1)+ LOAD(base + 20,-base - 1, typ.i64, align8, 0)+ BINOP(base + 21,-base - 20, C64.1, 1, typ.i64)+ STORE(base + 22,-base - 1,-base - 21, align8, 0)
  Lcode(code.l + c, lmap.l, noblocks.l + 3, regno.l + 21, poppush(args.l, length.args,-base - 19), blocks.l, tailphi.l, loopblock.l)

Function encode(stat5, erecord.stat5)encoding.stat5 export

type statencoding is encoding stat5

type stat5 is record caller:word, callee:word

function hash(s:stat5)int hash.caller.s + hash.callee.s

function =(a:stat5, b:stat5)boolean caller.a = caller.b ∧ callee.a = callee.b

Function profile(caller:word, callee:word)int 
 if caller = callee ∨ caller ="noprofile"_1 
  then 0 
  else encoding.encode(stat5(caller, callee), statencoding)+ 1

function callarc(a:stat5)seq.word [ caller.a, callee.a]

Function profilearcs seq.word @(+, callarc,"", mapping.statencoding)

/type debug is encoding ipair.Lcode

/function hash(i:ipair.Lcode)int index.i

/function =(a:ipair.Lcode, b:ipair.Lcode)boolean index.a = index.b

/function print(p:ipair.Lcode)seq.word let l = value.p {"&br"+ state.l +"regno ="+ toword.regno.l + @(+, toword,"", args.l)+ @(+, printL,"", blocks.l)}

+"code"+ print.code.l }

/function printL(x:Lcode)seq.word @(+, toword,"[", args.x)+"]"

/Function dump seq.word @(+, print,"", mapping.debug)

