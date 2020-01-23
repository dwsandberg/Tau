Module codetemplates

use bitpackedseq.bit

use bits

use blockseq.templatepart

use blockseq.word

use deepcopy.int

use deepcopy.linklists2

use deepcopy.match5

use deepcopy.seq.templatepart

use deepcopy.seq.word

use deepcopy.word

use encoding.match5

use fileio

use intercode

use internalbc

use ipair.linklists2

use llvm

use process.seq.match5

use seq.bit

use seq.int

use seq.llvmtype

use seq.match5

use seq.seq.int

use seq.templatepart

use seq.word

use stdlib

use textio

function wordstype llvmtype array(-1, i64)

Function conststype llvmtype array(-2, i64)

Function type:match5 internaltype export


type match5 is record fullinst:seq.word, length:int, parts:seq.templatepart, action:word, arg:int, index:int

Function addindex(m:match5, i:int)match5 match5(fullinst.m, length.m, parts.m, action.m, arg.m, i)

function match5(fullinst:seq.word, length:int, parts:seq.templatepart, action:word, arg:int)match5 
 match5(fullinst, length, parts, action, arg, 0)

Function length(match5)int export

Function action(match5)word export

Function arg(match5)int export

Function fullinst(m:match5)seq.word export

Function inst(m:match5)word fullinst(m)_1

Function instarg(m:match5)word fullinst(m)_2

function =(a:match5, b:match5)boolean fullinst.a = fullinst.b

function hash(a:match5)int hash.fullinst.a

type ematch5 is encoding match5

Function table seq.match5 
 let t = [ match5("IDXUC"_1, 3, CAST(1, ibcsub1, typ.ptr.i64, 10)+ GEP(2, 1, typ.i64,-1, ibcsub2)+ LOAD(3,-2, typ.i64, align8, 0)), 
  match5(// ? //"Q3FZbuiltinZintZint"_1, 5, CMP2(1, ibcsub1, ibcsub2, 39)+ CAST(2,-1, typ.i64, CASTZEXT)+ CMP2(3, ibcsub1, ibcsub2, 38)+ CAST(4,-3, typ.i64, CASTZEXT)+ BINOP(5,-2,-4, 0, typ.i64)), 
  match5("getaddressZbuiltinZTzseqZint"_1, 2, BINOP(1, ibcsub2, C64.3, // shift left // 7)+ BINOP(2, ibcsub1,-1, 0, typ.i64)), 
  match5("Q3EZbuiltinZintZint"_1, 2, CMP2(1, ibcsub1, ibcsub2, 38)+ CAST(2,-1, typ.i64, CASTZEXT)), 
  match5("notZbuiltinZboolean"_1, 1, BINOP(1, ibcsub1, C64.1, 12, typ.i64)), 
  match5("hashZbuiltinZint"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64], C."HASH", ibcsub1)), 
  // include aborted here so does not show up in profile results match5("abortedZbuiltinZTzprocess"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64, i64], C."abortedZbuiltinZTzprocess",-1, ibcsub1)), Including this as a template causes subtle compile errors // 
   match5("Q3DZbuiltinZintZint"_1, 2, CMP2(1, ibcsub1, ibcsub2, 32)+ CAST(2,-1, typ.i64, CASTZEXT)), 
  match5("EQL"_1, 2, CMP2(1, ibcsub1, ibcsub2, 32)+ CAST(2,-1, typ.i64, CASTZEXT)), 
  match5("Q2DZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 1, typ.i64)), 
  match5("Q2BZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 0, typ.i64)), 
  match5("Q2AZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 2, typ.i64)), 
  match5("Q2FZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 4, typ.i64)), 
  match5("Q2DZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ BINOP(3,-1,-2, 1)+ CAST(4,-3, typ.i64, 11)), 
  match5(// + //"Q2BZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ BINOP(3,-1,-2, 0)+ CAST(4,-3, typ.i64, 11)), 
  match5(// * //"Q2AZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ BINOP(3,-1,-2, 2)+ CAST(4,-3, typ.i64, 11)), 
  match5(// / //"Q2FZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ BINOP(3,-1,-2, 4)+ CAST(4,-3, typ.i64, 11)), 
  match5(// ? //"Q3FZbuiltinZrealZreal"_1, 7, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ CMP2(3,-1,-2, 3)+ CAST(4,-3, typ.i64, CASTZEXT)+ CMP2(5,-1,-2, 2)+ CAST(6,-5, typ.i64, CASTZEXT)+ BINOP(7,-4,-6, 0, typ.i64)), 
  match5("intpartZbuiltinZreal"_1, 2, CAST(1, ibcsub1, typ.double, 11)+ CAST(2,-1, typ.i64, // fptosi double // 4)), 
  match5("torealZbuiltinZint"_1, 2, // sitofp // CAST(1, ibcsub1, typ.double, 6)+ CAST(2,-1, typ.i64, 11)), 
  match5("sqrtZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.sqrt.f64",-1)+ CAST(3,-2, typ.i64, 11)), 
  match5("sinZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.sin.f64",-1)+ CAST(3,-2, typ.i64, 11)), 
  match5("cosZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.cos.f64",-1)+ CAST(3,-2, typ.i64, 11)), 
  match5("Q3CQ3CZbuiltinZbitsZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, // SHL // 7, typ.i64)), 
  match5("Q3EQ3EZbuiltinZbitsZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, // LSHR // 8, typ.i64)), 
  match5("Q02227ZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // AND // 10, typ.i64)), 
  match5("Q02228ZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // OR // 11, typ.i64)), 
  match5("xorZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // XOR // 12, typ.i64)), 
  match5("setfldZbuiltinZTzaddressZT"_1, 3, CAST(1, ibcsub1, typ.ptr.i64, 10)+ STORE(2,-1, ibcsub2, align8, 0)+ GEP(2, 1, typ.i64,-1, C64.1)+ CAST(3,-2, typ.i64, 9)), 
  match5("STKRECORD"_1, 3, ALLOCA(1, typ.ptr.i64, typ.i64, C64.2, 0)+ STORE(2,-1, ibcsub1, align8, 0)+ GEP(2, 1, typ.i64,-1, C64.1)+ STORE(3,-2, ibcsub2, align8, 0)+ CAST(3,-1, typ.i64, CASTPTRTOINT)), 
  match5("CALLIDX"_1, 2, CAST(1, ibcsub1, typ.ptr.function.[ i64, i64, i64, i64], CASTINTTOPTR)+ CALL(2, 0, 32768, typ.function.[ i64, i64, i64, i64],-1, ibcfirstpara2, ibcsub2, ibcsub3)), 
  match5("if 3", 0, empty:seq.templatepart,"SPECIAL"_1, 0), 
  match5("if 4", 0, empty:seq.templatepart,"SPECIAL"_1, 0), 
  match5("MRECORD 2", 0, empty:seq.templatepart,"SPECIAL"_1, 0), 
  match5("THENBLOCK 1", 0, empty:seq.templatepart,"SPECIAL"_1, 0), 
  match5("ELSEBLOCK 1", 0, empty:seq.templatepart,"SPECIAL"_1, 0)]
  let discard = @(+, addit, 0, t)
  t

function addit(m:match5)int findindex(ematch5,m)

function match5(inst:word, length:int, b:internalbc)match5 
 let parts = getparts.b 
  let nopara = @(max, parano, 0, parts)
  match5([ inst, toword.nopara], length, parts,"TEMPLATE"_1, nopara)

type temppair is record templates:seq.match5, consts:linklists2

Function templates(temppair)seq.match5 export

Function consts(temppair)linklists2 export

Function inittemppair temppair temppair(empty:seq.match5, createlinkedlists)

Function buildtemplates(p:temppair, fullinst:seq.word)temppair 
 let s = templates.p 
  let lastconsts = consts.p 
  // let z10 = createfile("stat.txt", [ fullinst]+"start")// 
  let a = match5(fullinst, 0, empty:seq.templatepart,"NOTFOUND"_1, 0)
  let b = findencode(ematch5,a)
  if length.b = 0 
  then let inst = fullinst_1 
   let instarg = fullinst_2 
   let m = if inst ="FREF"_1 
    then temppair(s + match5(fullinst, 0, empty:seq.templatepart,"ACTARG"_1, C(i64, [ CONSTCECAST, 9, typ.ptr.getftype.instarg, C.instarg])), lastconsts)
    else if inst ="LIT"_1 
    then temppair(s + match5(fullinst, 0, empty:seq.templatepart,"ACTARG"_1, C64.toint.instarg), lastconsts)
    else if inst ="LOCAL"_1 
    then temppair(s + match5(fullinst, 0, empty:seq.templatepart,"LOCAL"_1, toint.instarg), lastconsts)
    else if inst in"PARAM FIRSTVAR"
    then temppair(s + match5(fullinst, 0, empty:seq.templatepart,"ACTARG"_1, toint.instarg), lastconsts)
    else if inst in"CONTINUE FINISHLOOP LOOPBLOCK RECORD SET DEFINE MSET"
    then temppair(s + match5(fullinst, 0, empty:seq.templatepart,"SPECIAL"_1, 0), lastconsts)
    else if inst in"CONSTANT WORDS"
    then let tt = if inst ="CONSTANT"_1 
      then addconst(lastconsts, fullinst)
      else addwordseq(lastconsts, subseq(fullinst, 3, length.fullinst))
     let newcode = GEP(1, 1, typ.conststype, C."list", C64.0, C64(index.tt + 1))+ CAST(2,-1, typ.i64, 9)
     let r = match5(fullinst, 2, getparts.newcode,"TEMPLATE"_1, 0)
     temppair(s + r, value.tt)
    else if inst ="WORD"_1 
    then let discard = registerword.instarg 
     temppair(s + match5(fullinst, 0, empty:seq.templatepart,"ACTARG"_1, C64.hash.instarg), lastconsts)
    else let noargs = toint.instarg 
    let newcode = CALLSTART(1, 0, 32768, typ.function.constantseq(noargs + 2, i64), C.[ inst], noargs + 1)
    temppair(s + match5(fullinst, 1, getparts.newcode,"CALL"_1, noargs), lastconsts)
   let discard = encode(ematch5,last.templates.m)
   m 
  else // already have a match5 // temppair(s + b_1, lastconsts)

/Function deepcopy2(m:match5)match5 let y0 = deepcopy.fullinst.m let y1 = deepcopy.length.m let y2 = deepcopy.parts.m let y3 = deepcopy.action.m let y4 = deepcopy.arg.m let y5 = deepcopy.consts.m match5(y0, y1, y2, y3, y4, y5)

/Function checkmap(s:seq.match5)seq.word @(+, hjk,"", s)

/function hjk(m:match5)seq.word [ inst.m, toword.length.a.consts.m]

function ematch5 erecord.match5 export

Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc 
 let args = if inst.t in"WORD CONSTANT"∨ action.t ="CALL"_1 
   then empty:seq.int 
   else subseq(argstack, length.argstack - toint.instarg.t + 1, length.argstack)
  processtemplate(parts.t, deltaoffset, args)

Function CASTZEXT int 1

Function CASTTRUNC int 0

Function CASTPTRTOINT int 9

Function CASTINTTOPTR int 10

type pp is record idx:int, val:int

function getvbr(a:seq.bit, idx:int, size:int)pp getvbr(a, size, bits.0, 0, idx, 0)

function getvbr(a:seq.bit, size:int, val:bits, nobits:int, idx:int, i:int)pp 
 let b = toint(a_(idx + i))
  if i = size - 1 
  then if b = 0 then pp(idx + size, toint.val)else getvbr(a, size, val, nobits, idx + size, 0)
  else getvbr(a, size, bits.b << nobits ∨ val, nobits + 1, idx, i + 1)

function getinfo(b:seq.bit, noargs:int, r:seq.int, idx:int, recs:seq.seq.int, abbrvlen:int)seq.seq.int 
 if length.r > 0 
  then // working on record // 
   if noargs = 0 
   then getinfo(b, 0, empty:seq.int, idx, recs + r, abbrvlen)
   else let next = getvbr(b, idx, 6)
   getinfo(b, noargs - 1, r + val.next, idx.next, recs, abbrvlen)
  else let t = getvbr(b, abbrvlen, bits.0, 0, idx, 0)
  if val.t = 3 
  then // record // 
   let inst = getvbr(b, idx.t, 6)
   let args = getvbr(b, idx.inst, 6)
   getinfo(b, val.args, [ val.inst], idx.args, recs, abbrvlen)
  else recs

function astext2(a:seq.int)seq.word {"["+ @(+, toword,"", a)+"]"}

Function astext(a:bitpackedseq.bit)seq.word 
 // @(+, toword,"", @(+, toint, empty:seq.int, toseq.a))+"&br"+ // 
  let recs = getinfo(toseq.a, 0, empty:seq.int, 1, empty:seq.seq.int, 4)
  @(seperator."&br", astext2,"", recs)

