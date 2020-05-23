#!/usr/local/bin/tau


run mylib testnew

Module codegennew

use seq.int

use ipair.Lcode2

use seq.Lcode2

use UTF8

use bitpackedseq.bit

use seq.seq.bits

use seq.bits

use bits

use codetemplates

use seq.fsignrep

use seq.seq.seq.int

use seq.seq.int


use ipair.internalbc

use seq.internalbc

use internalbc

use libscope


use llvm

use seq.llvmconst

use otherseq.llvmtype

use seq.llvmtype

use seq.localmap

use seq.match5

use stacktrace

use encoding.stat5

use seq.stat5

use stdlib

use textio

use seq.match5


use persistant

use seq.sig

function funcdec(m:match5)seq.int
 // let discard = C.mangledname.f //
  let nopara=arg.m
  [ MODULECODEFUNCTION, typ.function.constantseq(nopara + 2, i64), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  
  

Function codegen(fs2:intercode, thename:word)seq.bits
 let symlist ="libname initlib5 list profcounts profclocks profspace profrefs profstat spacecount" + merge.[ thename,"$profileresult"_1] + "init22 "
 + merge."llvm.sqrt.f64"
 + merge."llvm.sin.f64"
 + merge."llvm.cos.f64"
      let match5map = match5map(fs2,symlist)
    // assert false report fullinst.last.match5map //
  let libmods2=arg.last.match5map
      // let zx2c = createfile("stat.txt", ["in codegen0.3"])//
     // assert false report checkmap.match5map //
     let defines2=@(+, _(match5map), empty:seq.match5, defines.fs2)
     let bodies = @(+, addfuncdef(match5map), empty:seq.internalbc, defines2)
     let profilearcs2 = profilearcs
     let noprofileslots = length.profilearcs2 / 2
      // let libsyms = @(+, tolibsym(coding.fs, codes.fs), empty:seq.libsym, defines.fs)//
      let profilearcs3 = addwordseq2( profilearcs2)
      let liblib = addliblib( [thename],  libmods2)
       let x = C(array(4, i64)
      , [ AGGREGATE, profilearcs3, C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profcounts"]), 
                                   C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profclocks"]), 
                                   C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profspace"])])
       let libnametype = array(length.decodeword.thename + 1, i8)
      let libnameptr = C(ptr.i8, [ CONSTGEP, typ.libnametype, typ.ptr.libnametype, C."libname", typ.i32, C32.0, typ.i32, C32.0])
      let bodytxts = [ BLOCKCOUNT(1, 1)
      + RET(1, C(i64, [ CONSTCECAST, 9, typ.ptr.array(4, i64), C."profstat"]))
      , BLOCKCOUNT(1, 1)
      + CALL(1, 0, 32768, typ.function.[ i64, ptr.i8,   i64], C."initlib5", libnameptr,  liblib )
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
                 let data = constdata                                   
      let adjust = [ 0, // consttype // length.data + 2, // profiletype // noprofileslots + 2 + 3]
      let deflist = [ // libname //
      [ MODULECODEGLOBALVAR, typ.libnametype, 2, C(libnametype, [ CONSTDATA] + tointseq.decodeword.thename + 0) + 1, 3, align4, 0]
      , // lnitlib 5 //
      [ MODULECODEFUNCTION, typ.function.[ i64, ptr.i8, i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // list // [ MODULECODEGLOBALVAR, typ.conststype, 2,    C(conststype, [ AGGREGATE]  +  data)+ 1, 3, align8 + 1, 0]
      , // profcounts // [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL]) + 1, 3, align8 + 1, 0]
      , // profclocks // [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL]) + 1, 3, align8 + 1, 0]
      , // profspace // [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL]) + 1, 3, align8 + 1, 0]
      , // profrefs // [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL]) + 1, 3, align8 + 1, 0]
      , // profstat // [ MODULECODEGLOBALVAR, typ.array(4, i64), 2, x + 1, 3, align8 + 1, 0]
      , // spacecount // [ MODULECODEGLOBALVAR, typ.i64, 2, 0, 0, align8 + 1, 0]
      , // profileresult // [ MODULECODEFUNCTION, typ.function.[ i64], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // init22 // [ MODULECODEFUNCTION, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // llvm.sqrt.f64 // [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // llvm.sin.f64 // [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      , // llvm.cos.f64 // [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
      + @(+, funcdec, empty:seq.seq.int, defines2)
       llvm(deflist, bodytxts, adjust(typerecords, adjust, 1))

use funcsig

 
 function addfuncdef(match5map:seq.match5,  m:match5)internalbc
 //   let hh=process.subaddfuncdef(match5map,m)
    assert not.aborted.hh report "fail get"+ inst.m+ message.hh +"&br"+print.code.m
    result.hh
use process.internalbc
function subaddfuncdef(match5map:seq.match5,  m:match5)internalbc //
 let options=options(match5map,m)
 let code= if length.options > 0  then  
   assert  "PROFILE"_1 in options  report "PROFILE PROBLEM"
  // assert  inst.m in "compilelib2Zmain2Zword subcompilelibZmain2Zword
    bbbfirstZpass2newZsymbolsetZseqzQ2EzwordZseqzQ2EzwordZprgZmytype
    pass2newZpass2newZsymbolsetZseqzQ2EzfirstpassZsymbolset
    pass1Zpass1ZseqzQ2EzseqzQ2EzseqzQ2EzwordZseqzQ2EzwordZsymbolsetZsetzQ2Ezfirstpass
    bindZpass1ZsymbolsetZsetzQ2EzfirstpassZsymbolsetZfirstpass
    bind2Zpass1ZsymbolsetZsetzQ2EzsymbolZsymbolsetZsymbol" report  "P"+inst.m //
   subseq(code.m,2,length.code.m-1) else code.m
 let mangledname= inst.m
 let nopara=arg.m
    let l = Lcode2(emptyinternalbc, paramap(nopara,empty:seq.localmap), 1, nopara + 1, empty:stack.int, empty:stack.Lcode2)
 let g5 = if "PROFILE"_1 in options then 
   // assert false report  options(match5map,m) // mangledname else"noprofile"_1
 let r = @(processnext.g5,_.match5map, l, (code))
  BLOCKCOUNT(1, noblocks.r) + code.r + RET(regno.r + 1, top.args.r)

type Lcode2 is record code:internalbc, lmap:seq.localmap, noblocks:int, regno:int, args:stack.int,
 blocks:stack.Lcode2
 
 

use stack.Lcode2

use stack.int


type localmap is record localno:int, regno:int

function paramap( i:int ,result:seq.localmap) seq.localmap
if i=0 then result else 
paramap(i-1,result+localmap(i, -i-1))

function length(s:stack.int) int length.toseq.s

use otherseq.Lcode2

function processnext(profile:word, l:Lcode2, m:match5)Lcode2
 let inst = inst.m
  let action = action.m
  if action = "CALL"_1 then
  let noargs = arg.m
   let args = top(args.l, noargs)
    if  profile = "noprofile"_1 ∨ profile = inst then
    let c = usetemplate(m, regno.l, empty:seq.int) + CALLFINISH(regno.l + 1, [ -1] + args)
      Lcode2(code.l + c, lmap.l, noblocks.l, regno.l + 1, push(pop(args.l, noargs), -(regno.l + 1)), blocks.l)
    else
      // if callee ="PROCESS2"_1 then let discard = if noargs = 1 ∧ nosons(t_1)= 5 then profile(profile, arg.label(t_1_3))else Case of CONST insteand of record as arg 0 addcode(l.sons, c, -(regno.l.sons + 1), 1)else //
     profilecall(profiletype, l, args, C.[ inst], profile(profile, inst))
  else if action = "ACTARG"_1 then 
  Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, arg.m), blocks.l)
  else if action = "LOCAL"_1 then 
   Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, getloc(lmap.l, arg.m, 1)), blocks.l)
  else if action = "TEMPLATE"_1 then
  let newcode = usetemplate(m, regno.l, toseq.args.l)
     let noargs = arg.m
     Lcode2(code.l + newcode, lmap.l, noblocks.l, regno.l + length.m, push(pop(args.l, noargs), -(regno.l + length.m)), blocks.l)
  else
   assert action = "SPECIAL"_1 report"UNKNOWN ACTION" + action
    if inst in "EXITBLOCK" then
           assert    length.toseq.args.l > 0 report "fail 5e"
     let exitblock=       Lcode2(code.l, lmap.l, noblocks.l , regno.l, push(args.l,0), blocks.l)
    Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l, empty:stack.int, push(blocks.l,exitblock))
    else if inst in "BR"  then
           assert    length.toseq.args.l > 2 report "fail 5b"
       let cond=
        let newcode = CAST(regno.l + 1, top(args.l,arg.m)_1, typ.i1, CASTTRUNC)
        Lcode2(code.l + newcode, lmap.l, noblocks.l, regno.l + 1, push(args.l,1), blocks.l)
      Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l + 1, empty:stack.int, push(blocks.l,cond))
    else if inst in "BLOCK"  then
     let no=arg.m 
      let blks= top(blocks.l,no)
      assert length.blks=no report "XXXXXX arg"+profile
       let rblk = processblk(blks,1,empty:seq.localmap,BR(regno.l, noblocks.l- 1)) 
       //       assert length.phi.rblk > 3 report  "phi"+@(+,toword,"",phi.rblk) //
        let firstblkargs=args.blks_1
        let kind=top.firstblkargs
        let popno=if kind=1 then 
          // stack from top is kind,br label,br label, cond exp //
          4
        else 
         assert  top.firstblkargs=2 report "Code Gen--not expecting first blk kind"+toword.kind+profile
           // stack from top is  kind,noexps,firstvar,  exps //
            top.pop.firstblkargs + 3
         if length.phi.rblk=2 &and false then
          Lcode2(code.rblk, lmap.l, noblocks.l , regno.l,  push(pop(firstblkargs, popno),(phi.rblk)_2), pop(blocks.l, no))  
         else 
       let newstack =push(pop(firstblkargs, popno)  , -(regno.l + 1))
      let newcode=code.rblk+phiinst(regno.last.blks, typ.i64, phi.rblk,1)
      Lcode2(newcode, lmap.l, noblocks.l , regno.l + 1,  newstack, pop(blocks.l, no))
    else if inst = "DEFINE"_1 then
    Lcode2(code.l,  [localmap(arg.m, top.args.l)]+lmap.l, noblocks.l, regno.l, pop(args.l,1),  blocks.l)
    else if inst = "SET"_1 then l
     else if inst = "LOOPBLOCK"_1 then
     let varcount = arg.m - 1
     let firstvar = constvalue.top.args.l
     let bodymap = @(addloopmapentry(firstvar, regno.l), identity,lmap.l, arithseq(varcount, 1, 1))
     let exitblock=       Lcode2(code.l, lmap.l, noblocks.l , regno.l, push(push(args.l,varcount),2), blocks.l)
    Lcode2(emptyinternalbc, bodymap, noblocks.l + 1, regno.l+ varcount, empty:stack.int,  push( blocks.l,exitblock) )  
    else  if inst = "CONTINUE"_1 then
    let exitblock=       Lcode2(code.l, lmap.l, noblocks.l , regno.l, push(args.l,3), blocks.l)
    Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l, empty:stack.int, push(blocks.l,exitblock))  
    else 
     assert inst = "RECORD"_1 report"code gen SPECIAL" + inst
     let noargs = arg.m
     let args = top(args.l, noargs)
     let newcode = CALL(regno.l + 1, 0, 32768, typ.function.[ i64, i64, i64], C."allocatespaceZbuiltinZint", -1, C64.noargs)
     + CAST(regno.l + 2, -(regno.l + 1), typ.ptr.i64, CASTINTTOPTR)
      Lcode2(value.@(setnextfld, identity, ipair(regno.l + 2, code.l + newcode), args), lmap.l, noblocks.l, regno.l + 2 + noargs, push(pop(args.l, noargs), -(regno.l + 1)), blocks.l)


function processblk(blks:seq.Lcode2,i:int, map:seq.localmap,exitbr:internalbc) processblkresult
         processblk(blks,1,exitbr,emptyinternalbc,1,empty:seq.int,empty:seq.int) 
         
function kind(a:Lcode2) word toword.(top.args.a) 

type processblkresult  is record code:internalbc,phi:seq.int
     
function processblk(    blks:seq.Lcode2,i:int, exitbr:internalbc,code:internalbc,varcount:int,phi:seq.int,tailphi:seq.int) processblkresult
    if i > length.blks then
        let firstblk=blks_1
        let code1= if top.args.firstblk= //  loopblock // 2 then
            let noargs = top.pop.args.firstblk
                     //    assert false report "JKL"+    @(+,toword,"",  tailphi ) //
            code.firstblk+BR(regno.firstblk + 1, noblocks.firstblk) + phiinst(regno.firstblk, typ.i64, tailphi, noargs)+code
         else code
         //  code1 + phiinst(regno.last.blks, typ.i64, phi,varcount)   //
         processblkresult(code1,phi)
       else let l=blks_i
         assert length.toseq.args.l > 0 report "XXXXXX"+toword.length.blks+toword.i
         let kind=top.args.l
          if kind=0 then // exit block //
           assert length.args.l &ge 2 report "check l"
           let t=top(args.l, varcount+1)
           let t2=subseq(t,1,varcount)
           processblk(blks,i+1,exitbr, code+code.l+exitbr,varcount,phi+ [ noblocks.l - 1] +  t2,tailphi )
        else if kind=2 then // LOOPBLOCK //
           //   assert false report "L"+@(+,toword,"",args.l) //
          let noargs = top.pop.args.l
        //  let firstvar = top.pop.args.l //
           let newtailphi = [ noblocks.l - 1] + top(pop.pop.pop.args.l,noargs)
         processblk(blks,i+1,exitbr,    code, varcount,phi,newtailphi) 
        else if kind=3 then // CONTINUE //
           assert kind.blks_1 ="2"_1   report "incorrect format on block"+@(+,kind,"",         blks)  
           let noargs = top.pop.args.blks_1
                 //  assert false report "C"+@(+,toword,"",args.blks_1) +"noargs:"+toword.noargs //
          let newtailphi = tailphi + [ noblocks.l - 1]+  top( pop.args.l,noargs)
          let newcode=BR(regno.l, noblocks.blks_1)
          processblk(blks,i+1,exitbr,    code+code.l+ newcode, varcount,phi,newtailphi) 
        else
          // br block //
           assert kind=1 report "expecting br block"+toword.kind
                assert length.args.l > 3 report "check m"+@(+,toword, "",[kind]+toseq.args.l)
                 let args=top(args.l,4) 
                assert between(constvalue(args_2)- 1,1,length.blks) &and 
                between(constvalue(args_3)- 1,1,length.blks) report "check mm"
           let newcode=BR(regno.l + 1, noblocks.blks_(constvalue(args_2)- 1 ),   noblocks.blks_(constvalue(args_3)- 1 ),-regno.l)
         processblk(blks,i+1,exitbr,    code+code.l+ newcode, varcount,phi,tailphi) 
    
 8XAT6qVV3qHJ9uLsowg2NmUa  

Function setnextfld(p:ipair.internalbc, arg:int)ipair.internalbc
 let regno = index.p
  ipair(regno + 1, value.p + STORE(regno + 1, - regno, arg, align8, 0)
  + GEP(regno + 1, 1, typ.i64, - regno, C64.1))

function getloc(l:seq.localmap, localno:int, i:int)int
 if localno.l_i = localno then regno.l_i else getloc(l, localno, i + 1)

function addloopmapentry(baselocal:int, regbase:int,l:seq.localmap,i:int) seq.localmap
        [localmap(baselocal + i - 1, - regbase - i)]+l
 
function profilecall(profiletype2:llvmtype, l:Lcode2, args:seq.int, callee:int, idx:int)Lcode2
 let base = regno.l
 let block = noblocks.l
 let p1 = C(ptr.i64, [ CONSTGEP, typ.profiletype2, typ.ptr.profiletype2, C."profclocks", typ.i32, C32.0, typ.i64, C64.idx])
 let pspace = C(ptr.i64, [ CONSTGEP, typ.profiletype2, typ.ptr.profiletype2, C."profspace", typ.i32, C32.0, typ.i64, C64.idx])
 let pcount = C(ptr.i64, [ CONSTGEP, typ.profiletype2, typ.ptr.profiletype2, C."profcounts", typ.i32, C32.0, typ.i64, C64.idx])
 let c = GEP(base + 1, 1, typ.profiletype2, C."profrefs", C64.0, C64.idx)
 + LOAD(base + 2, - base - 1, typ.i64, align8, 0)
 + BINOP(base + 3, - base - 2, C64.1, 0, typ.i64)
 + STORE(base + 4, - base - 1, - base - 3, align8, 0)
 + CMP2(base + 4, - base - 2, C64.0, 32)
 + BR(base + 5, block, block + 1, - base - 4)
 + CALL(base + 5, 0, 32768, typ.function.[ i64], C."clock")
 + LOAD(base + 6, C."spacecount", typ.i64, align8, 0)
 + CALL(base + 7, 0, 32768, typ.function.constantseq(length.args + 2, i64), callee, -1, args)
 + CALL(base + 8, 0, 32768, typ.function.[ i64], C."clock")
 + LOAD(base + 9, C."spacecount", typ.i64, align8, 0)
 + BINOP(base + 10, - base - 8, - base - 5, 1, typ.i64)
 + BINOP(base + 11, - base - 9, - base - 6, 1, typ.i64)
 + LOAD(base + 12, p1, typ.i64, align8, 0)
 + BINOP(base + 13, - base - 12, - base - 10, 0, typ.i64)
 + STORE(base + 14, p1, - base - 13, align8, 0)
 + LOAD(base + 14, pspace, typ.i64, align8, 0)
 + BINOP(base + 15, - base - 14, - base - 11, 0, typ.i64)
 + STORE(base + 16, pspace, - base - 15, align8, 0)
 + LOAD(base + 16, pcount, typ.i64, align8, 0)
 + BINOP(base + 17, - base - 16, C64.1, 0, typ.i64)
 + STORE(base + 18, pcount, - base - 17, align8, 0)
 + BR(base + 18, block + 2)
 + CALL(base + 18, 0, 32768, typ.function.constantseq(length.args + 2, i64), callee, -1, args)
 + BR(base + 19, block + 2)
 + PHI(base + 19, typ.i64, - base - 7, block, - base - 18, block + 1)
 + LOAD(base + 20, - base - 1, typ.i64, align8, 0)
 + BINOP(base + 21, - base - 20, C64.1, 1, typ.i64)
 + STORE(base + 22, - base - 1, - base - 21, align8, 0)
  Lcode2(code.l + c, lmap.l, noblocks.l + 3, regno.l + 21, push(pop(args.l, length.args), - base - 19), blocks.l)

Function encode(erecord.stat5, stat5)encoding.stat5 export

type statencoding is encoding stat5

type stat5 is record caller:word, callee:word 



function assignencoding(l:int, a:stat5) int l+1

function hash(s:stat5)int abs(hash.caller.s + hash.callee.s)

function =(a:stat5, b:stat5)boolean caller.a = caller.b ∧ callee.a = callee.b

Function profile(caller:word, callee:word)int
 if caller = callee ∨ caller = "noprofile"_1 then 0
 else valueofencoding.encode(statencoding, stat5(caller, callee)) + 1

function callarc(a:stat5)seq.word [ caller.a, callee.a]

Function profilearcs seq.word @(+, callarc,"", orderadded.statencoding)

/type debug is encoding ipair.Lcode2

/function hash(i:ipair.Lcode2)int index.i

/function =(a:ipair.Lcode2, b:ipair.Lcode2)boolean index.a = index.b

/function print(p:ipair.Lcode2)seq.word let l = value.p {"
&br"+ state.l +"regno ="+ toword.regno.l + @(+, toword,"", args.l)+ @(+, printL,"", blocks.l)}

+"code"+ print.code.l }

/function printL(x:Lcode2)seq.word @(+, toword,"[", args.x)+"]"

/Function dump seq.word @(+, print,"", mapping.debug)