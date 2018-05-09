module altgen

use buildtree

use codetemplates

use internalbc

use ipair.Lcode

use ipair.internalbc

use llvm

use persistant

use seq.Lcode

use seq.encoding.llvmtype

use seq.int

use seq.internalbc

use seq.ipair.Lcode

use seq.llvmconst

use seq.localmap

use seq.seq.int

use seq.tree.cnode

use stdlib

use tree.cnode

use seq.tree.seq.word 

use tree.seq.word

use ipair.linklists2

type altresult is record body:internalbc, l:linklists2

Function body(altresult)internalbc export

Function l(altresult)linklists2 export

Function altgen(f:func, consts:linklists2, lib:word, pwordstype:encoding.llvmtype, pconststype:encoding.llvmtype, pprofiletype:encoding.llvmtype, tab:seq.match5)altresult 
 let paraadj =-nopara.f - 2 
  let l = Lcode("0"_1, emptyinternalbc, consts, empty:seq.localmap, 1, nopara.f + 1, empty:seq.int, 
  empty:seq.Lcode, empty:seq.int, 0,empty:seq.tree(seq.word))
  let g5 = geninfo6(lib, pwordstype, pconststype, pprofiletype, mangledname.f, paraadj, tab,if "PROFILE"_1 in flags.f then mangledname.f else "noprofile"_1 )
  // assert false report prep(codetree.f)+"^^"+ print.codetree.f // 
  let r = @(processnext.g5, identity, l, prep.codetree.f)
  altresult(BLOCKCOUNT(1, noblocks.r)+ code.r + RET(regno.r + 1, last.args.r), lst.r)
 

type Lcode is record state:word, code:internalbc, lst:linklists2, lmap:seq.localmap, noblocks:int, regno:int, args:seq.int, blocks:seq.Lcode, tailphi:seq.int, loopblock:int, const:seq.tree(seq.word)

type localmap is record localno:int, regno:int

type geninfo6 is record lib:word, wordstype:encoding.llvmtype, conststype:encoding.llvmtype, profiletype:encoding.llvmtype, funcname:word, paraAdjustment:int, tab:seq.match5, profile:word

function push(l:Lcode, code:internalbc, regno:int, arg:int)Lcode 
 Lcode("0"_1, code, lst.l, lmap.l, noblocks.l, regno, args.l + [ arg], blocks.l, tailphi.l, loopblock.l,const.l)

function push(l:Lcode, arg:int)Lcode 
 Lcode("0"_1, code.l, lst.l, lmap.l, noblocks.l, regno.l, args.l + [ arg], blocks.l, tailphi.l, loopblock.l,const.l)


function processnext(lib:geninfo6, l:Lcode, next:word)Lcode 
 // let descard = encode(ipair(length.mapping.debug, l), debug)// 
  let state = state.l 
  let instarg = next 
  if state ="0"_1 
  then Lcode(next, code.l, lst.l, lmap.l, noblocks.l, regno.l, args.l, blocks.l, tailphi.l, loopblock.l,const.l)
  else if state = "CLIT"_1 then
     Lcode("0"_1, code.l, lst.l, lmap.l, noblocks.l, regno.l, args.l, blocks.l, tailphi.l, loopblock.l,
      const.l+tree("LIT"+next))
  else if state = "CFREF"_1 then
       Lcode("0"_1, code.l, lst.l, lmap.l, noblocks.l, regno.l, args.l, blocks.l, tailphi.l, loopblock.l,
      const.l+tree("FREF"+next))
  else if state = "CWORD"_1 then
        Lcode("0"_1, code.l, lst.l, lmap.l, noblocks.l, regno.l, args.l, blocks.l, tailphi.l, loopblock.l,
      const.l+tree("WORD"+next))
  else if state = "CRECORD"_1 then 
       let nosons=toint.next
       Lcode("0"_1, code.l, lst.l, lmap.l, noblocks.l, regno.l, args.l, blocks.l, tailphi.l, loopblock.l,
      subseq(const.l,1,length.const.l-nosons )+tree("CRECORD"+next,subseq(const.l,length.const.l-nosons+1,length.const.l)))
  else if state = "CONSTANT"_1 then
     let tt =addconst(lst.l,(const.l)_1)
        let newcode= GEP(regno.l+1, 1, typ.conststype, C."list", C64.0,  C64(index.tt + 1))
        + CAST(regno.l+2, -(regno.l+1), typ.i64, 9)
       Lcode("0"_1, code.l+newcode, value.tt, lmap.l, noblocks.l, regno.l+2, args.l+[-(regno.l + 2)], blocks.l, tailphi.l,
        loopblock.l,empty:seq.tree(seq.word))
  else if state ="PARA"_1 
  then push(l, toint.instarg + paraAdjustment.lib)
  else if state ="LOCAL"_1 
  then push(l, getloc(lmap.l, toint.instarg, 1))
  else if state ="LIT"_1 
  then push(l, C64.toint.instarg)
  else if state ="FREF"_1 
  then push(l, C(i64, [ CONSTCECAST, 9, typ.ptr.getftype.next, C.next]))
  else // if state ="CRECORD"_1 then let tt = addconst(lst.l, casttree.t)let newcode = usetemplate(regno.l, CONSTtemplate, C64(index.tt + 1), 0)Lcode("0"_1, code.l + newcode, lst.value.tt, lmap.l, noblocks.l, regno.l + 2, [-(regno.l + 2)]+ args.l, blocks.l)else // 
  if state ="WORD"_1 
  then let a = C(ptr.i64, [ CONSTGEP, 
   typ.wordstype.lib, 
   typ.ptr.wordstype.lib, 
   C."words", 
   typ.i32, 
   C32.0, 
   typ.i64, 
   C64(word33.next + 1)])
   let newcode = usetemplate(regno.l, WORDtemplate, a, 0)
   push(l, code.l + newcode, regno.l + 1,-(regno.l + 1))
  else if state ="DEFINE"_1 
  then Lcode("0"_1, code.l, lst.l, lmap.l + localmap(toint.instarg, last.args.l), noblocks.l, regno.l, subseq(args.l, 1, length.args.l - 1), [l]+blocks.l, tailphi.l, loopblock.l,const.l)
  else if state ="SET"_1 
   then Lcode("0"_1, code.l, lst.l, lmap.(blocks.l)_1 , noblocks.l, regno.l, args.l, subseq(blocks.l,2,length.blocks.l), tailphi.l, loopblock.l,const.l)
  else if state ="ELSEBLOCK"_1 then
  // assert args.l=[2, -8 ]report  @(+,toword,"args",args.l) //
    Lcode("0"_1, emptyinternalbc, lst.l, lmap.l, noblocks.l + 1, regno.l, empty:seq.int, [ l]+ blocks.l, tailphi.l, loopblock.l,const.l)
  else if state="THENBLOCK"_1 then
   let newcode = CAST(regno.l + 1, last.args.l, typ.i1, CASTTRUNC)
     let cond= Lcode("0"_1, code.l + newcode, lst.l, lmap.l, noblocks.l, regno.l + 1, poppush(args.l, 1,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l,const.l)
    Lcode("0"_1, emptyinternalbc, lst.l, lmap.l, noblocks.l + 1, regno.l+1, empty:seq.int, [cond]+ blocks.l, tailphi.l, loopblock.l,const.l)
  else if state ="if"_1 
  then let exp3 = l 
   let exp1 = blocks(l)_2 
   let exp2 = blocks(l)_1 
   // assert false report [ toword.last.args.exp1, toword.last.args.exp2, toword.last.args.exp3]// 
   let br = BR(regno.exp1 + 1, noblocks.exp1, noblocks.exp2, last.args.exp1)
   let br1 = BR(regno.exp3, noblocks.exp3)
   let phi = PHI(regno.exp3 + 1, typ.i64, last.args.exp2, noblocks.exp2 - 1, last.args.exp3, noblocks.exp3 - 1)
   let newcode = code.exp1 + br + code.exp2 + br1 + code.exp3 + br1 + phi 
   Lcode("0"_1, newcode, lst.l, lmap.l, noblocks.l + 1, regno.exp3 + 1, poppush(args.exp1, 1,-(regno.exp3 + 1)), subseq(blocks.l, 3, length.blocks.l), tailphi.l, loopblock.l,const.l)
  else if state ="FIRSTVAR"_1 
  then push(l, toint.next)
  else if state ="LOOPBLOCK"_1 
  then let varcount = toint.next - 1 
   let firstvar = last.args.l 
   let bodymap = @(+, loopmapentry(firstvar, regno.l), lmap.l, arithseq(varcount, 1, 1))
   let tailphi = [ noblocks.l-1]+ subseq(args.l, length.args.l  - varcount , length.args.l - 1)
   let k = Lcode("0"_1, code.l, lst.l,lmap.l, noblocks.l , regno.l , subseq(args.l,1 ,length.args.l  - varcount -1),
    blocks.l, tailphi.l, loopblock.l,const.l)
   Lcode("0"_1, emptyinternalbc, lst.l, bodymap, noblocks.l + 1, regno.l + varcount, [ varcount], [ k]+ blocks.l, tailphi, noblocks.l,const.l)
  else if state ="CALLIDX"_1 
  then let exp1 = (args.l)_(length.args.l-2)
   let exp2 =  (args.l)_(length.args.l-1)
   let exp3 =  (args.l)_(length.args.l) 
     let newcode = CAST(regno.l + 1, exp1, typ.ptr.function.[ i64, i64, i64, i64], CASTINTTOPTR)+ 
                 CALL(regno.l + 2, 0, 32768, typ.function.[ i64, i64, i64, i64],-(regno.l + 1), -1, exp2, exp3)  
  Lcode("0"_1, code.l + newcode, lst.l, lmap.l, noblocks.l, regno.l + 2, poppush(args.l, 3,-(regno.l + 2)), blocks.l, tailphi.l, 
  loopblock.l,const.l) 
  else if state ="FINISHLOOP"_1 
  then let b = blocks(l)_1 
   let varcount =  args(l)_(length.args.l - 1) 
   // assert false report"K"+ toword.varcount + @(+, toword,"t", tailphi.l)// 
   let newcode = BR(regno.b + 1, loopblock.l)+ phiinst(regno.b, typ.i64, tailphi.l, varcount)+ code.l 
   let x = Lcode("0"_1, code.b + newcode, lst.l, lmap.b, noblocks.l, regno.l, args.b+[last.args.l], subseq(blocks.l, 2, length.blocks.l), tailphi.b, loopblock.b,const.l)
   // assert true report"XX"+ toword.varcount + @(+, toword,"phi", tailphi.l) //
   x 
  else if state ="CONTINUE"_1 
  then let noargs = toint.next 
   let block = noblocks.l 
   let tailphi = tailphi.l + [ block - 1]+ subseq(args.l, length.args.l - noargs + 1, length.args.l)
   Lcode("0"_1, code.l + BR(regno.l, loopblock.l), lst.l, lmap.l, block + 1, regno.l, poppush(args.l, noargs, -1), blocks.l, tailphi, loopblock.l,const.l)
  else let noargs = toint.instarg 
  let template = lookup(tab.lib, state)
  if length.template > 0 
  then 
     let e1 = if noargs > 0 then args(l)_(length.args.l + 1 - noargs)else 0
     let newcode = usetemplate(regno.l, template.template, e1, if noargs > 1 then args(l)_length.args.l else e1)
   Lcode("0"_1, code.l + newcode, lst.l, lmap.l, noblocks.l, regno.l + length.template, poppush(args.l, noargs,-(regno.l + length.template)), blocks.l, tailphi.l, loopblock.l,const.l)
  else  
  if state in"RECORD"
  then let nosons = toint.next 
   let newcode = usetemplate(regno.l, RECORDtemplate, C64.nosons, -1)
   assert length.top(args.l, nosons)= nosons report"RECORD PROBLEM"+ next 
   Lcode("0"_1, value.@(setnextfld, identity, ipair(regno.l + 2, code.l + newcode), top(args.l, nosons)), lst.l, lmap.l, noblocks.l, regno.l + 2 + nosons, poppush(args.l, nosons,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l,const.l)
  else if state in"STKRECORD"
  then let nosons = toint.next 
    let newcode=value.@(setnextfld, identity, ipair(regno.l + 1, code.l 
    + ALLOCA(regno.l+1,typ.ptr.i64,typ.i64,C64.nosons,0)), top(args.l, nosons))
    +CAST(regno.l+2+nosons, -(regno.l+1), typ.i64, CASTPTRTOINT)
    Lcode("0"_1, newcode
    , lst.l, lmap.l, noblocks.l, regno.l + 2 + nosons, poppush(args.l, nosons,-(regno.l + 2 + nosons)), 
    blocks.l, tailphi.l, loopblock.l,const.l)
  else // assert length.top(args.l, noargs)= noargs report"OOPS2"+ state + next // 
  // assert false report"OOPS2x"+ state + next + @(+, toword,"", top(args.l, noargs)) //
  let c = CALL(regno.l + 1, 0, 32768, typ.function.constantseq(noargs + 2, i64), C.[ state], -1, top(args.l, noargs))
  let callee=state
  let prof = profile(profile.lib, callee)
  if prof = 0 
  then 
   Lcode("0"_1, code.l + c, lst.l, lmap.l, noblocks.l, regno.l + 1, poppush(args.l, noargs,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l,const.l)
  else // if callee ="PROCESS2"_1 
  then let discard = if noargs = 1 ∧ nosons(t_1)= 5 
    then profile(profile.lib, arg.label(t_1_3))
    else   Case of CONST insteand of record as arg   0 
   addcode(l.sons, c,-(regno.l.sons + 1), 1) 
  else // profilecall(profiletype.lib, l,top(args.l, noargs) , C.[ callee], prof)

  Lcode("0"_1, code.l + c, lst.l, lmap.l, noblocks.l, regno.l + 1, poppush(args.l, noargs,-(regno.l + 1)), blocks.l, tailphi.l, loopblock.l,const.l)

exp1 exp2 exp2 FIRSTVAR <firstvar> LOOPBLOCK 4 <loop body> FINISHLOOP 2

Function setnextfld(p:ipair.internalbc, arg:int)ipair.internalbc 
 let regno = index.p 
  ipair(regno + 1, value.p + STORE(regno + 1,-regno, arg, align8, 0)+ GEP(regno + 1, 1, typ.i64,-regno, C64.1))

function getloc(l:seq.localmap, localno:int, i:int)int 
 if localno(l_i)= localno then regno(l_i)else getloc(l, localno, i + 1)

function poppush(a:seq.int, pop:int, new:int)seq.int subseq(a, 1, length.a - pop)+ [ new]

function top(a:seq.int, n:int)seq.int subseq(a, length.a - n + 1, length.a)

Function prep2(t:tree.cnode) seq.word
 let inst = inst.label.t 
  if inst ="LIT"_1 
  then  "CLIT"+arg.label.t
  else  if inst ="FREF"_1  
  then  "CFREF"+arg.label.t
  else if inst = "WORD"_1 then "CWORD"+arg.label.t
  else @(+, prep2,"", sons.t)+ [ inst, toword.nosons.t]

Function prep(t:tree.cnode)seq.word 
 let inst = inst.label.t 
  if inst ="if"_1 
  then prep(t_1)+"THENBLOCK 1"+ prep(t_2)+"ELSEBLOCK 1"+ prep(t_3)+"if 3"
  else if inst ="SET"_1 
  then prep(t_1)+"DEFINE"+ arg.label.t + prep(t_2)+ inst + arg.label.t 
  else if inst ="LOOP"_1 
  then @(+, prep,"", subseq(sons.t, 3, nosons.t))+"FIRSTVAR"+ arg.label(t_1)+"LOOPBLOCK"+ toword(nosons.t - 1)+ prep(t_2)+"FINISHLOOP 2"
  else if inst in"LIT LOCAL PARA FREF WORD"
  then [ inst, arg.label.t]
  else if inst ="CRECORD"_1 then  
    prep2(t)+   "CONSTANT 1"
  else @(+, prep,"", sons.t)+ [ inst, toword.nosons.t]

exp1 exp2 exp2 FIRSTVAR <firstvar> LOOPBLOCK 4 <loop body> FINISHLOOP 2

function loopmapentry(baselocal:int, regbase:int, i:int)localmap localmap(baselocal + i - 1,-regbase - i)

function profilecall(profiletype:encoding.llvmtype, l:Lcode,args:seq.int, callee:int, idx:int)Lcode 
   let base = regno.l 
  let block = noblocks.l 
  let p1 = C(ptr.i64, [ CONSTGEP, 
  typ.profiletype, 
  typ.ptr.profiletype, 
  C."profclocks", 
  typ.i32, 
  C32.0, 
  typ.i64, 
  C64.idx])
  let pspace = C(ptr.i64, [ CONSTGEP, 
  typ.profiletype, 
  typ.ptr.profiletype, 
  C."profspace", 
  typ.i32, 
  C32.0, 
  typ.i64, 
  C64.idx])
  let pcount = C(ptr.i64, [ CONSTGEP, 
  typ.profiletype, 
  typ.ptr.profiletype, 
  C."profcounts", 
  typ.i32, 
  C32.0, 
  typ.i64, 
  C64.idx])
  let c = GEP(base + 1, 1, typ.profiletype, C."profrefs", C64.0, C64.idx)
  + LOAD(base + 2,-base - 1, typ.i64, align8, 0)
  + BINOP(base + 3,-base - 2, C64.1, 0, typ.i64)
  + STORE(base + 4,-base - 1,-base - 3, align8, 0)
  + CMP2(base + 4,-base - 2, C64.0, 32)+ BR(base + 5, block, block + 1,-base - 4)
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
  + BINOP(base + 17,-base - 16, C64.1, 0, typ.i64)+ STORE(base + 18, pcount,-base - 17, align8, 0)
  + BR(base + 18, block + 2)
  + CALL(base + 18, 0, 32768, typ.function.constantseq(length.args + 2, i64), callee, -1, args)
  + BR(base + 19, block + 2)+ PHI(base + 19, typ.i64,-base - 7, block,-base - 18, block + 1)+ LOAD(base + 20,-base - 1, typ.i64, align8, 0)
  + BINOP(base + 21,-base - 20, C64.1, 1, typ.i64)+ STORE(base + 22,-base - 1,-base - 21, align8, 0)
   Lcode( "0"_1, code.l+c, lst.l, lmap.l, noblocks.l+3, regno.l+21, poppush(args.l, length.args,-base - 19), blocks.l, tailphi.l, loopblock.l, const.l)


use seq.stat5

Function encode(stat5, erecord.stat5)  encoding.stat5 export

type statencoding is encoding stat5

type stat5 is record caller:word, callee:word

function hash(s:stat5)int hash.caller.s + hash.callee.s

function =(a:stat5, b:stat5)boolean caller.a = caller.b ∧ callee.a = callee.b

function maxprof int 1000

Function profile(caller:word, callee:word)int 
 assert length.decode.callee > 0 report"wrong"+ caller + callee 
  if caller = callee ∨ caller ="noprofile"_1 ∨ decode(callee)_1 = decode("q"_1)_1 
  then 0 
  else let idx = encoding.encode(stat5(caller, callee), statencoding)
  if idx > maxprof then 0 else idx + 1

function xx(a:stat5)seq.word [ caller.a, callee.a]

Function see seq.word 
 let map = subseq(mapping.statencoding, 1, maxprof)
  @(+, xx,"", map)



/type debug is encoding ipair.Lcode

/function hash(i:ipair.Lcode)int index.i

/function =(a:ipair.Lcode, b:ipair.Lcode)boolean index.a = index.b

/function print(p:ipair.Lcode)seq.word 
 let l = value.p 
  {"&br"+ state.l +"regno ="+ toword.regno.l + @(+, toword,"", args.l)+@(+,printL,"",blocks.l) }
  
  +"code"+ print.code.l }
  
/function printL(x:Lcode) seq.word  @(+, toword,"[", args.x) +"]"

/Function dump seq.word @(+, print,"", mapping.debug)
