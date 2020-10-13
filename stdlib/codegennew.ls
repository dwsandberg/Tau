#!/usr/local/bin/tau


run mylib testnew

Module codegennew

use symbol

use seq.myinternaltype

use seq.int

use ipair.Lcode2

use seq.Lcode2

use UTF8

use bitpackedseq.bit

use seq.seq.bits

use seq.bits

use bits

use codetemplates

use seq.symbol

use seq.seq.seq.int

use seq.seq.int


use ipair.internalbc

use seq.internalbc

use internalbc


use llvm

use llvmconstants


/use seq.llvmconst

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

use set.symbol
 
Function codegen(theprg:program, defines:seq.symbol, uses:set.symbol, thename:word,libdesc:symbol,alltypes:seq.myinternaltype)seq.bits
 //   assert false report @(seperator."&br",tollvmtype.alltypes ,"",toseq.toset.theprg) //
  let tobepatched= typ.conststype+typ.profiletype+toint.symboltableentry("list",conststype)+toint.symboltableentry("profiledata",profiletype)  
   let discard4= @(+,funcdec.alltypes,0,defines)
 let match5map = match5map(theprg,  uses ,alltypes)
  let libmods2=arg.match5map_libdesc
      // let zx2c = createfile("stat.txt", ["in codegen0.3"])//
  let discard3=   modulerecord(  " spacecount ", [ toint.GLOBALVAR, typ.i64,         2,         0,                           0, toint.align8 + 1, 0]) 
  let bodies = @(+, addfuncdef(match5map), empty:seq.internalbc, defines)
  let xxx=profiledata
      let liblib = slot.addliblib( [thename],  libmods2,toint.ptrtoint( ptr.i64, CGEP(symboltableentry("profiledata",profiletype),0)))
         let libnametype = array(length.decodeword.thename + 1, i8)
       let libslot= modulerecord("",[ toint.GLOBALVAR, typ.libnametype, 2, toint.DATA(libnametype, tointseq.decodeword.thename + 0) + 1, 3, toint.align8, 0])
       let f2= modulerecord(" init22 ",      [ toint.FUNCTIONDEC, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])
     let bodytxts = bodies+ 
       [BLOCKCOUNT(1, 1)
      +  CALL(r.1, 0, 32768,  function.[ i64, ptr.i8,   i64], 
       symboltableentry("initlib5" ,function.[ i64, ptr.i8,   i64]),
        CGEPi8( libslot, 0),  liblib ) + ret]
      let data = @(+,slot,empty:seq.slot,constdata )                                  
      let adjust = [ 0, // consttype // length.data + 2, // profiletype // profiledatalen+3  ]
      let patchlist = [  // list // [ toint.GLOBALVAR, typ.conststype,   2,    toint.AGGREGATE.data + 1, 3, toint.align8 + 1, 0]
       ,[toint.GLOBALVAR, typ.profiletype, 2, toint.xxx + 1,  3, toint.align8 + 1, 0] ]
         llvm(patchlist, bodytxts, adjust(typerecords, adjust, 1))


 
 function addfuncdef(match5map:seq.match5,  i:symbol)internalbc
   let m=match5map_i 
 //   let hh=process.subaddfuncdef(match5map,m)
    assert not.aborted.hh report "fail get"+ inst.m+ message.hh +"&br"+print.code.m
    result.hh
use process.internalbc
function subaddfuncdef(match5map:seq.match5,  m:match5)internalbc //
 let options=options(match5map,m)
 let code= if length.options > 0  then  
  // assert  "PROFILE"_1 in options  report "PROFILE PROBLEM"+options //
    subseq(code.m,1,length.code.m-2) else code.m
 let nopara=arg.m
    let l = Lcode2(emptyinternalbc, paramap(nopara,empty:seq.localmap), 1, nopara + 1, empty:stack.int, empty:stack.Lcode2)
 let g5 = if "PROFILE"_1 in options then  mangledname.m else"noprofile"_1
 let r = @(processnext.g5,_.match5map, l, (code))
  BLOCKCOUNT(1, noblocks.r) + code.r + RET(r(regno.r + 1), slot.top.args.r)

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
   let action = action.m
  if action = "CALL"_1 then
     let callee = mangledname.m  
  let noargs = arg.m
   let args = top(args.l, noargs)
    if profile = "noprofile"_1 ∨ profile = callee then
    let c = usetemplate(m, regno.l, empty:seq.int) + CALLFINISH(regno.l + 1, [ -1] + args)
      Lcode2(code.l + c, lmap.l, noblocks.l, regno.l + 1, push(pop(args.l, noargs), -(regno.l + 1)), blocks.l)
    else
       profilecall( l, args, symboltableentry( callee,functype.m), profile(profile, callee),functype.m)
  else if action = "ACTARG"_1 then 
  Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, arg.m), blocks.l)
  else if action = "LOCAL"_1 then 
   Lcode2(code.l, lmap.l, noblocks.l, regno.l, push(args.l, getloc(lmap.l, arg.m, 1)), blocks.l)
  else if action = "TEMPLATE"_1 then
  let newcode = usetemplate(m, regno.l, toseq.args.l)
     let noargs = arg.m
     Lcode2(code.l + newcode, lmap.l, noblocks.l, regno.l + length.m, push(pop(args.l, noargs), -(regno.l + length.m)), blocks.l)
  else if action = "EXITBLOCK"_1 then
           assert    length.toseq.args.l > 0 report "fail 5e"
     let exitblock=       Lcode2(code.l, lmap.l, noblocks.l , regno.l, push(args.l,0), blocks.l)
    Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l, empty:stack.int, push(blocks.l,exitblock))
    else if action = "BR"_1  then
           assert    length.toseq.args.l > 2 report "fail 5b"
        let newcode = CAST(r(regno.l + 1), slot.top(args.l,arg.m)_1,  i1, CASTTRUNC)
       let cond= Lcode2(code.l + newcode, lmap.l, noblocks.l, regno.l + 1, push(args.l,1), blocks.l)
      Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l + 1, empty:stack.int, push(blocks.l,cond))
    else if action = "BLOCK"_1  then
     let no=arg.m 
      let blks= top(blocks.l,no)
      assert length.blks=no report "XXXXXX arg"+profile
       let rblk = processblk(functype.m,blks,1,empty:seq.localmap,BR(  noblocks.l- 1)) 
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
        // if length.phi.rblk=2 &and false then
          Lcode2(code.rblk, lmap.l, noblocks.l , regno.l,  push(pop(firstblkargs, popno),(phi.rblk)_2), pop(blocks.l, no))  
         else //
       let newstack =push(pop(firstblkargs, popno)  , -(regno.l + 1))
      let newcode=code.rblk+phiinst(regno.last.blks, typ.functype.m, phi.rblk,1)
      Lcode2(newcode, lmap.l, noblocks.l , regno.l + 1,  newstack, pop(blocks.l, no))
    else if action = "DEFINE"_1 then
    Lcode2(code.l,  [localmap(arg.m, top.args.l)]+lmap.l, noblocks.l, regno.l, pop(args.l,1),  blocks.l)
    else if action = "SET"_1 then l
     else if action = "LOOPBLOCK"_1 then
     let varcount = arg.m - 1
     let firstvar = constvalue.slot.top.args.l
     let bodymap = @(addloopmapentry(firstvar, regno.l), identity,lmap.l, arithseq(varcount, 1, 1))
     let exitblock=       Lcode2(code.l, lmap.l, noblocks.l , regno.l, push(push(args.l,varcount),2), blocks.l)
    Lcode2(emptyinternalbc, bodymap, noblocks.l + 1, regno.l+ varcount, empty:stack.int,  push( blocks.l,exitblock) )  
    else  if action = "CONTINUE"_1 then
    let exitblock=       Lcode2(code.l, lmap.l, noblocks.l , regno.l, push(args.l,3), blocks.l)
    Lcode2(emptyinternalbc, lmap.l, noblocks.l + 1, regno.l, empty:stack.int, push(blocks.l,exitblock))  
    else if  action = "RECORD"_1 then 
      let noargs = arg.m
     let args = top(args.l, noargs)
     let newcode = CALL(r(regno.l + 1), 0, 32768,  function.[ ptr.i64, i64, i64], 
     symboltableentry("allocatespaceQ3AseqQ2ETZbuiltinZint",function.[ ptr.i64, i64, i64]), r.1, C64.noargs)
     let fldbc=setnextfld(code.l + newcode,args,1,fullinst.m,3,regno.l+1,regno.l+1,0)
     let newbc=value.fldbc+  CAST(r(index.fldbc + 1), r(regno.l + 1),  i64, CASTPTRTOINT) 
      Lcode2(newbc, lmap.l, noblocks.l, index.fldbc+1, push(pop(args.l, noargs), -(index.fldbc + 1)), blocks.l)
    else 
         assert action = "CALLIDX"_1 report"code gen unknown" + action
        callidxcode( l , top(args.l,2))

function processblk(phitype:llvmtype,blks:seq.Lcode2,i:int, map:seq.localmap,exitbr:internalbc) processblkresult
         processblk(phitype,blks,1,exitbr,emptyinternalbc,1,empty:seq.int,empty:seq.int) 
         
function kind(a:Lcode2) word toword.(top.args.a) 

type processblkresult  is record code:internalbc,phi:seq.int
     
function processblk(phitype:llvmtype,    blks:seq.Lcode2,i:int, exitbr:internalbc,code:internalbc,varcount:int,phi:seq.int,tailphi:seq.int) processblkresult
    if i > length.blks then
        let firstblk=blks_1
        let code1= if top.args.firstblk= //  loopblock // 2 then
            let noargs = top.pop.args.firstblk
                     //    assert false report "JKL"+    @(+,toword,"",  tailphi ) //
            code.firstblk+BR(  noblocks.firstblk) + phiinst(regno.firstblk, typ.phitype, tailphi, noargs)+code
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
           processblk(phitype,blks,i+1,exitbr, code+code.l+exitbr,varcount,phi+ [ noblocks.l - 1] +  t2,tailphi )
        else if kind=2 then // LOOPBLOCK //
           //   assert false report "L"+@(+,toword,"",args.l) //
          let noargs = top.pop.args.l
        //  let firstvar = top.pop.args.l //
           let newtailphi = [ noblocks.l - 1] + top(pop.pop.pop.args.l,noargs)
         processblk(phitype,blks,i+1,exitbr,    code, varcount,phi,newtailphi) 
        else if kind=3 then // CONTINUE //
           assert kind.blks_1 ="2"_1   report "incorrect format on block"+@(+,kind,"",         blks)  
           let noargs = top.pop.args.blks_1
                 //  assert false report "C"+@(+,toword,"",args.blks_1) +"noargs:"+toword.noargs //
          let newtailphi = tailphi + [ noblocks.l - 1]+  top( pop.args.l,noargs)
          let newcode=BR( noblocks.blks_1)
          processblk(phitype,blks,i+1,exitbr,    code+code.l+ newcode, varcount,phi,newtailphi) 
        else
          // br block //
           assert kind=1 report "expecting br block"+toword.kind
                assert length.args.l > 3 report "check m"+@(+,toword, "",[kind]+toseq.args.l)
                 let args=top(args.l,4) 
                assert between(constvalue.slot(args_2)- 1,1,length.blks) &and 
                between(constvalue.slot(args_3)- 1,1,length.blks) report "check mm"
           let newcode=BR(r(regno.l + 1), noblocks.blks_(constvalue.slot(args_2)- 1 ),   
           noblocks.blks_(constvalue.slot(args_3)- 1 ),r.regno.l)
         processblk(phitype,blks,i+1,exitbr,    code+code.l+ newcode, varcount,phi,tailphi) 
    
   
Function setnextfld( bc:internalbc,args:seq.int,i:int,types:seq.word,j:int,regno:int,pint:int,preal:int) ipair.internalbc
if i > length.args then ipair(regno,bc)
else 
   let newj=  if types_j in "$  $record" then 
    // we have reached the type in the module in the full instruction in the match5 record // j else 
   max(findindex(","_1,types)+1,length.types-1)
   let typ=if length.types=3 then "int"_1 else types_(newj-1)
   assert typ in  "int real seq ptr"  report "unknown type gencode"+types
    if preal =0 &and typ="real"_1 then   
     setnextfld( bc+CAST(r(regno + 1), r.pint,  ptr.double, 11)  
            ,args,i,types,j,regno+1,pint ,regno+1)
  else   
let newbc=bc+ (if check &and typ="real"_1 then
       GEP(r(regno + 1),  double,r.preal, C64.(i-1))
       else        GEP(r(regno + 1),  i64,  r.pint, C64.(i-1))
)
+STORE(r(regno + 2), r.(regno+1), slot.args_i)
  setnextfld(newbc,args,i+1,types,newj,regno+1,pint,preal)

function getloc(l:seq.localmap, localno:int, i:int)int
 if localno.l_i = localno then regno.l_i else getloc(l, localno, i + 1)

function addloopmapentry(baselocal:int, regbase:int,l:seq.localmap,i:int) seq.localmap
        [localmap(baselocal + i - 1, - regbase - i)]+l
 
use seq.slot

function profilecall( l:Lcode2, args:seq.int, callee:slot, idx:int,functype:llvmtype)Lcode2
 let base = regno.l
 let block = noblocks.l
  let  pcount=   toint.CGEP(  symboltableentry("profiledata",ptr.profiletype),  2+6 * ( idx-2) + 2)
 let  p1=  // pclocks // toint.CGEP(  symboltableentry("profiledata",ptr.profiletype),  2+6 * ( idx-2) + 3)
 let  pspace=   toint.CGEP(  symboltableentry("profiledata",ptr.profiletype),  2+6 * ( idx-2) + 4)
 let  prefs=   toint.CGEP(  symboltableentry("profiledata",ptr.profiletype),  2+6 * ( idx-2) + 5)
 let c = GEP(r(base + 1),  profiletype,symboltableentry("profiledata",ptr.profiletype))
 + LOAD(r(base + 2), slot.prefs,  i64 )
 + BINOP(r(base + 3), r( base +2), C64.1, add )
 + STORE(r(base + 4), slot.prefs, r(base +3))
 + CMP2(r(base + 4), r(base +2), C64.0, 32)
 + BR(r(base + 5), block, block + 1, r(base +4))
 + CALL(r(base + 5), 0, 32768,  function.[ i64], symboltableentry("clock",function.[ i64]))
 + LOAD(r(base + 6), symboltableentry("spacecount",i64), i64 )
 + CALL(r(base + 7), 0, 32768,  functype, callee, r.1, @(+,slot,empty:seq.slot,args))
 + CALL(r(base + 8), 0, 32768,  function.[ i64], symboltableentry("clock",function.[ i64]))
 + LOAD(r(base + 9), symboltableentry("spacecount",i64),  i64 )
 + BINOP(r(base + 10), r(base+8), r(base + 5), sub)
 + BINOP(r(base + 11), r( base + 9), r( base + 6), sub )
 + LOAD(r(base + 12), slot.p1, i64 )
 + BINOP(r(base + 13), r( base + 12), r(base +10), add )
 + STORE(r(base + 14), slot.p1, r(base + 13))
 + LOAD(r(base + 14), slot.pspace, i64 )
 + BINOP(r(base + 15), r( base + 14), r( base + 11), add )
 + STORE(r(base + 16), slot.pspace, r(base + 15))
 + LOAD(r(base + 16), slot.pcount,  i64)
 + BINOP(r(base + 17),r(base + 16), C64.1,add )
 + STORE(r(base + 18), slot.pcount, r(base + 17))
 + BR( block + 2)
 + CALL(r(base + 18), 0, 32768,  functype, callee, r.1, @(+,slot,empty:seq.slot,args))
 + BR( block + 2)
 + PHI(r(base + 19),  i64, r(base +7), block, r( base +18), block + 1)
 + LOAD(r(base + 20), slot.prefs,  i64)
 + BINOP(r(base + 21), r( base +20), C64.1, sub )
 + STORE(r(base + 22), slot.prefs, r(base + 21))
  Lcode2(code.l + c, lmap.l, noblocks.l + 3, regno.l + 21, push(pop(args.l, length.args), - base - 19), blocks.l)
 

use seq.encodingpair.stat5

type stat5 is record caller:word, callee:word 


  
  function    profilerepA(zero:slot,a     :encodingpair.stat5 ) seq.slot
           [slot.wordref.caller.data.a,slot.wordref.callee.data.a,zero,zero,zero,zero]
           
  function profiledata slot         
          let d=encoding:seq.encodingpair.stat5
          let data=    @(+, profilerepA.C64.0, [C64.6,C64.length.d], d)
           AGGREGATE.data 

 function profiledatalen int
       (length.encoding:seq.encodingpair.stat5 * 6)+2

function assignencoding(l:int, a:stat5) int l+1

function hash(s:stat5)int abs(hash.caller.s + hash.callee.s)

function =(a:stat5, b:stat5)boolean caller.a = caller.b ∧ callee.a = callee.b

Function profile(caller:word, callee:word)int
 if caller = callee ∨ caller = "noprofile"_1 then 0
 else valueofencoding.encode(stat5(caller, callee)) + 1

 
/type debug is encoding ipair.Lcode2

/function hash(i:ipair.Lcode2)int index.i

/function =(a:ipair.Lcode2, b:ipair.Lcode2)boolean index.a = index.b

/function print(p:ipair.Lcode2)seq.word let l = value.p {"
&br"+ state.l +"regno ="+ toword.regno.l + @(+, toword,"", args.l)+ @(+, printL,"", blocks.l)}

+"code"+ print.code.l }

/function printL(x:Lcode2)seq.word @(+, toword,"[", args.x)+"]"

/Function dump seq.word @(+, print,"", mapping.debug)

function callidxcode( l:Lcode2, args:seq.int)Lcode2
let theseq=args_1
let idx=args_2
 let base = regno.l
 let block = noblocks.l 
 let last=15 
 let c = CAST(r(base +1), slot.theseq,  ptr.i64, CASTINTTOPTR)
 + LOAD(r(base +2), r(base+1),  i64 )
 + CMP2(r(base + 3), r(base + 2), C64.0, 32)
 + BR(r(base + 4), block +2, block  , r(base + 3))
 + // block // // gt // CMP2(r(base + 4), r(base + 2), C64.1000, 38)
  +BR(r(base + 5), block +1, block+3  , r(base + 4))
 + // block 1 // CAST(r(base +5),r(base+2),  ptr.function.[ i64,  i64, i64, i64], CASTINTTOPTR)
 +   CALL(r(base +6), 0, 32768,  function.[ i64,   i64, i64, i64], r(base+5), r.1,  @(+,slot,empty:seq.slot,args))  
  + BR( block + 4)
  + // block 2 // GEP(r(base +7) ,  i64, r(base+1), slot.idx) 
  + GEP(r(base +8)  ,  i64, r(base+7),C64.1) 
  + LOAD(r(base +9) , r(base+8), i64)
  + BR( block + 4)
  +  // block 3 // 
    // first element start //   GEP(r(base +10)  ,  i64, r(base+1),C64.2) 
  + BINOP(r(base+11),  slot.idx, C64.1,sub)
  + BINOP(r(base+12),  r(base+11), r(base+2),  mul)
  + // objptr+2+ds*(idx-1) // GEP(r(base+13),  i64, r(base+10), r(base+12))
  + CAST(r(base+14),r(base+13), i64, CASTPTRTOINT)
 + BR( block + 4)
  + // block 4 //
  PHI(r(base + last),  i64, r(base + 6), block +1, r( base + 9), block + 2,r(base+14), block+3)
  Lcode2(code.l + c, lmap.l, noblocks.l+5  , regno.l + last, push(pop(args.l, 2), - base - last), blocks.l)

  