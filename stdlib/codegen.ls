Module codegen

use buildtree

use codetemplates

use internalbc

use ipair.linklists2

use libdescfunc

use libscope

use llvm



use passcommon

use persistant

use seq.encoding.llvmtype

use seq.func

use seq.internalbc

use seq.libsym

use seq.libtype

use seq.linklists2

use seq.llvmconst

use seq.localmap5

use seq.seq.int

use seq.seq.seq.int

use seq.stat5

use seq.tree.cnode

use stacktrace

use stdlib

use textio

use tree.cnode

function funcdec(proto:int, a:seq.int)seq.int 
 // first two elements of llvm symbol record must be discarded to form funcname // 
  let funcname = encodeword.subseq(a, 3, length.a)
  [ MODULECODEFUNCTION, typ.getftype.funcname, 0, proto, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

function funcdec(proto:int, a:llvmconst)seq.int 
 // first two elements of llvm symbol record must be discarded to form funcname // 
  [ MODULECODEFUNCTION, typ.getftype.funcname.a, 0, proto, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  
use seq.seq.bits

Function codegen5(z:pass1result)seq.bits 
    PROFILE.let thename = libname(z)_1 
  let symlist = "libname initlib5 words wordlist list  profcounts profclocks profspace profrefs profstat spacecount clock"+ merge(thename,"$profileresult"_1)+"init22 allocatespaceZbuiltinZint PROCESS2 HASH"+ merge."llvm.sqrt.f64"+ merge."llvm.sin.f64"+ merge."llvm.cos.f64"
  let discard2 = @(+, C, 0, symlist + @(+, mangledname,"", code.z))
  let discard3 = @(+, findcalls, 0, @(+, codetree, empty:seq.tree.cnode, code.z))
  let nosyms = length.symbolrecords2 
  let wordstype = array(-1, i64)
   // let conststype = array(-2, i64) //
  let profiletype = array(-3, i64)
  let fb = funcdef(code.z, geninfo5(thename, wordstype, conststype, profiletype,"X"_1, 0, table,"noprofile"_1), createlinkedlists, 1, empty:seq.internalbc)
  let noprofileslots = length.see / 2 
    let liblib = prepareliblib2(alltypes.z,consts.fb,libdesc.z)
    let beforearcs =   value.liblib
  let arcs = place.beforearcs
  let data =   addwordseq(beforearcs,see) 
  let x = C(array(4, i64), [ AGGREGATE, 
  C(i64, [ CONSTCECAST, 9, typ.ptr.i64, getelementptr(conststype,"list",arcs+1) ] ), 
  C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profcounts"]), 
  C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profclocks"]), 
  C(i64, [ CONSTCECAST, 9, typ.ptr.profiletype, C."profspace"])])
  let words = worddata 
  let worddatatype = array(length.words + 2, i64)
  let adjust = [ 0, 2 + wordcount + 1, length.a.data + 5 + 2, noprofileslots + 2 + 3]
  let syms = symbolrecords2 
  assert length.syms = nosyms report"extra symbols!"
  let libnametype = array(length.decode.thename + 1, i8)
  let libnameptr = C(ptr.i8, [ CONSTGEP, typ.libnametype, typ.ptr.libnametype, C."libname", typ.i32, C32.0, typ.i32, C32.0])
  let deflist = [ [ MODULECODEGLOBALVAR, 
  typ.libnametype, 
  2, 
  C(libnametype, [ CONSTDATA]+ decode.thename + 0)+ 1, 
  3, 
  align4, 
  0], 
  [ MODULECODEFUNCTION, 
  typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64,  ptr.i64], 
  0, 
  1, 
  0, 
  1, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0], 
  [ MODULECODEGLOBALVAR, typ.wordstype, 2, C(wordstype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  [ MODULECODEGLOBALVAR, 
  typ.worddatatype, 
  2, 
  1 + C(worddatatype, [ AGGREGATE, C64.0, C64.length.words]+ words), 
  3, 
  align8 + 1, 
  0], 
  [ MODULECODEGLOBALVAR, typ.conststype, 2, initializer(conststype, data), 3, align8 + 1, 0], 
  // profcounts // 
   [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  // profclocks // 
   [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  // profspace // 
   [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  // profrefs // 
   [ MODULECODEGLOBALVAR, typ.profiletype, 2, C(profiletype, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  // profstat // [ MODULECODEGLOBALVAR, typ.array(4, i64), 2, x + 1, 3, align8 + 1, 0], 
  // spacecount // [ MODULECODEGLOBALVAR, typ.i64, 2, 0, 0, align8 + 1, 0], 
  // count()// [ MODULECODEFUNCTION, typ.function.[ i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  [ MODULECODEFUNCTION, typ.function.[ i64], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  [ MODULECODEFUNCTION, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // allocatespaceZbuiltinZint // 
   [ MODULECODEFUNCTION, typ.function.[ i64, i64, i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // PROCESS2 // [ MODULECODEFUNCTION, typ.function.[ i64, i64, i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // hash // [ MODULECODEFUNCTION, typ.function.[ i64, i64], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // llvm.sqrt.f64 // 
   [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // llvm.sin.f64 // 
   [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], 
  // llvm.cos.f64 // 
   [ MODULECODEFUNCTION, typ.function.[ double, double], 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]+ @(+, funcdec.0, empty:seq.seq.int, subseq(syms, length.symlist + 1, length.code.z + length.symlist))+ @(+, funcdec.1, empty:seq.seq.int, subseq(syms, length.symlist + 1 + length.code.z, length.syms))
  let bodytxts = [ BLOCKCOUNT(1, 1)+ RET(1, C(i64, [ CONSTCECAST, 9, typ.ptr.array(4, i64), C."profstat"])), 
  BLOCKCOUNT(1, 1)+ 
  CALL(1, 0, 32768, typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64,  ptr.i64], 
   C."initlib5"  , libnameptr, 
  getelementptr(wordstype,"words",0), 
  getelementptr(worddatatype,"wordlist",0),
   getelementptr(conststype,"list",0), 
    getelementptr(conststype,"list",index.liblib+1) )
   + GEP(2, 1, typ.profiletype, C."profclocks", C64.0, C64.1)
  + STORE(3, -2, C64.noprofileslots, align8, 0)+ GEP(3, 1, typ.profiletype, C."profspace", C64.0, C64.1)
  + STORE(4, -3, C64.noprofileslots, align8, 0)+ GEP(4, 1, typ.profiletype, C."profcounts", C64.0, C64.1)
  + STORE(5, -4, C64.noprofileslots, align8, 0)+ GEP(5, 1, typ.profiletype, C."profrefs", C64.0, C64.1)
  + STORE(6, -5, C64.noprofileslots, align8, 0)+ RET.6]+ bodies.fb 
  assert length.symbolrecords2 = nosyms report"extra symbols2!"
  llvm(deflist, bodytxts, adjust(typerecords, adjust, 1)
  )

type localmap5 is record localno:int, regno:int

type Lcode5 is record code:internalbc, lst:linklists2, regno:int, arg:int, noblocks:int, tailphi:seq.int, loopblock:int,
multival:seq.int

Lcode5(internalbc, linklists2, int, int, int, seq.int, seq.int, int, seq.int)NOT FOUND 

function print(m:localmap5)seq.word 
 {"local"+ toword.localno.m +"ref"+ toword.regno.m }

function findcalls(t:tree.cnode)int 
 let discard = if inst.label.t =" FREF"_1
   then C.arg.label.t 
   else  if inst.label.t in"SET RECORD CRECORD STKRECORD LOCAL  LIT PARA EQL if IDXUC PROCESS2  WORD  
   Q3EZbuiltinZintZint hashZbuiltinZint allocatespaceZbuiltinZint CALLIDX LOOP CONTINUE MSET MRECORD"
   then 0 
   else 
   C.inst.label.t 
  @(+, findcalls, 0, sons.t)




type funcdefresult5 is record bodies:seq.internalbc, consts:linklists2

type geninfo5 is record lib:word, wordstype:encoding.llvmtype, conststype:encoding.llvmtype, profiletype:encoding.llvmtype, funcname:word, paraAdjustment:int, tab:seq.match5, profile:word

use seq.funcdefresult5 

use altgen

/use process.altresult

/function xxx(f:func, consts:linklists2 ,info:geninfo5) altresult
altgen(f,consts,lib.info, wordstype.info, conststype.info, profiletype.info, tab.info)


function funcdef(fl:seq.func, info:geninfo5, consts:linklists2, i:int, result:seq.internalbc)funcdefresult5 
if i > length.fl 
  then funcdefresult5(result, consts)
  else 
   let f =  fl_i 
              let x=altgen(f,consts,lib.info, wordstype.info, conststype.info, profiletype.info, tab.info)
       funcdef(fl, info, l.x, i + 1, result + [ body.x])
    


function loopmapentry(baselocal:int, regbase:int, i:int)localmap5 
 localmap5(baselocal + i - 1,-regbase - i)
 
function mgetmapentry(baselocal:int,explist:seq.int,i:int) localmap5
   localmap5(baselocal + i - 1,explist_i)
 
use set.word

use seq.set.word

use seq.Lcode5

function casttree(tree.cnode) tree.seq.word builtin

function gencode(lib:geninfo5, lmap:seq.localmap5, l:Lcode5, t:tree.cnode)Lcode5 
 let inst = inst.label.t 
  // let arg = arg.label.t // 
  if inst ="PARA"_1 
  then setarg(l, paraAdjustment.lib + toint.arg.label.t )
  else if inst ="LOCAL"_1 
  then setarg(l, getloc(lmap, toint.arg.label.t , 1))
  else if inst ="LIT"_1 
  then setarg(l, C64.toint.arg.label.t )
  else if inst ="FREF"_1 
  then setarg(l, C(i64, [ CONSTCECAST, 9, typ.ptr.getftype.arg.label.t , C.arg.label.t ]))
  else if inst="CRECORD"_1 then
      let tt =addconst(lst.l,casttree.t)
         let newcode= GEP(regno.l+1, 1, typ.conststype, C."list", C64.0,  C64(index.tt + 1))
        + CAST(regno.l+2, -(regno.l+1), typ.i64, 9)
        // setlist(usetemplate(l, CONSTtemplate, C64(index.tt +1 ), 0,-(regno.l + 2), 2), value.tt) //
         Lcode5(code.l + newcode, value.tt, regno.l + 2, -(regno.l + 2), noblocks.l, tailphi.l, loopblock.l,multival.l)        
    else  if inst ="WORD"_1 
  then let a = C(ptr.i64, [ CONSTGEP, 
   typ.wordstype.lib, 
   typ.ptr.wordstype.lib, 
   C."words", 
   typ.i32, 
   C32.0, 
   typ.i64, 
   C64(word33.arg.label.t  + 1)])
   usetemplate(l, WORDtemplate, a, 0,-(regno.l + 1), 1)
  else  if inst ="if"_1 
  then let exp1a = gencode(lib, lmap, l, t_1)
   let c2 = CAST(regno.exp1a + 1, arg.exp1a, typ.i1, CASTTRUNC)
   let exp1 = addcode(exp1a, c2,-(regno.exp1a + 1), 1)
   let exp2 = gencode(lib, lmap, addblockreset.exp1, t_2)
   let exp3 = gencode(lib, lmap, addblockreset.exp2, t_3)
   let br = BR(regno.exp1 + 1, noblocks.exp1, noblocks.exp2, arg.exp1)
   let br1 = BR(regno.exp3, noblocks.exp3)
   let nophiinst=max(length.multival.exp2,1)
   let phi = if length.multival.exp2=0 then
      PHI(regno.exp3 + 1, typ.i64, arg.exp2, noblocks.exp2 - 1, arg.exp3, noblocks.exp3 - 1)
    else 
     @(+,  ifphi(regno.exp3,noblocks.exp2 - 1,noblocks.exp3 - 1,multival.exp2,multival.exp3) ,emptyinternalbc,arithseq(nophiinst,1,1))
    let newcode = code.exp1 + br + code.exp2 + br1 + code.exp3 + br1 + phi 
   Lcode5(newcode, lst.exp3, regno.exp3 + nophiinst,-(regno.exp3 + 1), noblocks.exp3 + 1, tailphi.exp3, loopblock.exp3,
    if length.multival.exp2=0 then empty:seq.int else  arithseq(nophiinst,-1,-(regno.exp3+1) ))
  else if inst ="CALLIDX"_1 
  then let exp1 = gencode(lib, lmap, l, t_1)
   let exp2 = gencode(lib, lmap, exp1, t_2)
   let exp3 = gencode(lib, lmap, exp2, t_3)
   let newcode = CAST(regno.exp3 + 1, arg.exp1, typ.ptr.function.[ i64, i64, i64, i64], CASTINTTOPTR)
               + CALL(regno.exp3 + 2, 0, 32768, typ.function.[ i64, i64, i64, i64],-(regno.exp3 + 1), -1, arg.exp2, arg.exp3)
   addcode(exp3, newcode,-(regno.exp3 + 2), 2)
  else if inst ="SET"_1 
  then let exp1 = gencode(lib, lmap, l, t_1)
   let newmap = lmap + localmap5(toint.arg.label.t, arg.exp1)
   // assert false report @(+, print,"MAP", newmap)// gencode(lib, newmap, exp1, t_2)
  else 
  let template = lookup(tab.lib, inst)
  if length.template > 0 
  then let exp1 = gencode(lib, lmap, l, t_1)
   let exp2 = if nosons.t = 2 then gencode(lib, lmap, exp1, t_2)else exp1 
   usetemplate(exp2, template.template, arg.exp1, arg.exp2,-(regno.exp2 + length.template), length.template)
  else  if inst ="LOOP"_1 
  then // Sons of loop <start # of loop variables>, <loopbody> < entering values of loop variables> // 
     let sons=@(addson(lib,false,lmap),identity,processsonsresult5(l,empty:seq.int    ), subseq(sons.t,3,nosons.t))
   let varcount = nosons.t - 2 
   let loopblock = noblocks.l.sons 
   let bodymap = @(+, loopmapentry(toint.arg.label(t_1), regno.l.sons), lmap, arithseq(varcount, 1, 1))
   assert true report @(+, print,"bodymap", bodymap)+ @(+, toword,"explist", explist.sons)+"regno"+ toword.regno.l.sons + toword.paraAdjustment.lib 
   let bodyl = Lcode5(emptyinternalbc, lst.l, regno.l.sons + varcount, -1, noblocks.l.sons + 1, empty:seq.int, loopblock,empty:seq.int)
   let body = gencode(lib, bodymap, bodyl, t_2)
   Lcode5(code.l.sons + BR(regno.l.sons + 1, loopblock)+ phiinst(regno.l.sons, typ.i64, [ loopblock - 1]+ explist.sons + tailphi.body, varcount)+ code.body, lst.body, regno.body, arg.body, noblocks.body, tailphi.l, loopblock.l
   ,multival.l)
  else  
   let sons=@(addson(lib,inst ="CONTINUE"_1 ,lmap),identity,processsonsresult5(l,empty:seq.int    ), sons.t )
   if inst = "MRECORD"_1 then
        let size=length.multival.l.sons
        let l2=usetemplate(l.sons, RECORDtemplate, C64.size, -1,-(regno.l.sons + 2), 2)
        setarg(@(setnextfld,identity,l2,multival.l.sons ),-(regno.l.sons + 1))
   else if inst ="MSET"_1 then
    Lcode5(code.l.sons,lst.l.sons,regno.l.sons,-1,noblocks.l.sons, tailphi.l.sons, loopblock.l.sons,explist.sons)
   else if inst ="CONTINUE"_1  then  
   let block = noblocks.l.sons 
   Lcode5(code.l.sons + BR(regno.l.sons, loopblock.l), lst.l.sons, regno.l.sons, -1, block + 1, tailphi.l.sons + [ block - 1]+ 
   explist.sons, loopblock.l,empty:seq.int)
  else
   if inst ="RECORD"_1  
  then 
         let l2=usetemplate(l.sons, RECORDtemplate, C64.nosons.t, -1,-(regno.l.sons + 2), 2)
                 setarg(@(setnextfld,identity,l2,explist.sons ),-(regno.l.sons + 1)) 
                 else if
      //
         let newcode = usetemplate(regno.l.sons, RECORDtemplate, C64.nosons.t, -1)
         let x= value.@(setnextfld, identity, ipair(regno.l + 2, code.l.sons + newcode), explist.sons)
       Lcode5(x, lst.l.sons,regno.l + 2 + nosons.t, -(regno.l + 1), noblocks.l.sons, tailphi.l.sons , loopblock.l,multival.l)           
    else  if // inst ="STKRECORD"_1  
  then 
       let l2=usetemplate(l.sons, STKRECORDtemplate( C64.nosons.t),-1, -1,-(regno.l.sons + 1), 2) 
      setarg(@(setnextfld,identity,l2,explist.sons ),-(regno.l.sons + 2))
  else 
   let callee=inst
   let c = CALL(regno.l.sons + 1, 0, 32768, typ.function.constantseq(nosons.t + 2, i64), C.[ callee], -1, explist.sons)
  let prof = profile(profile.lib, callee)
  if prof = 0 
  then addcode(l.sons, c,-(regno.l.sons + 1), 1)
  else if callee ="PROCESS2"_1 
  then let discard = if nosons.t = 1 ∧ nosons(t_1)= 5 
    then profile(profile.lib, arg.label(t_1_3))
    else // Case of CONST insteand of record as arg // 0 
   addcode(l.sons, c,-(regno.l.sons + 1), 1)
  else profilecall(profiletype.lib, sons, C.[ callee], prof)
  
  
use ipair.internalbc



function getloc(l:seq.localmap5, localno:int, i:int)int 
 if localno(l_i)= localno then regno(l_i)else getloc(l, localno, i + 1)

type processsonsresult5 is record l:Lcode5, explist:seq.int

use seq.processsonsresult5

function addson(info:geninfo5, continue:boolean, lmap:seq.localmap5,p:processsonsresult5,t:tree.cnode) processsonsresult5 
FORCEINLINE.
     let  exp = gencode(info, lmap, l.p, t)
     processsonsresult5(exp, explist.p +  if continue &and length.multival.exp > 0 then multival.exp else [arg.exp])




function profilecall(profiletype:encoding.llvmtype, sons:processsonsresult5, callee:int, idx:int)Lcode5 
 let l = l.sons 
 let args = explist.sons
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
  addblock.addblock.addblock.addcode(l, c,-base - 19, 21)

/function setnextfld(p:ipair.internalbc, arg:int)ipair.internalbc 
 let regno = index.p 
  ipair(regno + 1, value.p + STORE(regno + 1,-regno, arg, align8, 0)+ GEP(regno + 1, 1, typ.i64,-regno, C64.1))

Function setnextfld(l:Lcode5,arg:int) Lcode5
    let c=STORE(regno.l + 1,arg.l, arg, align8, 0)+GEP(regno.l + 1, 1, typ.i64, arg.l, C64(1) )
    addcode(l,c,-(regno.l + 1),1) 
 
function addblock(l:Lcode5)Lcode5 Lcode5(code.l, lst.l, regno.l, arg.l, noblocks.l + 1, tailphi.l, loopblock.l,multival.l)

function addblockreset(l:Lcode5)Lcode5 
 Lcode5(emptyinternalbc, lst.l, regno.l, arg.l, noblocks.l + 1, tailphi.l, loopblock.l,multival.l)

function setarg(l:Lcode5, arg:int)Lcode5 Lcode5(code.l, lst.l, regno.l, arg, noblocks.l, tailphi.l, loopblock.l,empty:seq.int)

function setlist(l:Lcode5, list:linklists2)Lcode5 
 Lcode5(code.l, list, regno.l, arg.l, noblocks.l, tailphi.l, loopblock.l,multival.l)

function addcode(l:Lcode5, c:internalbc, arg:int, reginc:int)Lcode5 
 Lcode5(code.l + c, lst.l, regno.l + reginc, arg, noblocks.l, tailphi.l, loopblock.l,multival.l)

function usetemplate(l:Lcode5, c:internalbc, val1:int, val2:int, arg:int, reginc:int)Lcode5 
 Lcode5(code.l + usetemplate(regno.l, c, val1, val2), lst.l, regno.l + reginc, arg, noblocks.l, tailphi.l, loopblock.l,multival.l)

------------------------


function  ifphi (lastreg:int,thenblock:int,elseblock:int,thenmultival:seq.int,elsemultival:seq.int,i:int)internalbc
 PHI(lastreg+i, typ.i64, thenmultival_i, thenblock, elsemultival_i, elseblock)
 
_____________________



