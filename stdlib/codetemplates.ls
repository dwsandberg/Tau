
Module codetemplates

use bits

use fileio

use internalbc

use llvm

use llvmconstants

use mangle

use persistant

use standard

use symbolE

use textio

use seq.bit

use set.int

use otherseq.llvmtype

use seq.llvmtype

use encoding.match5

use seq.match5

use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use seq.seq.int

use seq.seq.symbol

Export constdata seq.slot

Export wordref(w:word)int

Export addliblib(libname:seq.word, mods:int, profiledata:int, isbase:boolean)int



Function tollvmtype(alltypes:typedict, s:symbol)llvmtype
 if  s = Optionsym then function.[i64,i64,i64,i64] 
 else function.tollvmtypelist(alltypes, s)

Function tollvmtypelist(alltypes:typedict, s:symbol)seq.llvmtype
let starttypes = [ tollvmtype(alltypes, resulttype.s), i64]
 for acc = starttypes, @e = paratypes.s do acc + tollvmtype(alltypes, @e)/for(acc)

function tollvmtype(alltypes:typedict, s:mytype)llvmtype
 if isseq.s  then ptr.i64
 else
  let kind =  getbasetype(alltypes, s)
   if kind=typeint /or kind=typeboolean then i64
   else if kind = typereal then double else ptr.i64

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Export type:match5

Export length(match5)int { no of instruction that return results }

Export action(match5)word

Export arg(match5)int

Function firstvar(a:match5)int length.a

Function brt(a:match5)int length.a

Function brf(a:match5)int arg.a

Export llvmtypelist(match5)seq.llvmtype

type match5 is sym:symbol, length:int, parts:internalbc, action:word, arg:int, code:seq.symbol, llvmtypelist:seq.llvmtype

Function functype(m:match5)llvmtype function.llvmtypelist.m

function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:int, code:seq.symbol, llvmtypelist:seq.llvmtype)match5
let m = match5(sym, length, parts, action, arg, code, llvmtypelist)
let discard = encode.m
 m

function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:slot)match5
 addtemplate(sym, length, parts, action, toint.arg, empty:seq.symbol, [ i64])

function addtemplate(sym:symbol, length:int, b:internalbc)match5 addtemplate(sym, length, b,"TEMPLATE"_1, slot.nopara.sym)

function addtemplates(t:seq.word, sym:symbol, length:int, b:internalbc)match5
 first.for acc = empty:seq.match5, e = t do [ addtemplate(replaceTsymbol(typeref(moduleref."?",[e]), sym), length, b)]/for(acc)

function findtemplate(d:symbol)seq.match5 findencode.match5(d, 0, emptyinternalbc,"NOTFOUND"_1, 0, empty:seq.symbol, [ i64])

Export code(match5)seq.symbol

Export type:symbol

Export type:program

Function_(m:seq.match5, d:symbol)match5
let e = findtemplate.d
 assert not.isempty.e report"LL codetemplates" + print.d  + stacktrace
  e_1

function =(a:match5, b:match5)boolean sym.a = sym.b

function hash(a:match5)int fsighash.sym.a

function assignencoding( p:seq.encodingpair.match5,a:match5)int  length.p+1


Function options(match5map:seq.match5, m:match5)seq.word getoption.code.m

Function funcdec(alltypes:typedict, i:symbol)int
 toint.modulerecord([ mangledname.i], [ toint.FUNCTIONDEC, typ.tollvmtype(alltypes, i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

Function match5map(theprg:program, uses:set.symbol, alltypes:typedict)seq.match5
let discard3 = [addtemplate(symbol3("internal","packedindex", seqof.typebit,typeint ,typeint), 8, 
 BINOP(r.1, ibcsub.2,C64.1,sub)
+BINOP(r.2, r.1, C64.6, lshr) 
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
+ LOAD(r.5, r.4, i64)
+ BINOP(r.6, r.1, C64.63, and)
+ BINOP(r.7, r.5, r.6, lshr)
+ BINOP(r.8, r.7, C64.1, and))
, addtemplate(symbol3("internal","packedindex",seqof.typebyte,typeint,typeint ), 9, 
 BINOP(r.1, ibcsub.2,C64.1,sub)
+ BINOP(r.2, r.1, C64.3, lshr) 
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
+ LOAD(r.5, r.4, i64)
+ BINOP(r.6, r.1, C64.7, and)
+ BINOP(r.7, r.6, C64.3, shl)
+ BINOP(r.8, r.5, r.7, lshr)
+ BINOP(r.9, r.8, C64.255, and))
,addtemplate(symbol3("internal","packedindex",seqof.typeref(moduleref."tausupport","packed2"),typeint,typeptr ), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.2, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
,addtemplate(symbol3("internal","packedindex",seqof.typeref(moduleref."tausupport","packed3"),typeint,typeptr ), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.3, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
,addtemplate(symbol3("internal","packedindex",seqof.typeref(moduleref."tausupport","packed4"),typeint,typeptr ), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.4, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
,addtemplate(symbol3("internal","packedindex",seqof.typeref(moduleref."tausupport","packed5"),typeint,typeptr ), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.5, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
,addtemplate(symbol3("internal","packedindex",seqof.typeref(moduleref."tausupport","packed6"),typeint,typeptr ), 4, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.6, mul)
+ BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3))
, addtemplate(symbol3("fileio","tocstr",seqof.typebits,typeref(moduleref."fileio", "cstr")), 2, GEP(r.1, i64, ibcsub.1, C64.2) + CAST(r.2, r.1, i64, ptrtoint))
, addtemplate(symbol3("bits","toint" ,typebyte,typeint ), 0, emptyinternalbc)
, addtemplate(symbol3("bits","toint" ,typebit,typeint ), 0, emptyinternalbc)
, { addtemplate(NullptrOp, 1, CAST(r.1, C64.0, ptr.i64, inttoptr)), addtemplate(STKRECORDOp, 3, ALLOCA(r.1, ptr.ptr.i64, i64, C64.2, 0)+ STORE(r.2, r.1, ibcsub.1)+ GEP(r.2, ptr.i64, r.1, C64.1)+ STORE(r.3, r.2, ibcsub.2)+ GEP(r.3, ptr.i64, r.1, C64.0)), addtemplate(symbol("bitcast(ptr)","builtin","int"), 1, CAST(r.1, ibcsub.1, i64, ptrtoint)), addtemplate(symbol("bitcast(int seq)","interpreter","int"), 1, CAST(r.1, ibcsub.1, i64, ptrtoint)), }
addtemplate(symbol3("interpreter","GEP " ,seqof.typeint,typeint,typeint), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + CAST(r.2, r.1, i64, ptrtoint))
, addtemplate(symbol3("interpreter","bitcast ",typeint,seqof.typeint), 1, CAST(r.1, ibcsub.1, ptr.i64, inttoptr))
, addtemplate(symbol3("internal","bitcast",typeptr,typeptr ), 1, GEP(r.1, i64, ibcsub.1, C64.0))
, addtemplate(symbol4(moduleref."tausupport","toseqX"_1,seqof.typeint, [typeptr],seqof.typeint ), 0, emptyinternalbc)
, addtemplates("bit byte int ptr real packed2 packed3 packed4 packed5 packed6", 
symbol4(moduleref."internal","toseq"_1,seqof.typeT, [typeptr],typeptr ), 0, emptyinternalbc)
, addtemplate(symbol3("real","intpart",typereal, typeint ), 1, CAST(r.1, ibcsub.1, i64, fptosi))
, addtemplate(symbol3("real","toreal",typeint,typereal ), 1, CAST(r.1, ibcsub.1, double, sitofp))
, addtemplate(symbol3("real","-",typereal,typereal,typereal), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sub))
, addtemplate(symbol3("real","+",typereal,typereal,typereal), 1, BINOP(r.1, ibcsub.1, ibcsub.2, add))
, addtemplate(symbol3("real","*",typereal,typereal,typereal), 1, BINOP(r.1, ibcsub.1, ibcsub.2, mul))
, addtemplate(symbol3("real","/",typereal,typereal,typereal), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sdiv))
, addtemplate(symbol3("real","casttoreal",typeint,typereal), 1, CAST(r.1, ibcsub.1, double, bitcast))
, addtemplate(symbol3("real","representation",typereal, typeint), 1, CAST(r.1, ibcsub.1, i64, bitcast))
, addtemplate(symbol3("real","?",typereal,typereal ,typeref(moduleref."standard","ordering")), 5, CMP2(r.1, ibcsub.1, ibcsub.2, 3) + CAST(r.2, r.1, i64, zext)
+ CMP2(r.3, ibcsub.1, ibcsub.2, 2)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add))
, addtemplate(symbol3("standard","? ", typeint,typeint,typeref(moduleref."standard","ordering")), 5, CMP2(r.1, ibcsub.1, ibcsub.2, 39) + CAST(r.2, r.1, i64, zext)
+ CMP2(r.3, ibcsub.1, ibcsub.2, 38)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add))
, addtemplate(symbol3("internal","GEP ",seqof.typeptr,typeint,typeptr), 1, GEP(r.1, i64, ibcsub.1, ibcsub.2))
, addtemplate(symbol3("standard","not", typeboolean,typeboolean), 1, BINOP(r.1, ibcsub.1, C64.1, xor))
, addtemplate(symbol3("standard",">" ,typeint,typeint,typeboolean ), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 38) + CAST(r.2, r.1, i64, zext))
, addtemplate(symbol3("standard","=",typeboolean,typeboolean,typeboolean), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext))
, addtemplate(symbol3("standard","=" ,typeint,typeint,typeboolean ), 2, CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext))
, addtemplate(symbol3("standard","-" ,typeint,typeint,typeint ), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sub))
, addtemplate(symbol3("standard","+" ,typeint,typeint,typeint ), 1, BINOP(r.1, ibcsub.1, ibcsub.2, add))
, addtemplate(symbol3("standard","*" ,typeint,typeint,typeint ), 1, BINOP(r.1, ibcsub.1, ibcsub.2, mul))
, addtemplate(symbol3("standard","/" ,typeint,typeint,typeint ), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sdiv))
, addtemplate(symbol3("bits","<<",typebits,typeint,typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, shl))
, addtemplate(symbol3("bits",">>",typebits,typeint,typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, lshr))
, addtemplate(symbol3("bits","∧",typebits,typebits,typebits ), 1, BINOP(r.1, ibcsub.1, ibcsub.2, and))
, addtemplate(symbol3("bits","∨",typebits,typebits,typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, or))
, addtemplate(symbol3("bits","xor",typebits,typebits,typebits), 1, BINOP(r.1, ibcsub.1, ibcsub.2, xor))
, addtemplate(symbol3(moduleref("builtin",typeint),"setfld",[typeint, seqof.typeint, typeint], typeint), 2, GEP(r.1, i64, ibcsub.2, ibcsub.1) + STORE(r.2, r.1, ibcsub.3)
+ BINOP(r.2, ibcsub.1, C64.1, add))
, addtemplate(symbol3(moduleref("builtin",typeboolean),"setfld",[typeint, seqof.typeboolean, typeboolean], typeint), 2, GEP(r.1, i64, ibcsub.2, ibcsub.1) + STORE(r.2, r.1, ibcsub.3)
+ BINOP(r.2, ibcsub.1, C64.1, add))
, addtemplate(symbol3(moduleref("builtin",typereal),"setfld",[typeint, seqof.typereal, typereal], typeint), 3, CAST(r.1, ibcsub.3, i64, bitcast) + GEP(r.2, i64, ibcsub.2, ibcsub.1)
+ STORE(r.3, r.2, r.1)
+ BINOP(r.3, ibcsub.1, C64.1, add))
, addtemplates("ptr packed2 packed3 packed4 packed5 packed6", symbol3(moduleref("builtin",typeT),"setfld",[typeint, seqof.typeT, typeT], typeint), 3, CAST(r.1, ibcsub.2, ptr.ptr.i64, bitcast) + GEP(r.2, ptr.i64, r.1, ibcsub.1)
+ STORE(r.3, r.2, ibcsub.3)
+ BINOP(r.3, ibcsub.1, C64.1, add))
, addtemplates("int real ptr packed2 packed3 packed4 packed5 packed6", symbol3(moduleref("builtin",seqof.typeT),"setfld",[typeint, seqof.seqof.typeT, seqof.typeT], typeint), 3, CAST(r.1, ibcsub.2, ptr.ptr.i64, bitcast) + GEP(r.2, ptr.i64, r.1, ibcsub.1)
+ STORE(r.3, r.2, ibcsub.3)
+ BINOP(r.3, ibcsub.1, C64.1, add))
, addtemplate(abortsymbol.typeint 
, 1
, CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
)
, addtemplate(abortsymbol.typeboolean
, 1
, CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
)
, addtemplate(abortsymbol.typereal
, 2
, CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
+ CAST(r.2, r.1, double, sitofp)
)
, addtemplate(abortsymbol.typeptr 
, 2
, CALL(r.1, 0, 32768, function.[ i64, i64, ptr.i64], symboltableentry("assert"_1, function.[ i64, i64, ptr.i64]), slot.ibcfirstpara2, ibcsub.1)
+ CAST(r.2, r.1, ptr.i64, inttoptr)
)
,  addtemplates("int boolean bit byte", symbol3("internal","callidx",seqof.typeT,typeint,typeint ), 4, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[ i64, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4, 0, 32768, function.[ i64, i64, ptr.i64, i64], r.3, slot.ibcfirstpara2, ibcsub.1, ibcsub.2))
, addtemplate(symbol3("internal","callidx",seqof.typereal,typeint,typereal ), 4, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[ double, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4, 0, 32768, function.[ double, i64, ptr.i64, i64], r.3, slot.ibcfirstpara2, [ ibcsub.1, ibcsub.2]))
, addtemplates("ptr packed2 packed3 packed4 packed5 packed6"
, symbol3("internal","callidx",seqof.typeT,typeint,typeptr )
, 4
, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[ ptr.i64, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4, 0, 32768, function.[ ptr.i64, i64, ptr.i64, i64], r.3, slot.ibcfirstpara2, [ ibcsub.1, ibcsub.2])
)
, addtemplates("int   boolean byte bit ", symbol3("internal","idxseq",seqof.typeT,typeint,typeint ), 3, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1)
+ LOAD(r.3, r.2, i64))
, addtemplate(symbol3("internal","idxseq",seqof.typereal,typeint,typereal ), 4, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1)
+ LOAD(r.3, r.2, i64)
+ CAST(r.4, r.3, double, bitcast))
, addtemplates("ptr packed2 packed3 packed4 packed5 packed6",symbol3("internal","idxseq",seqof.typeT,typeint,typeptr ), 4, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1)
+ LOAD(r.3, r.2, i64)
+ CAST(r.4, r.3, ptr.i64, inttoptr))
, addtemplate(GetSeqLength, 2, GEP(r.1, i64, ibcsub.1, C64.1) + LOAD(r.2, r.1, i64))
, addtemplate(GetSeqType, 1, LOAD(r.1, ibcsub.1, i64))
, addtemplate(symbol3(moduleref("builtin", typeint),"load",[typeptr,typeint],typeint ),         2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
, addtemplate(symbol3(moduleref("builtin", typeboolean),"load",[typeptr,typeint],typeboolean ), 2, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
, addtemplate(symbol3(moduleref("builtin", typeptr),"load",[typeptr,typeint],typeptr ),         3, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)+ CAST(r.3, r.2, ptr.i64, inttoptr))
, addtemplate(symbol3(moduleref("builtin", typereal),"load",[typeptr,typeint],typereal ), 3,           GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, double, bitcast))
,addtemplates("int byte bit ptr real boolean packed2 packed3 packed4 packed5 packed6",
symbol4(moduleref."internal","allocateseq"_1,seqof.typeT,[typeint,typeint,typeint],seqof.typeT  )
    , 4
    , BINOP(r.1, ibcsub.1, C64.2, add)
     + CALL(r.2, 0, 32768, function.[ ptr.i64, i64, i64], symboltableentry("allocatespace", function.[ ptr.i64, i64, i64])
    , slot.ibcfirstpara2, r.1)
    +  STORE(r.3, r.2, ibcsub.2)
     + GEP(r.3, i64, r.2, C64.1) + STORE(r.4, r.3, ibcsub.3)
     + GEP(r.4, i64, r.2, C64.0)
    )
]
let const = for acc = empty:seq.symbol, e = toseq(uses - asset.[ Optionsym])do
 if isconst.e then
  if isrecordconstant.e then acc + e
  else { let discard = buildrecordconst(e, alltypes)acc else } let discard = buildconst(e, alltypes)
   acc
 else let discard5 = buildtemplate(theprg, alltypes, e)
  acc
/for(acc)
let discard4 = processconst.const
 empty:seq.match5

function symboltableentry(name:word)slot symboltableentry(name, i64)

Function symboltableentry(name:word, type:llvmtype)slot symboltableentry([ name], type)

Function symboltableentry(name:seq.word, type:llvmtype)slot
 modulerecord(name, [ toint.FUNCTIONDEC, typ.type, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

function processconst(toprocess:seq.symbol)int
 if isempty.toprocess then 0
 else
  processconst.for notprocessed = empty:seq.symbol, xx = toprocess do
   for args = empty:seq.int, defined = true, ele = constantcode.xx while defined do let tp = findtemplate.ele
    if isempty.tp then next(empty:seq.int, false)else next(args + arg.tp_1, true)/for(if defined then
   let discard = addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.addobject.args)
    notprocessed
   else notprocessed + xx /if)
  /for(notprocessed)

/ function buildrecordconst(s:symbol, alltypes:typedict)match5 for args = empty:seq.int, ele = constantcode.s do let tp = findtemplate.ele args + if isempty.tp then let discard = if isrecordconstant.ele then arg.buildrecordconst(ele, alltypes)else arg.buildconst(ele, alltypes)arg.(findtemplate.ele)_1 else arg.tp_1 end(addtemplate(ele, 0, emptyinternalbc,"ACTARG"_1, slot.addobject.args))

function =(a:llvmtype, b:llvmtype)boolean typ.a = typ.b

function buildconst(xx:symbol, alltypes:typedict)match5
 if isFref.xx then
 let f1 =(constantcode.xx)_1
 let mn = mangledname.f1
 let functyp = ptr.tollvmtype(alltypes, f1)
  addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, ptrtoint(functyp, symboltableentry(mn, functyp)))
 else if islit.xx then
  addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, if inmodule(xx,"$real") then Creal.value.xx else C64.value.xx)
 else if iswordseq.xx then addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.addwordseq2.worddata.xx)
 else
  assert isword.xx report"not a constant"
   addtemplate(xx, 0, emptyinternalbc,"ACTARG"_1, slot.wordref.wordname.xx )

function buildtemplate(theprg:program, alltypes:typedict, xx:symbol)match5
 { xx will not be constant }
 if islocal.xx then addtemplate(xx, 0, emptyinternalbc,"LOCAL"_1, slot.value.xx)
 else if isdefine.xx then addtemplate(xx, 0, emptyinternalbc,"DEFINE"_1, slot.toint.wordname.xx  )
 else if isblock.xx then addtemplate(xx, 0, emptyinternalbc,wordname.xx, 0, empty:seq.symbol, [ i64])
 else if isstart.xx then
 let typ = tollvmtype(alltypes, resulttype.xx)
  addtemplate(xx, 0, emptyinternalbc,wordname.xx, nopara.xx, empty:seq.symbol, [ typ])
 else if isspecial.xx then
  if isRecord.xx then
   if nopara.xx < 10 then
   let fldbc = recordcode(arithseq(nopara.xx, 1, ibcfirstpara2 + 1), tollvmtypelist(alltypes, xx) << 2, 0, true)
    addtemplate(xx, regno.fldbc, bc.fldbc)
   else addtemplate(xx, 0, emptyinternalbc,wordname.xx, nopara.xx, empty:seq.symbol, tollvmtypelist(alltypes, xx) << 2)
  else if isSequence.xx then
   if nopara.xx < 10 then
   let fldbc = sequencecode(arithseq(nopara.xx, 1, ibcfirstpara2 + 1), tollvmtype(alltypes, parameter.modname.xx), 0, true)
    addtemplate(xx, regno.fldbc, bc.fldbc)
   else
    addtemplate(xx, 0, emptyinternalbc,wordname.xx, nopara.xx, empty:seq.symbol, [ tollvmtype(alltypes, parameter.modname.xx)])
  else if isbr.xx then addtemplate(xx, brt.xx, emptyinternalbc,wordname.xx, brf.xx, empty:seq.symbol, [ i64])
  else if isloopblock.xx then
   addtemplate(xx, firstvar.xx, emptyinternalbc,wordname.xx, nopara.xx, empty:seq.symbol, for oldacc = [ tollvmtype(alltypes, resulttype.xx)], e20 = paratypes.xx do oldacc + tollvmtype(alltypes, e20)/for(oldacc))
  else addtemplate(xx, 0, emptyinternalbc,wordname.xx, nopara.xx, empty:seq.symbol, [ i64])
 else
  { handle builtin package }
  let intable = findtemplate.xx
   if length.intable > 0 then intable_1
   else if wordname.xx = "global"_1 ∧ inmodule(xx ,"$global")then
    addtemplate(xx, 1, GEP(r.1, i64, slot.global([ mangledname.xx], i64, C64.0)))
   else if wordname.xx = "createthreadY"_1 ∧ inmodule(xx , "builtin") then
   let l=for acc = empty:seq.llvmtype, e = paratypes.xx << 3 do acc + tollvmtype(alltypes, e)
          /for(acc+tollvmtype(alltypes, parameter.modname.xx) )
         assert true report "TTT"+print.xx+for ll="",e=l do ll+print.e /for(ll)
     addtemplate(xx, 0, emptyinternalbc,wordname.xx, nopara.xx, empty:seq.symbol,l)
   else
     call(alltypes, xx,"CALL"_1, getCode(theprg, xx), mangledname.xx)

function call(alltypes:typedict, xx:symbol, type:word, code:seq.symbol, symname:word)match5
let list = tollvmtypelist(alltypes, xx)
let functype = function.list
let newcode = CALLSTART(1, 0, 32768, typ.functype, toint.symboltableentry(symname, functype), if type = "CALL"_1 then nopara.xx + 1 else nopara.xx)
 addtemplate(xx, 1, newcode, type, nopara.xx, code, list)

Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
let args = if action.t = "CALL"_1 then empty:seq.int
else subseq(argstack, length.argstack - arg.t + 1, length.argstack)
 processtemplate(parts.t, deltaoffset, args)

type recordcoderesult is regno:int, bc:internalbc

Export regno(recordcoderesult)int

Export bc(recordcoderesult)internalbc

function setnextfld(bc:internalbc, args:seq.int, i:int, types:seq.llvmtype, regno:int, pint:int, preal:int, pptr:int)recordcoderesult
 if i > length.args then recordcoderesult(regno, bc)
 else
  let typ = types_i
   if typ = double then
    if preal = 0 then
     setnextfld(bc + CAST(r(regno + 1), r.pint, ptr.double, bitcast), args, i, types, regno + 1, pint, regno + 1, pptr)
    else
     let newbc = GEP(r(regno + 1), double, r.preal, C64(i - 1))
     + STORE(r(regno + 2), r(regno + 1), slot.args_i)
      setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)
   else if typ = ptr.i64 then
    if pptr = 0 then
     setnextfld(bc + CAST(r(regno + 1), r.pint, ptr.ptr.i64, bitcast), args, i, types, regno + 1, pint, preal, regno + 1)
    else
     let newbc = GEP(r(regno + 1), ptr.i64, r.pptr, C64(i - 1))
     + STORE(r(regno + 2), r(regno + 1), slot.args_i)
      setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)
   else
    let newbc = GEP(r(regno + 1), i64, r.pint, C64(i - 1))
    + STORE(r(regno + 2), r(regno + 1), slot.args_i)
     setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)

Function sequencecode(args:seq.int, type:llvmtype, lastreg:int, template:boolean)recordcoderesult
 recordcode([ toint.C64.0, toint.C64.length.args] + args, [ i64, i64] + constantseq(length.args, type), lastreg, template)

Function recordcode(args:seq.int, types:seq.llvmtype, lastreg:int, template:boolean)recordcoderesult
let firstpara = if template then slot.ibcfirstpara2 else r.1
let newcode = CALL(r(lastreg + 1), 0, 32768, function.[ ptr.i64, i64, i64], symboltableentry("allocatespace", function.[ ptr.i64, i64, i64]), firstpara, C64.length.args)
let c = setnextfld(newcode, args, 1, types, lastreg + 1, lastreg + 1, 0, 0)
 if template then
  recordcoderesult(regno.c + 1, bc.c + GEP(r(regno.c + 1), i64, r(lastreg + 1), C64.0))
 else c