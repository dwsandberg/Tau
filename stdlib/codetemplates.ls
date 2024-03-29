Module codetemplates

use bits

use internalbc

use libraryModule

use llvm

use llvmconstants

use persistant

use standard

use symbol

use textio

use typedict

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

use set.word

use seq.seq.int

use seq.seq.symbol

Export constdata seq.slot

Export wordref(w:word)int

Export addliblib(libname:seq.word, syms:seq.symbol, libmods:seq.libraryModule, code:seq.seq.symbolref, profiledata:int, dependlibs:seq.word, entrypoint:slot, symboladdresses:int)int

Function tollvmtype(alltypes:typedict, s:symbol)llvmtype
if s = Optionsym then function.[i64, i64, i64, i64]else function.tollvmtypelist(alltypes, s)

function tollvmtypelist(alltypes:typedict, s:symbol)seq.llvmtype
assert resulttype.s ≠ typeT report"TTT" + print.s
let starttypes = [tollvmtype(alltypes, resulttype.s), i64]
for acc = starttypes, @e ∈ paratypes.s do
 assert @e ≠ typeT report"TTTP" + print.s
 acc + tollvmtype(alltypes, @e)
/for(acc)

Function tollvmtype(alltypes:typedict, s:mytype)llvmtype
if isseq.s then ptr.i64
else if abstracttypename.s = "process"_1 then ptr.i64
else
 let kind = basetype(s, alltypes)
 if kind = typeint ∨ kind = typeboolean then i64
 else if kind = typereal then double else ptr.i64

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Export type:match5

Export length(match5)int{no of instruction that return results}

Export action(match5)word

Export arg(match5)int

Export sym(match5)symbol

Function firstvar(a:match5)int length.a

Function brt(a:match5)int length.a

Function brf(a:match5)int arg.a

Export llvmtypelist(match5)seq.llvmtype

type match5 is sym:symbol, length:int, parts:internalbc, action:word, arg:int, llvmtypelist:seq.llvmtype

Function functype(m:match5)llvmtype function.llvmtypelist.m

Function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:int, llvmtypelist:seq.llvmtype)match5
let m = match5(sym, length, parts, action, arg, llvmtypelist)
let discard = encode.m
m

Function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:slot)match5
addtemplate(sym, length, parts, action, toint.arg, [i64])

Function addtemplate(sym:symbol, length:int, b:internalbc)match5
addtemplate(sym, length, b, "TEMPLATE"_1, slot.nopara.sym)

function addtemplates(t:seq.mytype, sym:symbol, length:int, b:internalbc)match5
first.for acc = empty:seq.match5, e ∈ t do[addtemplate(replaceTsymbol(e, sym), length, b)]/for(acc)

Function findtemplate(d:symbol)seq.match5 findencode.match5(d, 0, emptyinternalbc, "NOTFOUND"_1, 0, [i64])

Export type:symbol

Function _(m:seq.match5, d:symbol)match5
let e = findtemplate.d
assert not.isempty.e report"LL codetemplates" + print.d + stacktrace
e_1

function =(a:match5, b:match5)boolean sym.a = sym.b

function hash(a:match5)int fsighash.sym.a

Function assignencoding(a:match5)int nextencoding.a

Function funcdec(alltypes:typedict, i:symbol, symname:word)int
toint.modulerecord([symname]
, [toint.FUNCTIONDEC, typ.tollvmtype(alltypes, i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
)

Function initmap5 seq.match5
[addtemplate(symbol(internalmod, "packedindex", seqof.typebit, typeint, typeint)
, 8
, BINOP(r.1, ibcsub.2, C64.1, sub) + BINOP(r.2, r.1, C64.6, lshr) + BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
+ LOAD(r.5, r.4, i64)
+ BINOP(r.6, r.1, C64.63, and)
+ BINOP(r.7, r.5, r.6, lshr)
+ BINOP(r.8, r.7, C64.1, and)
)
, addtemplate(symbol(internalmod, "packedindex", seqof.typebyte, typeint, typeint)
, 9
, BINOP(r.1, ibcsub.2, C64.1, sub) + BINOP(r.2, r.1, C64.3, lshr) + BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
+ LOAD(r.5, r.4, i64)
+ BINOP(r.6, r.1, C64.7, and)
+ BINOP(r.7, r.6, C64.3, shl)
+ BINOP(r.8, r.5, r.7, lshr)
+ BINOP(r.9, r.8, C64.255, and)
)
, addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_1, typeint, typeptr)
, 4
, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.2, mul) + BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
)
, addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_2, typeint, typeptr)
, 4
, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.3, mul) + BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
)
, addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_3, typeint, typeptr)
, 4
, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.4, mul) + BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
)
, addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_4, typeint, typeptr)
, 4
, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.5, mul) + BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
)
, addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_5, typeint, typeptr)
, 4
, BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.6, mul) + BINOP(r.3, r.2, C64.2, add)
+ GEP(r.4, i64, ibcsub.1, r.3)
)
, addtemplate(symbol(internalmod, "toint", typebyte, typeint), 0, emptyinternalbc)
, addtemplate(symbol(internalmod, "toint", typebit, typeint), 0, emptyinternalbc)
, addtemplate(symbol(internalmod, "toptr", seqof.typeword, typeptr), 0, emptyinternalbc)
, {addtemplate(NullptrOp, 1, CAST(r.1, C64.0, ptr.i64, inttoptr)), addtemplate(STKRECORDOp, 3, ALLOCA(r.1, ptr.ptr 
.i64, i64, C64.2, 0)+STORE(r.2, r.1, ibcsub.1)+GEP(r.2, ptr.i64, r.1, C64.1)+STORE(r.3, r.2, ibcsub.2)+GEP(r.3, 
ptr.i64, r.1, C64.0)), }
addtemplate(symbol(internalmod, "bitcast", typeptr, typeint)
, 1
, CAST(r.1, ibcsub.1, i64, ptrtoint)
)
, addtemplate(symbol(internalmod, "bitcast", typeint, typeptr)
, 1
, CAST(r.1, ibcsub.1, ptr.i64, inttoptr)
)
, addtemplate(symbol(internalmod, "bitcast", typeint, typebyte), 0, emptyinternalbc)
, addtemplate(symbol(internalmod, "GEP", seqof.typeint, typeint, typeint)
, 2
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + CAST(r.2, r.1, i64, ptrtoint)
)
, addtemplates([typebit, typebyte, typeint, typeptr, typereal] + packedtypes
, symbol4(internalmod, "toseq"_1, seqof.typeT, [typeptr], typeptr)
, 0
, emptyinternalbc
)
, addtemplate(symbol(internalmod, "intpart", typereal, typeint)
, 1
, CAST(r.1, ibcsub.1, i64, fptosi)
)
, addtemplate(symbol(internalmod, "toreal", typeint, typereal)
, 1
, CAST(r.1, ibcsub.1, double, sitofp)
)
, addtemplate(symbol(internalmod, "-", typereal, typereal, typereal)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, sub)
)
, addtemplate(symbol(internalmod, "+", typereal, typereal, typereal)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, add)
)
, addtemplate(symbol(internalmod, "*", typereal, typereal, typereal)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, mul)
)
, addtemplate(symbol(internalmod, "/", typereal, typereal, typereal)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, sdiv)
)
, addtemplate(symbol(internalmod, "casttoreal", typeint, typereal)
, 1
, CAST(r.1, ibcsub.1, double, bitcast)
)
, addtemplate(symbol(internalmod, "representation", typereal, typeint)
, 1
, CAST(r.1, ibcsub.1, i64, bitcast)
)
, addtemplate(symbol(internalmod, "?", typereal, typereal, typeref."ordering standard")
, 5
, CMP2(r.1, ibcsub.1, ibcsub.2, 3) + CAST(r.2, r.1, i64, zext) + CMP2(r.3, ibcsub.1, ibcsub.2, 2)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add)
)
, addtemplate(symbol(internalmod, "?", typeint, typeint, typeref."ordering standard")
, 5
, CMP2(r.1, ibcsub.1, ibcsub.2, 39) + CAST(r.2, r.1, i64, zext) + CMP2(r.3, ibcsub.1, ibcsub.2, 38)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add)
)
, addtemplate(symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
, 1
, GEP(r.1, i64, ibcsub.1, ibcsub.2)
)
, addtemplate(symbol(internalmod, "not", typeboolean, typeboolean)
, 1
, BINOP(r.1, ibcsub.1, C64.1, xor)
)
, addtemplate(symbol(internalmod, ">", typeint, typeint, typeboolean)
, 2
, CMP2(r.1, ibcsub.1, ibcsub.2, 38) + CAST(r.2, r.1, i64, zext)
)
, addtemplate(symbol(internalmod, "=", typeboolean, typeboolean, typeboolean)
, 2
, CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext)
)
, addtemplate(symbol(internalmod, "=", typeint, typeint, typeboolean)
, 2
, CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext)
)
, addtemplate(symbol(internalmod, "-", typeint, typeint, typeint)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, sub)
)
, addtemplate(symbol(internalmod, "+", typeint, typeint, typeint)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, add)
)
, addtemplate(symbol(internalmod, "*", typeint, typeint, typeint)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, mul)
)
, addtemplate(symbol(internalmod, "/", typeint, typeint, typeint)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, sdiv)
)
, addtemplate(symbol(internalmod, "<<", typebits, typeint, typebits)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, shl)
)
, addtemplate(symbol(internalmod, ">>", typebits, typeint, typebits)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, lshr)
)
, addtemplate(symbol(internalmod, "∧", typebits, typebits, typebits)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, and)
)
, addtemplate(symbol(internalmod, "∨", typebits, typebits, typebits)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, or)
)
, addtemplate(symbol(internalmod, "xor", typebits, typebits, typebits)
, 1
, BINOP(r.1, ibcsub.1, ibcsub.2, xor)
)
, addtemplate(symbol(internalmod, "set", [typeptr, typeint], typeptr)
, 1
, STORE(r.1, ibcsub.1, ibcsub.2) + GEP(r.1, i64, ibcsub.1, C64.1)
)
, addtemplate(symbol(internalmod, "set", [typeptr, typeptr], typeptr)
, 2
, CAST(r.1, ibcsub.1, ptr.ptr.i64, bitcast) + STORE(r.2, r.1, ibcsub.2)
+ GEP(r.2, i64, ibcsub.1, C64.1)
)
, addtemplate(abortsymbol.typeint
, 1
, CALL(r.1
, 0
, 32768
, function.[i64, i64, ptr.i64]
, symboltableentry("assert", function.[i64, i64, ptr.i64])
, slot.ibcfirstpara2
, ibcsub.1
)
)
, addtemplate(abortsymbol.typebyte
, 1
, CALL(r.1
, 0
, 32768
, function.[i64, i64, ptr.i64]
, symboltableentry("assert", function.[i64, i64, ptr.i64])
, slot.ibcfirstpara2
, ibcsub.1
)
)
, addtemplate(abortsymbol.typeboolean
, 1
, CALL(r.1
, 0
, 32768
, function.[i64, i64, ptr.i64]
, symboltableentry("assert", function.[i64, i64, ptr.i64])
, slot.ibcfirstpara2
, ibcsub.1
)
)
, addtemplate(abortsymbol.typereal
, 2
, CALL(r.1
, 0
, 32768
, function.[i64, i64, ptr.i64]
, symboltableentry("assert", function.[i64, i64, ptr.i64])
, slot.ibcfirstpara2
, ibcsub.1
)
+ CAST(r.2, r.1, double, sitofp)
)
, addtemplates(packedtypes + typeptr
, abortsymbol.typeT
, 2
, CALL(r.1
, 0
, 32768
, function.[i64, i64, ptr.i64]
, symboltableentry("assert", function.[i64, i64, ptr.i64])
, slot.ibcfirstpara2
, ibcsub.1
)
+ CAST(r.2, r.1, ptr.i64, inttoptr)
)
, addtemplates([typeint, typeboolean, typebyte, typebit]
, symbol(internalmod, "callidx", seqof.typeT, typeint, typeint)
, 4
, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[i64, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4, 0, 32768, function.[i64, i64, ptr.i64, i64], r.3, slot.ibcfirstpara2, ibcsub.1, ibcsub.2)
)
, addtemplate(symbol(internalmod, "callidx", seqof.typereal, typeint, typereal)
, 4
, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[double, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4
, 0
, 32768
, function.[double, i64, ptr.i64, i64]
, r.3
, slot.ibcfirstpara2
, [ibcsub.1, ibcsub.2]
)
)
, addtemplates(packedtypes + typeptr
, symbol(internalmod, "callidx", seqof.typeT, typeint, typeptr)
, 4
, GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
+ CAST(r.3, r.2, ptr.function.[ptr.i64, i64, ptr.i64, i64], inttoptr)
+ CALL(r.4
, 0
, 32768
, function.[ptr.i64, i64, ptr.i64, i64]
, r.3
, slot.ibcfirstpara2
, [ibcsub.1, ibcsub.2]
)
)
, addtemplates([typeint, typeboolean, typebyte, typebit]
, symbol(internalmod, "idxseq", seqof.typeT, typeint, typeint)
, 3
, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1) + LOAD(r.3, r.2, i64)
)
, addtemplate(symbol(internalmod, "idxseq", seqof.typereal, typeint, typereal)
, 4
, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1) + LOAD(r.3, r.2, i64)
+ CAST(r.4, r.3, double, bitcast)
)
, addtemplates(packedtypes + typeptr
, symbol(internalmod, "idxseq", seqof.typeT, typeint, typeptr)
, 4
, BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1) + LOAD(r.3, r.2, i64)
+ CAST(r.4, r.3, ptr.i64, inttoptr)
)
, addtemplate(GetSeqLength, 2, GEP(r.1, i64, ibcsub.1, C64.1) + LOAD(r.2, r.1, i64))
, addtemplate(GetSeqType, 1, LOAD(r.1, ibcsub.1, i64))
, addtemplate(symbol(builtinmod.typeint, "load", [typeptr, typeint], typeint)
, 2
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
)
, addtemplate(symbol(builtinmod.typeboolean, "load", [typeptr, typeint], typeboolean)
, 2
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
)
, addtemplate(symbol(builtinmod.typeptr, "load", [typeptr, typeint], typeptr)
, 3
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64) + CAST(r.3, r.2, ptr.i64, inttoptr)
)
, addtemplate(symbol(builtinmod.typereal, "load", [typeptr, typeint], typereal)
, 3
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64) + CAST(r.3, r.2, double, bitcast)
)
, addtemplate(symbol(builtinmod.typeint, "fld", [typeptr, typeint], typeint)
, 2
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
)
, addtemplate(symbol(builtinmod.typebyte, "fld", [typeptr, typeint], typebyte)
, 2
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
)
, addtemplate(symbol(builtinmod.typeboolean, "fld", [typeptr, typeint], typeboolean)
, 2
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64)
)
, addtemplates(packedtypes + typeptr
, symbol(builtinmod.typeT, "fld", [typeptr, typeint], typeptr)
, 3
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64) + CAST(r.3, r.2, ptr.i64, inttoptr)
)
, addtemplate(symbol(builtinmod.typereal, "fld", [typeptr, typeint], typereal)
, 3
, GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64) + CAST(r.3, r.2, double, bitcast)
)
]

Function symboltableentry(name:seq.word, type:llvmtype)slot
modulerecord(name, [toint.FUNCTIONDEC, typ.type, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

function =(a:llvmtype, b:llvmtype)boolean typ.a = typ.b

Function buildconst(xx:symbol, alltypes:typedict)match5
if isRealLit.xx then addtemplate(xx, 0, emptyinternalbc, "ACTARG"_1, Creal.value.xx)
else if isIntLit.xx then addtemplate(xx, 0, emptyinternalbc, "ACTARG"_1, C64.value.xx)
else if iswordseq.xx then
 addtemplate(xx, 0, emptyinternalbc, "ACTARG"_1, slot.addwordseq2.worddata.xx)
else if xx = Littrue then addtemplate(xx, 0, emptyinternalbc, "ACTARG"_1, C64.1)
else if xx = Litfalse then addtemplate(xx, 0, emptyinternalbc, "ACTARG"_1, C64.0)
else
 assert isword.xx report"not a constant" + print.xx
 addtemplate(xx, 0, emptyinternalbc, "ACTARG"_1, slot.wordref.wordname.xx)

Function buildspecial(xx:symbol, alltypes:typedict)match5
if islocal.xx then addtemplate(xx, 0, emptyinternalbc, "LOCAL"_1, slot.value.xx)
else if isdefine.xx then addtemplate(xx, 0, emptyinternalbc, "DEFINE"_1, slot.value.xx)
else if isblock.xx then addtemplate(xx, 0, emptyinternalbc, wordname.xx, 0, [i64])
else if isstart.xx then
 let typ = tollvmtype(alltypes, resulttype.xx)
 addtemplate(xx, 0, emptyinternalbc, wordname.xx, nopara.xx, [typ])
else if isRecord.xx then
 if nopara.xx < 10 then
  let fldbc = 
   recordcode(arithseq(nopara.xx, 1, ibcfirstpara2 + 1), tollvmtypelist(alltypes, xx) << 2, 0, true)
  addtemplate(xx, regno.fldbc, bc.fldbc)
 else addtemplate(xx, 0, emptyinternalbc, wordname.xx, nopara.xx, tollvmtypelist(alltypes, xx) << 2)
else if isSequence.xx then
 if nopara.xx < 10 then
  let fldbc = 
   sequencecode(arithseq(nopara.xx, 1, ibcfirstpara2 + 1), tollvmtype(alltypes, para.module.xx), 0, true)
  addtemplate(xx, regno.fldbc, bc.fldbc)
 else
  addtemplate(xx
  , 0
  , emptyinternalbc
  , "SEQUENCE"_1
  , nopara.xx
  , [tollvmtype(alltypes, para.module.xx)]
  )
else if isbr.xx then addtemplate(xx, brt.xx, emptyinternalbc, wordname.xx, brf.xx, [i64])
else if isloopblock.xx then
 addtemplate(xx
 , firstvar.xx
 , emptyinternalbc
 , wordname.xx
 , nopara.xx
 , for oldacc = [tollvmtype(alltypes, resulttype.xx)], e20 ∈ paratypes.xx do oldacc + tollvmtype(alltypes, e20)/for(oldacc)
 )
else if iscontinue.xx then addtemplate(xx, 0, emptyinternalbc, "CONTINUE"_1, nopara.xx, [i64])
else addtemplate(xx, 0, emptyinternalbc, wordname.xx, nopara.xx, [i64])

Function call(alltypes:typedict, xx:symbol, type:word, symname:word)match5
let list = tollvmtypelist(alltypes, xx)
let functype = function.list
let newcode = 
 CALLSTART(1
 , 0
 , 32768
 , typ.functype
 , toint.symboltableentry([symname], functype)
 , if type = "CALL"_1 then nopara.xx + 1 else nopara.xx
 )
addtemplate(xx, 1, newcode, type, nopara.xx, list)

Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
let args = 
 if action.t = "CALL"_1 then empty:seq.int
 else subseq(argstack, length.argstack - arg.t + 1, length.argstack)
processtemplate(parts.t, deltaoffset, args)

type recordcoderesult is regno:int, bc:internalbc

Export regno(recordcoderesult)int

Export bc(recordcoderesult)internalbc

Export type:recordcoderesult

function setnextfld(bc:internalbc, args:seq.int, i:int, types:seq.llvmtype, regno:int, pint:int, preal:int, pptr:int)recordcoderesult
if i > length.args then recordcoderesult(regno, bc)
else
 let typ = types_i
 if typ = double then
  if preal = 0 then
   setnextfld(bc + CAST(r(regno + 1), r.pint, ptr.double, bitcast)
   , args
   , i
   , types
   , regno + 1
   , pint
   , regno + 1
   , pptr
   )
  else
   let newbc = GEP(r(regno + 1), double, r.preal, C64(i - 1)) + STORE(r(regno + 2), r(regno + 1), slot.args_i)
   setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)
 else if typ = ptr.i64 then
  if pptr = 0 then
   setnextfld(bc + CAST(r(regno + 1), r.pint, ptr.ptr.i64, bitcast)
   , args
   , i
   , types
   , regno + 1
   , pint
   , preal
   , regno + 1
   )
  else
   let newbc = GEP(r(regno + 1), ptr.i64, r.pptr, C64(i - 1)) + STORE(r(regno + 2), r(regno + 1), slot.args_i)
   setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)
 else
  let newbc = GEP(r(regno + 1), i64, r.pint, C64(i - 1)) + STORE(r(regno + 2), r(regno + 1), slot.args_i)
  setnextfld(bc + newbc, args, i + 1, types, regno + 1, pint, preal, pptr)

Function sequencecode(args:seq.int, type:llvmtype, lastreg:int, template:boolean)recordcoderesult
recordcode([toint.C64.0, toint.C64.length.args] + args
, [i64, i64] + constantseq(length.args, type)
, lastreg
, template
)

Function recordcode(args:seq.int, types:seq.llvmtype, lastreg:int, template:boolean)recordcoderesult
let firstpara = if template then slot.ibcfirstpara2 else r.1
let newcode = 
 CALL(r(lastreg + 1)
 , 0
 , 32768
 , function.[ptr.i64, i64, i64]
 , symboltableentry("allocatespace", function.[ptr.i64, i64, i64])
 , firstpara
 , C64.length.args
 )
let c = setnextfld(newcode, args, 1, types, lastreg + 1, lastreg + 1, 0, 0)
if template then recordcoderesult(regno.c + 1, bc.c + GEP(r(regno.c + 1), i64, r(lastreg + 1), C64.0))
else c 