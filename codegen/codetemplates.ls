Module codetemplates

use internalbc

use llvm

use llvmconstants

use otherseq.llvmtype

use encoding.match5

use seq.match5

use seq.mytype

use persistant

use seq.slot

use standard

use symbol

use seq.symbol

use typedict

Export type:match5

Export action(match5) word

Export arg(match5) int

Export length(match5) int {no of instruction that return results}

Export llvmtypelist(match5) seq.llvmtype

Export sym(match5) symbol

Export type:recordcoderesult

Export bc(recordcoderesult) internalbc

Export regno(recordcoderesult) int

Export wordref(w:word) int {From persistant}

Export constdata seq.slot {From persistant}

Export type:symbol {From symbol}

Function tollvmtype(alltypes:typedict, s:symbol) llvmtype
function.tollvmtypelist(alltypes, s)

Function tollvmtypelist(alltypes:typedict, s:symbol) seq.llvmtype
assert resulttype.s ≠ typeT report "TTT $(s)"
let starttypes = [tollvmtype(alltypes, resulttype.s), i64],
for acc = starttypes, @e ∈ paratypes.s do
 assert @e ≠ typeT report "TTTP $(s)",
 acc + tollvmtype(alltypes, @e)
/do acc

Function tollvmtype(alltypes:typedict, s:mytype) llvmtype
if isseq.s then
 ptr.i64
else if abstracttypename.s = "process"_1 then
 ptr.i64
else
 let kind = basetype(s, alltypes),
 if kind = typeint ∨ kind = typeboolean then
  i64
 else if kind = typereal then double else ptr.i64

Function firstvar(a:match5) int length.a

Function brt(a:match5) int length.a

Function brf(a:match5) int arg.a

type match5 is sym:symbol
 , length:int
 , parts:internalbc
 , action:word
 , arg:int
 , llvmtypelist:seq.llvmtype

Function empty:match5 match5
match5(Lit.0, 0, emptyinternalbc, "?"_1, 0, empty:seq.llvmtype)

Function functype(m:match5) llvmtype function.llvmtypelist.m

Function addtemplate(sym:symbol
 , length:int
 , parts:internalbc
 , action:word
 , arg:int
 , llvmtypelist:seq.llvmtype) match5
let m = match5(sym, length, parts, action, arg, llvmtypelist)
let discard = encode.m,
m

Function addtemplate(sym:symbol, length:int, parts:internalbc, action:word, arg:slot) match5
addtemplate(sym, length, parts, action, toint.arg, [i64])

Function addtemplate(sym:symbol, length:int, b:internalbc) match5
addtemplate(sym, length, b, "TEMPLATE"_1, slot.nopara.sym)

function addtemplates(t:seq.mytype, sym:symbol, length:int, b:internalbc) match5
first.for acc = empty:seq.match5, e ∈ t do
 [addtemplate(replaceTsymbol(e, sym), length, b)]
/do acc

Function findtemplate(d:symbol) seq.match5
findencode.match5(d, 0, emptyinternalbc, "NOTFOUND"_1, 0, [i64])

function =(a:match5, b:match5) boolean sym.a = sym.b

function hash(a:match5) int hash.sym.a

Function templatesyms seq.symbol
for acc = empty:seq.symbol, m ∈ encodingdata:match5 do acc + sym.m /do acc

Function funcdec(alltypes:typedict, i:symbol, symname:word) int
toint.modulerecord([symname]
 , [toint.FUNCTIONDEC, typ.tollvmtype(alltypes, i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

Function initmap5(liblist:seq.slot) seq.match5
[addtemplate(Littrue, 0, emptyinternalbc, "ACTARG"_1, C64.1)
 , addtemplate(Litfalse, 0, emptyinternalbc, "ACTARG"_1, C64.0)
 , addtemplate(symbol(internalmod, "packedindex", seqof.typebyte, typeint, typeint)
  , 9
  , BINOP(r.1, ibcsub.2, C64.1, sub) + BINOP(r.2, r.1, C64.3, lshr) + BINOP(r.3, r.2, C64.2, add)
  + GEP(r.4, i64, ibcsub.1, r.3)
  + LOAD(r.5, r.4, i64)
  + BINOP(r.6, r.1, C64.7, and)
  + BINOP(r.7, r.6, C64.3, shl)
  + BINOP(r.8, r.5, r.7, lshr)
  + BINOP(r.9, r.8, C64.255, and))
 , addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_1, typeint, typeptr)
  , 4
  , BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.2, mul) + BINOP(r.3, r.2, C64.2, add)
  + GEP(r.4, i64, ibcsub.1, r.3))
 , addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_2, typeint, typeptr)
  , 4
  , BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.3, mul) + BINOP(r.3, r.2, C64.2, add)
  + GEP(r.4, i64, ibcsub.1, r.3))
 , addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_3, typeint, typeptr)
  , 4
  , BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.4, mul) + BINOP(r.3, r.2, C64.2, add)
  + GEP(r.4, i64, ibcsub.1, r.3))
 , addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_4, typeint, typeptr)
  , 4
  , BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.5, mul) + BINOP(r.3, r.2, C64.2, add)
  + GEP(r.4, i64, ibcsub.1, r.3))
 , addtemplate(symbol(internalmod, "packedindex", seqof.packedtypes_5, typeint, typeptr)
  , 4
  , BINOP(r.1, ibcsub.2, C64.-1, add) + BINOP(r.2, r.1, C64.6, mul) + BINOP(r.3, r.2, C64.2, add)
  + GEP(r.4, i64, ibcsub.1, r.3))
 , addtemplate(symbol(internalmod, "toint", typebyte, typeint), 0, emptyinternalbc)
 , addtemplate(symbol(internalmod, "toptr", seqof.typeword, typeptr), 0, emptyinternalbc)
 , {addtemplate (NullptrOp, 1, CAST (r.1, C64.0, ptr.i64, inttoptr)), addtemplate (STKRECORDOp, 3, ALLOCA
  (r.1, ptr.ptr.i64, i64, C64.2, 0)+STORE (r.2, r.1, ibcsub.1)+GEP (r.2, ptr.i64, r.1, C64.1)+STORE
  (r.3, r.2, ibcsub.2)+GEP (r.3, ptr.i64, r.1, C64.0)),}
 addtemplate(symbol(internalmod, "bitcast", typeptr, typeint), 1, CAST(r.1, ibcsub.1, i64, ptrtoint))
 , addtemplate(symbol(internalmod, "bitcast", typeint, typeptr), 1, CAST(r.1, ibcsub.1, ptr.i64, inttoptr))
 , addtemplate(symbol(internalmod, "bitcast", typeint, typebyte), 0, emptyinternalbc)
 , addtemplate(symbol(internalmod, "GEP", seqof.typeint, typeint, typeint)
  , 2
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + CAST(r.2, r.1, i64, ptrtoint))
 , addtemplate(symbol(internalmod, "intpart", typereal, typeint), 1, CAST(r.1, ibcsub.1, i64, fptosi))
 , addtemplate(symbol(internalmod, "toreal", typeint, typereal), 1, CAST(r.1, ibcsub.1, double, sitofp))
 , addtemplate(symbol(internalmod, "-", typereal, typereal, typereal)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, sub))
 , addtemplate(symbol(internalmod, "+", typereal, typereal, typereal)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, add))
 , addtemplate(symbol(internalmod, "*", typereal, typereal, typereal)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, mul))
 , addtemplate(symbol(internalmod, "/", typereal, typereal, typereal)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, sdiv))
 , addtemplate(symbol(internalmod, "casttoreal", typeint, typereal)
  , 1
  , CAST(r.1, ibcsub.1, double, bitcast))
 , addtemplate(symbol(internalmod, "representation", typereal, typeint)
  , 1
  , CAST(r.1, ibcsub.1, i64, bitcast))
 , addtemplate(symbol(internalmod, ">1", typereal, typereal, typeref."ordering standard *")
  , 5
  , CMP2(r.1, ibcsub.1, ibcsub.2, 3) + CAST(r.2, r.1, i64, zext)
  + CMP2(r.3, ibcsub.1, ibcsub.2, 2)
  + CAST(r.4, r.3, i64, zext)
  + BINOP(r.5, r.2, r.4, add))
 , addtemplate(symbol(internalmod, ">1", typeint, typeint, typeref."ordering standard *")
  , 5
  , CMP2(r.1, ibcsub.1, ibcsub.2, 39) + CAST(r.2, r.1, i64, zext)
  + CMP2(r.3, ibcsub.1, ibcsub.2, 38)
  + CAST(r.4, r.3, i64, zext)
  + BINOP(r.5, r.2, r.4, add))
 , addtemplate(symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
  , 1
  , GEP(r.1, i64, ibcsub.1, ibcsub.2))
 , addtemplate(symbol(internalmod, "not", typeboolean, typeboolean), 1, BINOP(r.1, ibcsub.1, C64.1, xor))
 , addtemplate(symbol(internalmod, ">", typeint, typeint, typeboolean)
  , 2
  , CMP2(r.1, ibcsub.1, ibcsub.2, 38) + CAST(r.2, r.1, i64, zext))
 , addtemplate(symbol(internalmod, "=", typeboolean, typeboolean, typeboolean)
  , 2
  , CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext))
 , addtemplate(symbol(internalmod, "=", typeint, typeint, typeboolean)
  , 2
  , CMP2(r.1, ibcsub.1, ibcsub.2, 32) + CAST(r.2, r.1, i64, zext))
 , addtemplate(symbol(internalmod, "-", typeint, typeint, typeint), 1, BINOP(r.1, ibcsub.1, ibcsub.2, sub))
 , addtemplate(symbol(internalmod, "+", typeint, typeint, typeint), 1, BINOP(r.1, ibcsub.1, ibcsub.2, add))
 , addtemplate(symbol(internalmod, "*", typeint, typeint, typeint), 1, BINOP(r.1, ibcsub.1, ibcsub.2, mul))
 , addtemplate(symbol(internalmod, "/", typeint, typeint, typeint)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, sdiv))
 , addtemplate(symbol(internalmod, "<<", typebits, typeint, typebits)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, shl))
 , addtemplate(symbol(internalmod, ">>", typebits, typeint, typebits)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, lshr))
 , addtemplate(symbol(internalmod, "∧", typebits, typebits, typebits)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, and))
 , addtemplate(symbol(internalmod, "∨", typebits, typebits, typebits)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, or))
 , addtemplate(symbol(internalmod, "⊻", typebits, typebits, typebits)
  , 1
  , BINOP(r.1, ibcsub.1, ibcsub.2, xor))
 , addtemplate(symbol(internalmod, "set", [typeptr, typeint], typeptr)
  , 1
  , STORE(r.1, ibcsub.1, ibcsub.2) + GEP(r.1, i64, ibcsub.1, C64.1))
 , addtemplate(symbol(internalmod, "set", [typeptr, typeptr], typeptr)
  , 2
  , CAST(r.1, ibcsub.1, ptr.ptr.i64, bitcast) + STORE(r.2, r.1, ibcsub.2)
  + GEP(r.2, i64, ibcsub.1, C64.1))
 , addtemplate(symbol(internalmod, "clock", typeint)
  , 1
  , CALL(r.1, 0, 32768, function.[i64], symboltableentry("threadclock", function.[i64])))
 , {addtemplate (symbol (internalmod," spacecount", typeint), 1, LOAD (r.1, symboltableentry (" spacecount
  ", i64), i64)),}
 addtemplates([typeint, typeboolean, typebyte]
  , symbol(internalmod, "callidx", seqof.typeT, typeint, typeint)
  , 4
  , GEP(r.1, i64, ibcsub.1, C64.0) + LOAD(r.2, r.1, i64)
  + CAST(r.3, r.2, ptr.function.[i64, i64, ptr.i64, i64], inttoptr)
  + CALL(r.4
   , 0
   , 32768
   , function.[i64, i64, ptr.i64, i64]
   , r.3
   , slot.ibcfirstpara2
   , ibcsub.1
   , ibcsub.2)
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
   , [ibcsub.1, ibcsub.2])
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
   , [ibcsub.1, ibcsub.2])
  )
 , addtemplates([typeint, typeboolean, typebyte]
  , symbol(internalmod, "idxseq", seqof.typeT, typeint, typeint)
  , 3
  , BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1) + LOAD(r.3, r.2, i64))
 , addtemplate(symbol(internalmod, "idxseq", seqof.typereal, typeint, typereal)
  , 4
  , BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1) + LOAD(r.3, r.2, i64)
  + CAST(r.4, r.3, double, bitcast))
 , addtemplates(packedtypes + typeptr
  , symbol(internalmod, "idxseq", seqof.typeT, typeint, typeptr)
  , 4
  , BINOP(r.1, ibcsub.2, C64.1, add) + GEP(r.2, i64, ibcsub.1, r.1) + LOAD(r.3, r.2, i64)
  + CAST(r.4, r.3, ptr.i64, inttoptr))
 , addtemplate(GetSeqLength, 2, GEP(r.1, i64, ibcsub.1, C64.1) + LOAD(r.2, r.1, i64))
 , addtemplate(GetSeqType, 1, LOAD(r.1, ibcsub.1, i64))
 , addtemplate(symbol(builtinmod.typeint, "load", [typeptr, typeint], typeint)
  , 2
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
 , addtemplate(symbol(builtinmod.typeboolean, "load", [typeptr, typeint], typeboolean)
  , 2
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
 , addtemplate(symbol(builtinmod.typeptr, "load", [typeptr, typeint], typeptr)
  , 3
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64) + CAST(r.3, r.2, ptr.i64, inttoptr))
 , addtemplate(symbol(builtinmod.typereal, "load", [typeptr, typeint], typereal)
  , 3
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64) + CAST(r.3, r.2, double, bitcast))
 , addtemplate(symbol(builtinmod.typeint, "fld", [typeptr, typeint], typeint)
  , 2
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
 , addtemplate(symbol(builtinmod.typebyte, "fld", [typeptr, typeint], typebyte)
  , 2
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
 , addtemplate(symbol(builtinmod.typeboolean, "fld", [typeptr, typeint], typeboolean)
  , 2
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64))
 , addtemplates(packedtypes + typeptr
  , symbol(builtinmod.typeT, "fld", [typeptr, typeint], typeptr)
  , 3
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64) + CAST(r.3, r.2, ptr.i64, inttoptr))
 , addtemplate(symbol(builtinmod.typereal, "fld", [typeptr, typeint], typereal)
  , 3
  , GEP(r.1, i64, ibcsub.1, ibcsub.2) + LOAD(r.2, r.1, i64) + CAST(r.3, r.2, double, bitcast))
 , addtemplate(symbol(internalmod, "basewords", typeptr)
  , 4
  , CALL(r.1, 0, 32768, function.[ptr.i64], first.liblist) + GEP(r.2, i64, r.1, C64.1)
  + LOAD(r.3, r.2, i64)
  + CAST(r.4, r.3, ptr.i64, inttoptr))
 , addtemplate(symbol(internalmod, "addresssymbols", seqof.typeptr)
  , 4 + 3 * length.liblist
  , for
   acc = CALL(r.1
    , 0
    , 32768
    , function.[ptr.i64, i64, i64]
    , symboltableentry("allocatespace", function.[ptr.i64, i64, i64])
    , slot.ibcfirstpara2
    , C64(length.liblist + 2))
   + GEP(r.2, i64, r.1, C64.0)
   + STORE(r.3, r.2, C64.0)
   + GEP(r.3, i64, r.1, C64.1)
   + STORE(r.4, r.3, C64.length.liblist)
   , idx = 1
   , w ∈ liblist
  do
   next(
    acc + GEP(r(idx + 3), i64, r.1, C64((idx + 5) / 3))
    + CALL(r(idx + 4), 0, 32768, function.[ptr.i64], w)
    + LOAD(r(idx + 5), r(idx + 4), i64)
    + STORE(r(idx + 6), r(idx + 3), r(idx + 5))
    , idx + 3)
  /do acc + GEP(r(4 + 3 * length.liblist), i64, r.1, C64.0))
 ]

Function profiledatatemplate(profdata:seq.slot) match5
let start = 
 CALL(r.1
  , 0
  , 32768
  , function.[ptr.i64, i64, i64]
  , symboltableentry("allocatespace", function.[ptr.i64, i64, i64])
  , slot.ibcfirstpara2
  , C64(length.profdata + 2))
 + GEP(r.2, i64, r.1, C64.0)
 + STORE(r.3, r.2, C64.0)
 + GEP(r.3, i64, r.1, C64.1)
 + STORE(r.4, r.3, C64.length.profdata)
,
addtemplate(symbol(internalmod, "profiledata", seqof.typeptr)
 , 4 + 3 * length.profdata
 , for acc = start, idx = 1, w ∈ profdata do
  next(
   acc + GEP(r(idx + 3), i64, r.1, C64((idx + 5) / 3))
   + CALL(r(idx + 4), 0, 32768, function.[ptr.i64, i64], w, slot.ibcfirstpara2)
   + CAST(r(idx + 5), r(idx + 4), i64, ptrtoint)
   + STORE(r(idx + 6), r(idx + 3), r(idx + 5))
   , idx + 3)
 /do acc + GEP(r(4 + 3 * length.profdata), i64, r.1, C64.0))

Function symboltableentry(name:seq.word, type:llvmtype) slot
modulerecord(name, [toint.FUNCTIONDEC, typ.type, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

Function =(a:llvmtype, b:llvmtype) boolean typ.a = typ.b

Function buildspecial(xx:symbol, alltypes:typedict) match5
if isRecord.xx then
 if nopara.xx < 10 then
  let fldbc = 
   recordcode(arithseq(nopara.xx, 1, ibcfirstpara2 + 1)
    , tollvmtypelist(alltypes, xx) << 2
    , 0
    , true)
  ,
  addtemplate(xx, regno.fldbc, bc.fldbc)
 else
  addtemplate(xx, 0, emptyinternalbc, wordname.xx, nopara.xx, tollvmtypelist(alltypes, xx) << 2)
else if isSequence.xx then
 if nopara.xx < 10 then
  let fldbc = 
   sequencecode(arithseq(nopara.xx, 1, ibcfirstpara2 + 1)
    , tollvmtype(alltypes, para.module.xx)
    , 0
    , true)
  ,
  addtemplate(xx, regno.fldbc, bc.fldbc)
 else
  addtemplate(xx
   , 0
   , emptyinternalbc
   , "SEQUENCE"_1
   , nopara.xx
   , [tollvmtype(alltypes, para.module.xx)])
else if isloopblock.xx then
 addtemplate(xx
  , firstvar.xx
  , emptyinternalbc
  , wordname.xx
  , nopara.xx
  , for oldacc = [tollvmtype(alltypes, resulttype.xx)], e20 ∈ paratypes.xx do
   oldacc + tollvmtype(alltypes, e20)
  /do oldacc)
else
 empty:match5

Function call(alltypes:typedict, xx:symbol, type:word, symname:word) match5
let list = tollvmtypelist(alltypes, xx)
let functype = function.list
let newcode = 
 CALLSTART(1
  , 0
  , 32768
  , typ.functype
  , toint.symboltableentry([symname], functype)
  , if type = "CALL"_1 then nopara.xx + 1 else nopara.xx)
,
addtemplate(xx, 1, newcode, type, nopara.xx, list)

Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int) internalbc
let args = 
 if action.t = "CALL"_1 then
  empty:seq.int
 else
  subseq(argstack, length.argstack - arg.t + 1, length.argstack)
,
processtemplate(parts.t, deltaoffset, args)

type recordcoderesult is regno:int, bc:internalbc

Function sequencecode(args:seq.int, type:llvmtype, lastreg:int, template:boolean) recordcoderesult
recordcode([toint.C64.0, toint.C64.length.args] + args
 , [i64, i64] + constantseq(length.args, type)
 , lastreg
 , template)

Function recordcode(args:seq.int, types:seq.llvmtype, lastreg:int, template:boolean) recordcoderesult
let firstpara = if template then slot.ibcfirstpara2 else r.1
let newcode = 
 CALL(r(lastreg + 1)
  , 0
  , 32768
  , function.[ptr.i64, i64, i64]
  , symboltableentry("allocatespace", function.[ptr.i64, i64, i64])
  , firstpara
  , C64.length.args)
let pint = lastreg + 1,
for bc = newcode, i = 1, regno = pint, preal = 0, pptr = 0, arg ∈ args do
 let typ = types_i,
 if typ = double then
  let offset = if preal = 0 then 1 else 0
  let newpreal = if preal = 0 then regno + 1 else preal
  let newbc0 = if preal = 0 then bc + CAST(r(regno + 1), r.pint, ptr.double, bitcast) else bc
  let newbc = 
   GEP(r(regno + offset + 1), double, r.newpreal, C64(i - 1))
   + STORE(r(regno + offset + 2), r(regno + offset + 1), slot.args_i)
  ,
  next(newbc0 + newbc, i + 1, regno + offset + 1, newpreal, pptr)
 else if typ = ptr.i64 then
  let offset = if pptr = 0 then 1 else 0
  let newpptr = if pptr = 0 then regno + 1 else pptr
  let newbc0 = if pptr = 0 then bc + CAST(r(regno + 1), r.pint, ptr.ptr.i64, bitcast) else bc
  let newbc = 
   GEP(r(regno + offset + 1), ptr.i64, r.newpptr, C64(i - 1))
   + STORE(r(regno + offset + 2), r(regno + offset + 1), slot.args_i)
  ,
  next(newbc0 + newbc, i + 1, regno + offset + 1, preal, newpptr)
 else
  let newbc = 
   GEP(r(regno + 1), i64, r.pint, C64(i - 1))
   + STORE(r(regno + 2), r(regno + 1), slot.args_i)
  ,
  next(bc + newbc, i + 1, regno + 1, preal, pptr)
/do
 if template then
  recordcoderesult(regno + 1, bc + GEP(r(regno + 1), i64, r(lastreg + 1), C64.0))
 else
  recordcoderesult(regno, bc) 