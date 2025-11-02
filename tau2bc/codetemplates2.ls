Module codetemplates2

use codetemplates

use internalbc

use llvm

use seq.llvmtype

use encoding.match5

use seq.match5

use mytype

use seq1.mytype

use persistant

use seq.slot

use standard

use seq.symbol

use set.symbol

use symbol1

use seq.symdef

use set.symdef

use seq.typedef

use seq1.seq.word

Export type:match5 {From codetemplates}

Export action(match5) word {From codetemplates}

Export arg(match5) int {From codetemplates}

Export firstvar(a:match5) int {From codetemplates}

Export length(match5) int {no of instruction that return results} {From codetemplates}

Export llvmtypelist(match5) seq.llvmtype {From codetemplates}

Export sym(match5) symbol {From codetemplates}

Export type:recordcoderesult {From codetemplates}

Export bc(recordcoderesult) internalbc {From codetemplates}

Export regno(recordcoderesult) int {From codetemplates}

Export findtemplate(d:symbol) seq.match5 {From codetemplates}

Export recordcode(
args:seq.int
, types:seq.llvmtype
, lastreg:int
, template:boolean
) recordcoderesult
{From codetemplates}

Export sequencecode(
args:seq.int
, type:llvmtype
, lastreg:int
, template:boolean
) recordcoderesult
{From codetemplates}

Export symboltableentry(name:seq.word, type:llvmtype) slot {From codetemplates}

Export tollvmtype(typedict, symbol) llvmtype {From codetemplates}

Export usetemplate(t:match5, deltaoffset:int, argstack:seq.int) internalbc
{From codetemplates}

Export constdata seq.slot {From persistant}

Function conststype llvmtype array(-2, i64)

Function stepone(
alltypes:typedict
, prgX:set.symdef
, libname:word
, isbase:boolean
, initprofile:seq.symbol
) seq.symdef
for
 used = empty:seq.symbol
 , crecord = empty:seq.symdef
 , indefines = empty:seq.symdef
 , cc ∈ toseq.prgX
do
 let firstsym = sym.cc,
 if isAbstract.module.firstsym then next(used, crecord, indefines)
 else
  let code = code.cc,
  if kind.firstsym = kconstantrecord then
   let lastsym = code sub n.code
   let kind = kind.lastsym,
   let sd =
    symdef(
     firstsym
     , if kind = ksequence then [Lit.0, Lit.nopara.lastsym] + code >> 1
     else
      assert kind = krecord report "codegen nnn:(sym.cc):(code.cc)",
      code >> 1
     , 0
    ),
   next(used + toseq.asset.code.sd, crecord + sd, indefines)
  else if isInternal.firstsym then
   if {firstsym is external call} not.isinternalimp.sym.cc ∧ isThisLibrary.cc then
    let discard5 = call(alltypes, firstsym, "CALL" sub 1, name.firstsym),
    next(used, crecord, indefines)
   else if not.isbase then
    let discard5 = call(alltypes, firstsym, "CALL" sub 1, mangledname(prgX, firstsym, libname)),
    next(used, crecord, indefines)
   else next(used + toseq.asset.code + firstsym, crecord, indefines + cc)
  else if kind.firstsym = kglobal then
   let discard5 =
    addtemplate(
     firstsym
     , 1
     , GEP(r.1, i64, slot.global([merge("$$" + toword.externalNo.cc)], i64, C64.0))
    ),
   next(used, crecord, indefines)
  else if libname = library.module.firstsym ∨ isThisLibrary.cc ∨ externalNo.cc = 0 then next(used + toseq.asset.code + firstsym, crecord, indefines + cc)
  else
   {not define in this library}
   let discard5 = call(alltypes, firstsym, "CALL" sub 1, mangledname(prgX, firstsym, libname)),
   next(used, crecord, indefines)
for discard101 = 0, sd ∈ indefines
do declare(alltypes, prgX, sym.sd, libname)
for acc = empty:seq.slot, sym ∈ initprofile
do
 if name.sym ∉ "profileData" then acc
 else acc + symboltableentry([mangledname(prgX, sym, libname)], tollvmtype(alltypes, sym))
let discard102 = profiledatatemplate.acc
let discard100 = uses(alltypes, asset.used, crecord, prgX, alltypes, libname),
indefines

function declare(alltypes:typedict, prgX:set.symdef, ele2:symbol, libname:word) int
let name = mangledname(prgX, ele2, libname)
let discard = funcdec(alltypes, ele2, name)
let discard5 = call(alltypes, ele2, "CALL" sub 1, name),
0

Function uses(
alltypes:typedict
, used1:set.symbol
, isrecordconstant:seq.symdef
, extnames:set.symdef
, typedict:typedict
, libname:word
) int
for acc = empty:match5, ele ∈ toseq.used1
do
 let kind = kind.ele,
 if kind = kfref then
  let basesym = basesym.ele
  let functyp = ptr.tollvmtype(typedict, basesym),
  addtemplate(
   Fref.basesym
   , 0
   , emptyinternalbc
   , "ACTARG" sub 1
   , ptrtoint(functyp, symboltableentry([mangledname(extnames, basesym, libname)], functyp))
  )
 else if kind = kwords then addtemplate(ele, 0, emptyinternalbc, "ACTARG" sub 1, slot.addwordseq.worddata.ele)
 else if kind = kword then addtemplate(ele, 0, emptyinternalbc, "ACTARG" sub 1, slot.wordref.wordname.ele)
 else if kind = krecord then
  if nopara.ele < 10 then
   let fldbc = recordcode(arithseq(nopara.ele, 1, ibcfirstpara2 + 1), tollvmtypelist(alltypes, ele) << 2, 0, true),
   addtemplate(ele, regno.fldbc, bc.fldbc)
  else addtemplate(ele, 0, emptyinternalbc, wordname.ele, nopara.ele, tollvmtypelist(alltypes, ele) << 2)
 else if kind = ksequence then
  if nopara.ele < 10 then
   let fldbc = sequencecode(arithseq(nopara.ele, 1, ibcfirstpara2 + 1), tollvmtype(alltypes, para.module.ele), 0, true),
   addtemplate(ele, regno.fldbc, bc.fldbc)
  else
   addtemplate(
    ele
    , 0
    , emptyinternalbc
    , "SEQUENCE" sub 1
    , nopara.ele
    , [tollvmtype(alltypes, para.module.ele)]
   )
 else if kind = kloop then
  for oldacc = [tollvmtype(alltypes, resulttype.ele)], e20 ∈ paratypes.ele
  do oldacc + tollvmtype(alltypes, e20),
  addtemplate(ele, firstvar.ele, emptyinternalbc, wordname.ele, nopara.ele, oldacc)
 else if isInternal.ele ∧ not.isinternalimp.ele then call(alltypes, ele, "CALL" sub 1, name.ele)
 else acc,
processconst(isrecordconstant, alltypes)

Function processconst(toprocess:seq.symdef, alltypes:typedict) int
let initvalue = n.encodingdata:match5
for notprocessed = empty:seq.symdef, xx ∈ toprocess
do
 for args = empty:seq.int, defined = true, ele ∈ code.xx
 while defined
 do
  let kind = kind.ele,
  if kind = kint then next(args + toint.C64.value.ele, true)
  else if kind = kreal then next(args + toint.Creal.value.ele, true)
  else if kind = ktrue then next(args + toint.C64.1, true)
  else if kind = kfalse then next(args + toint.C64.0, true)
  else
   let tp = findtemplate.ele,
   if isempty.tp then next(args, false) else next(args + arg.tp sub 1, true),
 if defined then
  let discard = addtemplate(sym.xx, 0, emptyinternalbc, "ACTARG" sub 1, slot.addobject.args),
  notprocessed
 else notprocessed + xx,
if n.encodingdata:match5 = initvalue then
 assert isempty.notprocessed report "processconst problem",
 0
else processconst(notprocessed, alltypes)

Function isinternalimp(s:symbol) boolean between(kind.s, kstacktrace, ksetP)

Function internalidx(s:symbol) int
{list of external calls" arcsin arccos sin tan cos sqrt createfile3 loadedLibs randomint getbytefile2 getbitfile2 callstack createthread getmachineinfo currenttime allocatespace processisaborted addencoding getinstance"}
if between(kind.s, kstacktrace, ksetP) then kind.s - kstacktrace + 2 else 1

Function mangledname(extname:set.symdef, s:symbol, library:word) word
let b = getSymdef(extname, s)
assert not.isempty.b report
 "Mangled Name problem:(s)"
  + library
  + for txt = "", sd ∈ toseq.extname
 do txt + "/br" + %.sym.sd + library.module.sym.sd,
 txt + stacktrace
let extNo =
 if kind.s ∈ [kother, kcompoundname, kmakereal, kcat, kmember, kidx] then externalNo.b sub 1
 else internalidx.s,
if extNo = 1 ∧ isThisLibrary.b sub 1 then name.s
else
 merge.[
  if isInternal.s then library.module.s
  else if isThisLibrary.b sub 1 then library
  else library.module.s
  , "$" sub 1
  , "$" sub 1
  , toword.extNo
 ]

Function addtype(a:mytype) int
addobject(
 for acc = [addint.1, addint.n.typerep.a], e ∈ typerep.a
 do acc + wordref.name.e + wordref.modname.e + wordref.library.e,
 acc
)

Function addtypeseq(a:seq.mytype) int
addobject(
 for acc = [addint.0, addint.n.a], @e ∈ a
 do acc + addtype.@e,
 acc
)

Function addsymbol(a:symbol) seq.int
let t = privatefields.a,
[
 addwordseq.worddata.a
 , wordref.library.module.a
 , wordref.name.module.a
 , addtype.para.module.a
 , addtypeseq.types.a
 , addint.t sub 1
 , addint.t sub 2
] 
