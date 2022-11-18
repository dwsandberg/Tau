Module codetemplates2

use codetemplates

use internalbc

use llvm

use seq.llvmtype

use encoding.match5

use seq.match5

use mytype

use otherseq.mytype

use persistant

use standard

use seq.symbol

use set.symbol

use symbol2

use seq.symdef

use set.symdef

use seq.typedef

use otherseq.seq.word

Export type:steponeresult

Export defines(steponeresult) seq.symdef

Export entrypoint(steponeresult) slot

Export type:match5 {From codetemplates}

Export action(match5) word {From codetemplates}

Export arg(match5) int {From codetemplates}

Export brf(a:match5) int

Export brt(a:match5) int

Export firstvar(a:match5) int

Export functype(m:match5) llvmtype {From codetemplates}

Export length(match5) int
{no of instruction that return results}
{From codetemplates}

Export llvmtypelist(match5) seq.llvmtype {From codetemplates}

Export sym(match5) symbol {From codetemplates}

Export type:recordcoderesult {From codetemplates}

Export bc(recordcoderesult) internalbc {From codetemplates}

Export regno(recordcoderesult) int {From codetemplates}

Export findtemplate(d:symbol) seq.match5 {From codetemplates}

Export recordcode(args:seq.int, types:seq.llvmtype, lastreg:int, template:boolean) recordcoderesult
{From codetemplates}

Export sequencecode(args:seq.int, type:llvmtype, lastreg:int, template:boolean) recordcoderesult
{From codetemplates}

Export symboltableentry(name:seq.word, type:llvmtype) slot {From codetemplates}

Export tollvmtype(typedict, symbol) llvmtype {From codetemplates}

Export usetemplate(t:match5, deltaoffset:int, argstack:seq.int) internalbc
{From codetemplates}

Export constdata seq.slot {From persistant}

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Function stepone(alltypes:typedict, prgX:set.symdef, libname:word, isbase:boolean) steponeresult
let discard1 = initmap5
for used = empty:seq.symbol
 , crecord = empty:seq.symdef
 , indefines = empty:seq.symdef
 , cc ∈ toseq.prgX
do
 let firstsym = sym.cc
 let code = code.cc
 if isrecordconstant.firstsym then
  let lastsym = last.code
  let sd = 
   symdef(firstsym
    , if isSequence.lastsym then
     [Lit.0, Lit.nopara.lastsym] + code >> 1
    else
     assert isRecord.lastsym report "nnn $(code)"
     code >> 1
    , 0)
  next(used + toseq.asset.code.sd, crecord + sd, indefines)
 else if isInternal.firstsym then
  if {firstsym is external call} externalNo.cc = 1 ∧ isThisLibrary.cc then
   let discard5 = call(alltypes, firstsym, "CALL"_1, name.firstsym)
   next(used, crecord, indefines)
  else if not.isbase then
   let discard5 = call(alltypes, firstsym, "CALL"_1, mangledname(prgX, firstsym, libname))
   next(used, crecord, indefines)
  else
   next(used + toseq.asset.code + firstsym, crecord, indefines + cc)
 else if isGlobal.firstsym then
  let discard5 = 
   addtemplate(firstsym
    , 1
    , GEP(r.1, i64, slot.global([merge("$$" + toword.externalNo.cc)], i64, C64.0)))
  next(used, crecord, indefines)
 else if libname = library.module.firstsym ∨ isThisLibrary.cc ∨ externalNo.cc = 0 then
  next(used + toseq.asset.code + firstsym, crecord, indefines + cc)
 else
  {not define in this library}
  let discard5 = call(alltypes, firstsym, "CALL"_1, mangledname(prgX, firstsym, libname))
  next(used, crecord, indefines)
/for (
 let entrypointsym = 
  for entrypointsym = Lit.0, sd ∈ indefines do
   let discard = declare(alltypes, prgX, sym.sd, libname)
   if name.sym.sd ∈ "entrypoint" then sym.sd else entrypointsym
  /for (entrypointsym)
 let discard100 = uses(alltypes, asset.used, crecord, prgX, alltypes, libname)
 steponeresult(indefines
  , symboltableentry([mangledname(prgX, entrypointsym, libname)], function.[ptr.i64, i64, ptr.i64]))
)

function declare(alltypes:typedict, prgX:set.symdef, ele2:symbol, libname:word) int
let name = mangledname(prgX, ele2, libname)
let discard = funcdec(alltypes, ele2, name)
let discard5 = call(alltypes, ele2, "CALL"_1, name)
0

Function uses(alltypes:typedict
 , used1:set.symbol
 , isrecordconstant:seq.symdef
 , extnames:set.symdef
 , typedict:typedict
 , libname:word) int
for acc = empty:match5, ele ∈ toseq.used1 do
 if isconst.ele then
  if isFref.ele then
   let basesym = basesym.ele
   let functyp = ptr.tollvmtype(typedict, basesym)
   addtemplate(Fref.basesym
    , 0
    , emptyinternalbc
    , "ACTARG"_1
    , ptrtoint(functyp, symboltableentry([mangledname(extnames, basesym, libname)], functyp)))
  else if isrecordconstant.ele then acc else buildconst(ele, alltypes)
 else if isspecial.ele then
  buildspecial(ele, alltypes)
 else if isBuiltin.ele then
  if wordname.ele = "createthreadY"_1 then
   let rt = parameter.para.module.ele
   let l = 
    for l = empty:seq.llvmtype, e ∈ paratypes.ele << 3 do
     l + tollvmtype(alltypes, e)
    /for (l + tollvmtype(alltypes, rt))
   addtemplate(ele, 0, emptyinternalbc, wordname.ele, nopara.ele, l)
  else
   acc
 else if isInternal.ele ∧ internalidx.ele = 1 then
  call(alltypes, ele, "CALL"_1, name.ele)
 else
  acc
/for (processconst(isrecordconstant, alltypes))

type steponeresult is defines:seq.symdef, entrypoint:slot

Function processconst(toprocess:seq.symdef, alltypes:typedict) int
let initvalue = length.encodingdata:match5
for notprocessed = empty:seq.symdef, xx ∈ toprocess do
 for args = empty:seq.int, defined = true, ele ∈ code.xx
 while defined
 do
  let tp = findtemplate.ele
  if isempty.tp then next(args, false) else next(args + arg.tp_1, true)
 /for (
  if defined then
   let discard = addtemplate(sym.xx, 0, emptyinternalbc, "ACTARG"_1, slot.addobject.args)
   notprocessed
  else
   notprocessed + xx
 )
/for (
 if length.encodingdata:match5 = initvalue then
  assert isempty.notprocessed report "processconst problem"
  0
 else
  processconst(notprocessed, alltypes)
)

Function internalidx(s:symbol) int
{list of external calls" arcsin arccos sin tan cos sqrt createfile3 loadedLibs randomint
 getbytefile2 getbitfile2 callstack createthread getmachineinfo currenttime allocatespace processisaborted
 addencoding getinstance"}
let l = 
 ["stacktrace"
  , "not boolean"
  , "intpart real"
  , "getseqtype ptr"
  , "getseqlength ptr"
  , "casttoreal int"
  , "toreal int"
  , "toint byte"
  , "toint bit"
  , "representation real"
  , "* real real"
  , "/ real real"
  , "+real real"
  , "-real real"
  , ">1 real real"
  , "* int int"
  , "/ int int"
  , "+int int"
  , "-int int"
  , ">1 int int"
  , "> int int"
  , "= boolean boolean"
  , "= int int"
  , "= real real"
  , "<< bits int"
  , ">> bits int"
  , "⊻ bits bits"
  , "∨ bits bits"
  , "∧ bits bits"
  , "abort real seq.word"
  , "abort int seq.word"
  , "abort boolean seq.word"
  , "abort ptr seq.word"
  , "set ptr int"
  , "set ptr real"
  , "set ptr ptr"]
let idx = findindex(l, [name.s] + %(types.s >> 1))
if idx ≤ length.l then idx + 1 else 1

Function mangledname(extname:set.symdef, s:symbol, library:word) word
let b = getSymdef(extname, s)
assert not.isempty.b
report
 "Mangled Name problem $(s)" + library
 + for txt = "", sd ∈ toseq.extname do
  txt + "/br" + %.sym.sd + library.module.sym.sd
 /for (txt + stacktrace)
if externalNo.b_1 = 1 ∧ isThisLibrary.b_1 then
 name.s
else
 merge.[
  if isInternal.s then
   library.module.s
  else if isThisLibrary.b_1 then library else library.module.s
  , "$"_1
  , "$"_1
  , toword.externalNo.b_1]

Function addtype(a:mytype) int
addobject.for acc = [addint.1, addint.length.typerep.a], e ∈ typerep.a do
 acc + wordref.name.e + wordref.modname.e + wordref.library.e
/for (acc)

Function addtypeseq(a:seq.mytype) int
addobject.for acc = [addint.0, addint.length.a], @e ∈ a do acc + addtype.@e /for (acc)

Function addsymbol(a:symbol) int
let t = privatefields.a
addobject.[addwordseq.worddata.a
 , wordref.library.module.a
 , wordref.name.module.a
 , addtype.para.module.a
 , addtypeseq.types.a
 , addint.t_1
 , addint.t_2] 