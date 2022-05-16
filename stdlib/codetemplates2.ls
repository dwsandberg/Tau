Module codetemplates2

use bits

use codetemplates

use internalbc

use llvm

use llvmconstants

use persistant

use standard

use symbol

use symbol2

use textio

use seq.bit

use set.int

use otherseq.llvmtype

use seq.llvmtype

use encoding.match5

use seq.match5

use seq.mytype

use set.mytype

use otherseq.symbol

use seq.symbol

use set.symbol

use otherseq.symbolref

use set.symbolref

use seq.symdef

use set.symdef

use set.word

use seq.seq.int

use seq.seq.symbol

use seq.seq.word

Function _(symbolrefdecode:seq.symbol, r:symbolref)symbol
let i = toint.r
if i > 0 then symbolrefdecode_i else Fref.symbolrefdecode_(-i)

Export type:match5

Export constdata seq.slot

Export wordref(w:word)int

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Export symboltableentry(name:seq.word, type:llvmtype)slot


Export defines(steponeresult)seq.symdef

Export type:steponeresult

Export extnames(steponeresult)set.symdef


Export findtemplate(d:symbol)seq.match5

Export length(match5)int{no of instruction that return results}

Export action(match5)word

Export arg(match5)int

Export sym(match5)symbol

Export firstvar(a:match5)int length.a

Export brt(a:match5)int length.a

Export brf(a:match5)int arg.a

Export llvmtypelist(match5)seq.llvmtype

Export usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc

Export sequencecode(args:seq.int, type:llvmtype, lastreg:int, template:boolean)recordcoderesult

Export regno(recordcoderesult)int

Export bc(recordcoderesult)internalbc

Export type:recordcoderesult

Export recordcode(args:seq.int, types:seq.llvmtype, lastreg:int, template:boolean)recordcoderesult

Export functype(m:match5)llvmtype

Function externalcall(sym:symbol)boolean
isInternal.sym
∧ name.sym
∉ "packedindex idxseq true false option callidx GEP abort stacktrace  not getseqtype getseqlength casttoreal intpart bitcast toreal toint representation xor 
set+-/ * ?=> >> << ∨ ∧"

list of external calls 
"arcsin arccos sin tan cos sqrt createfile3 loadedLibs primitiveadd randomint getfile2 getbytefile2 getbitfile2 callstack 
createthread getmachineinfo currenttime allocatespace processisaborted addencoding getinstance"

Function stepone(symbolrefdecode:seq.symbol
, alltypes:typedict
, prgcode:seq.seq.symbolref
, libextnames:set.symdef
, libname:word
)steponeresult
let discard1 = initmap5
let impsym = symbol(moduleref."inputoutput", "stacktraceimp", seqof.typeword)
let bb = getSymdef(libextnames, impsym)
let discard6 = 
 if not.isempty.bb then
  let discard5 = call(alltypes, impsym, "CALL"_1, mangledname(libextnames, impsym, libname))
  0
 else 0
let prgX=for  acc=empty:seq.symdef,cc ∈ prgcode do
 let rep=toint.first.cc
 let firstsym = symbolrefdecode_(symbolref.rep)
 let code = for code = empty:seq.symbol, r ∈ cc << 1 do code + symbolrefdecode_r /for(code)
   acc+if isrecordconstant.firstsym /or isGlobal.firstsym /or libname = library.module.firstsym
   then symdef(firstsym,code,rep)
 else if isInternal.firstsym then  symdef(firstsym,code,-rep)
   else  
   let b = getSymdef(libextnames, firstsym)
   assert isempty.b /or paragraphno.b_1 > 0 report "?"+print.sym.b_1
   {if not.isempty.b then b_1
   else }symdef(firstsym,code,-rep)
/for(acc)   
for used = empty:seq.symbol
, crecord = empty:seq.symdef
, extnames = empty:set.symdef
, cc ∈ prgX
do
 let firstsym = sym.cc
 let code = code.cc
 if isrecordconstant.firstsym then
  let lastsym = last.code
  let sd = 
   symdef(firstsym
   , if isSequence.lastsym then[Lit.0, Lit.nopara.lastsym] + code >> 1
   else
    assert isRecord.lastsym report"nnn" + print.code
    code >> 1
   , 0
   )
  next(used + toseq.asset.code.sd, crecord + sd,  extnames)
 else if isInternal.firstsym then
 if externalcall.firstsym then
   let discard5 = call(alltypes, firstsym, "CALL"_1, name.firstsym)
   next(used
   , crecord
    , extnames+cc
   )
  else
      let sdnew = symdef(firstsym, internalbody.firstsym, paragraphno.cc)
   next(used + toseq.asset.code + firstsym, crecord,  extnames + sdnew)
 else if isGlobal.firstsym then
  let discard5 = 
   addtemplate(firstsym
   , 1
   , GEP(r.1, i64, slot.global([merge("$$" + toword.paragraphno.cc)], i64, C64.0))
   )
  next(used, crecord,  extnames)
 else
  if libname = library.module.firstsym then
    next(used + toseq.asset.code + firstsym, crecord,  extnames +  cc)
  else 
  let b = getSymdef(libextnames, firstsym)
  if not.isempty.b then
   let discard5 = call(alltypes, firstsym, "CALL"_1, mangledname(libextnames, firstsym, libname))
   next(used, crecord,  extnames+b_1)
  else
      next(used + toseq.asset.code + firstsym, crecord,  extnames +  cc)
/for( 
let indefines= for acc=empty:set.symdef,   sd /in toseq.extnames do 
   if  paragraphno.sd < 0 /and not.externalcall.sym.sd /or library.module.sym.sd=libname 
     then 
 let ele2 = sym.sd
  let name = mangledname(extnames, ele2, libname)
  let discard = funcdec(alltypes, ele2, name)
  let discard5 = call(alltypes, ele2, "CALL"_1, name)   
   acc+sd else acc
 /for(acc) 
let discard100 = uses(alltypes, asset.used, crecord,    extnames, alltypes, libname)
let entrypoint=for entrypoint = slot.0, sd ∈ toseq.indefines
while toint.entrypoint = 0
do if name.sym.sd ∈ "entrypoint"then
 symboltableentry([mangledname(extnames, sym.sd, libname)], function.[ptr.i64, i64, ptr.i64])
else entrypoint
/for(entrypoint)
steponeresult( toseq.indefines, extnames, entrypoint))

function =(a:symdef,b:symdef) boolean sym.a=sym.b


Function internalbody(ele:symbol)seq.symbol
for acc = empty:seq.symbol, e9 ∈ arithseq(nopara.ele, 1, 1)do acc + Local.e9 /for(acc
+ if name.ele ∈ "stacktrace"then
 symbol(moduleref."inputoutput", "stacktraceimp", seqof.typeword)
else ele /if)

Function uses(alltypes:typedict
, used1:set.symbol
, isrecordconstant:seq.symdef
, extnames:set.symdef
, typedict:typedict
, libname:word
)int
for acc = empty:match5, ele ∈ toseq.used1 do
 if isconst.ele then
  if isFref.ele then   let basesym = basesym.ele
  let functyp = ptr.tollvmtype(typedict, basesym)
  addtemplate(Fref.basesym
  , 0
  , emptyinternalbc
  , "ACTARG"_1
  , ptrtoint(functyp, symboltableentry([mangledname(extnames, basesym, libname)], functyp))
  )
  else if isrecordconstant.ele then acc else buildconst(ele, alltypes)
 else if isspecial.ele   then buildspecial(ele, alltypes)
 else if isBuiltin.ele then
  if wordname.ele = "createthreadY"_1 then
   let rt = parameter.para.module.ele
   let l = 
    for l = empty:seq.llvmtype, e ∈ paratypes.ele << 3 do l + tollvmtype(alltypes, e)/for(l + tollvmtype(alltypes, rt))
   addtemplate(ele, 0, emptyinternalbc, wordname.ele, nopara.ele, l)
  else acc
 else if externalcall.ele then 
 call(alltypes, ele, "CALL"_1, name.ele)else acc
/for(
processconst(isrecordconstant, alltypes))

Export extnames(steponeresult)set.symdef

type steponeresult is defines:seq.symdef, extnames:set.symdef, entrypoint:slot


Export defines(steponeresult)seq.symdef

Export entrypoint(steponeresult)slot

Export type:steponeresult

Function addlibwords(extnames:set.symdef, typedict:typedict)slot
let f1 = 
 symbol(moduleref."inputoutput"
 , "addlibwords"
 , typeref."liblib libraryModule"
 , typeint
 )
let functyp = ptr.tollvmtype(typedict, f1)
ptrtoint(functyp, symboltableentry([mangledname(extnames, f1, "stdlib"_1)], functyp))

Export tollvmtype(typedict, symbol)llvmtype

Function processconst(toprocess:seq.symdef, alltypes:typedict)int
let initvalue = nextencoding.empty:match5
for notprocessed = empty:seq.symdef, xx ∈ toprocess do
 for args = empty:seq.int, defined = true, ele ∈ code.xx
 while defined
 do let tp = findtemplate.ele
 if isempty.tp then
  if isIntLit.ele then
   {length of recoredconstant as seq may not include length}
   let discard5 = buildconst(ele, alltypes)
   next(args, false)
  else next(args, false)
 else next(args + arg.tp_1, true)
 /for(if defined then
  let discard = addtemplate(sym.xx, 0, emptyinternalbc, "ACTARG"_1, slot.addobject.args)
  notprocessed
 else notprocessed + xx /if)
/for(if nextencoding.empty:match5 = initvalue then
 assert isempty.notprocessed report"processconst problem"
 0
else processconst(notprocessed, alltypes)/if)

Function mangledname(extname:set.symdef, s:symbol, library:word)word
 if  externalcall.s then name.s 
 else let b = getSymdef(extname, s)
 assert not.isempty.b
 report"Mangled Name problem" + print.s + library
 + for txt = "", sd ∈ toseq.extname do txt + print.sym.sd /for(txt)
 merge.if paragraphno.b_1 < 0 then[library, "$"_1, "$"_1, toword.-paragraphno.b_1]
 else[library.module.s, "$"_1, "$"_1, toword.paragraphno.b_1] 