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

Export match5map(steponeresult)seq.match5

Export defines(steponeresult)seq.symdef

Export type:steponeresult

Export extnames(steponeresult)set.symdef

Export_(m:seq.match5, d:symbol)match5

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
∉ "stacktrace not getseqtype getseqlength casttoreal intpart bitcast toreal toint representation xor set+-/ * ?=> >> << ∨ ∧"

Function stepone(symbolrefdecode:seq.symbol
, alltypes:typedict
, prgcode:seq.seq.symbolref
, libextnames:set.symdef
, thename:word
)steponeresult
let libname = thename
let discard1 = initmap5
let impsym=symbol(moduleref."inputoutput", "stacktraceimp", seqof.typeword)
let bb = lookup(libextnames, symdef(impsym, empty:seq.symbol, 0))
let discard6=  if not.isempty.bb then
     let discard5 = call(alltypes, impsym, "CALL"_1, mangledname(libextnames, impsym, thename))
    0
    else 0
for 
 used = empty:seq.symbol 
, used0 = empty:seq.symbolref
, crecord = empty:seq.symdef
, defines = empty:seq.symdef
, symrefs = empty:set.symbolref
, extnames = libextnames
, c ∈ prgcode
do
 let firstsym = symbolrefdecode_(first.c)
 let code = for code = empty:seq.symbol, r ∈ c << 1 do code + symbolrefdecode_r /for(code)
 if isrecordconstant.firstsym then
  let lastsym = last.code
  let sd = 
   symdef(firstsym
   , if isSequence.lastsym then[Lit.0, Lit.nopara.lastsym] + code >> 1 else code >> 1
   , 0
   )
  next(used+toseq.asset.code.sd,used0 + toseq.asset(c << 1), crecord + sd, defines, symrefs, extnames)
 else
  let b = lookup(libextnames, symdef(firstsym, empty:seq.symbol, 0))
  if not.isempty.b ∧ not.isInternal.firstsym ∨ externalcall.firstsym then
   let discard5 = call(alltypes, firstsym, "CALL"_1, mangledname(libextnames, firstsym, thename))
   next(used,used0, crecord, defines, symrefs + first.c, extnames)
  else if isInternal.firstsym then
next(used+toseq.asset.code,used0  + toseq.asset.c
   , crecord
   , defines + symdef(firstsym, internalbody.firstsym, toint.first.c)
   , symrefs + first.c
   , extnames + symdef(firstsym, empty:seq.symbol, -toint.first.c)
   )
else
   next(used+toseq.asset.code,used0 + toseq.asset.c
   , crecord
   , defines + symdef(firstsym, code, toint.first.c)
   , symrefs + first.c
   , extnames
   + symdef(firstsym
   , empty:seq.symbol
   , if thename = library.module.firstsym then toint.first.c else-toint.first.c
   )
   )
/for(uses(alltypes,{asset.used,} asset.used0, crecord, defines, thename
, extnames, symbolrefdecode, alltypes, libname, symrefs
))

Function internalbody(ele:symbol) seq.symbol
    for acc = empty:seq.symbol, e9 ∈ arithseq(nopara.ele, 1, 1)do 
    acc + Local.e9 /for(acc +
    if name.ele /in "stacktrace" then symbol(moduleref."inputoutput", "stacktraceimp", seqof.typeword)
   else 
     ele)


Function uses(alltypes:typedict
,{ used1:set.symbol
,} used:set.symbolref
, isrecordconstant:seq.symdef
, indefines:seq.symdef
, thename:word
, extnamesin:set.symdef
, symbolrefdecode:seq.symbol
, typedict:typedict
, libname:word
, symrefs:set.symbolref
)steponeresult
{let check= for acc=empty:set.symbol, ref /in toseq.used do  acc+symbolrefdecode_ref 
 /for( "JJJJ"+%.cardinality.acc+%.cardinality.used1+%.cardinality.used)
 assert isempty.check report check}
let i = binarysearch(toseq.used, symbolref.0)
let notprocessed = subseq(toseq.used, abs.i, length.toseq.used)
let frefs = subseq(toseq.used, 1, abs.i - 1)
for defines = asset.indefines, extnames = extnamesin, ref ∈ notprocessed do
 let ele = symbolrefdecode_ref
 if isabstract.module.ele then next(defines, extnames)
 else if isconst.ele then
  if isFref.ele ∨ isrecordconstant.ele then next(defines, extnames)
  else
   let discard5 = buildconst(ele, alltypes)
   next(defines, extnames)
 else if isspecial.ele then
  let discard5 = buildspecial(ele, alltypes)
  next(defines, extnames)
 else if isGlobal.ele then
  let discard5 = 
   addtemplate(ele, 1, GEP(r.1, i64, slot.global([merge("$$" + toword.toint.ref)], i64, C64.0)))
  next(defines, extnames)
 else if inModFor.ele ∨ ele = Optionsym then next(defines, extnames)
 else if isBuiltin.ele then
  if wordname.ele = "createthreadY"_1 then
   let rt = parameter.para.module.ele
   let l = 
    for l = empty:seq.llvmtype, e ∈ paratypes.ele << 3 do l + tollvmtype(alltypes, e)/for(l + tollvmtype(alltypes, rt))
   let discard5 = addtemplate(ele, 0, emptyinternalbc, wordname.ele, nopara.ele, l)
   next(defines, extnames)
  else next(defines, extnames)
 else if ref ∈ symrefs then next(defines, extnames)
 else if isInternal.ele then
  if externalcall.ele then
   let discard5 = call(alltypes, ele, "CALL"_1, name.ele)
   next(defines, extnames)
  else
   let code = internalbody.ele
   next(defines + symdef(ele, code, toint.ref), extnames + symdef(ele, empty:seq.symbol, -toint.ref))
 else
  let discard5 = call(alltypes, ele, "CALL"_1, mangledname(extnames, ele, thename))
  next(defines
  , extnames
  + symdef(ele
  , empty:seq.symbol
  , if thename = library.module.ele then toint.ref else-toint.ref
  )
  )
/for(let defines2 = 
 for acc = 0, sd ∈ toseq.defines do
  let ele2 = sym.sd
  let name = mangledname(extnames, ele2, thename)
  let discard = funcdec(alltypes, ele2, name)
  let discard5 = call(alltypes, ele2, "CALL"_1, name)
  acc  
 /for(0)
 let discard2 = for buildFref = empty:match5, ref2 ∈ frefs do
 let basesym = symbolrefdecode_(symbolref.-toint.ref2)
 let functyp = ptr.tollvmtype(typedict, basesym)
 addtemplate(Fref.basesym
  , 0
  , emptyinternalbc
  , "ACTARG"_1
  , ptrtoint(functyp, symboltableentry([mangledname(extnames, basesym, libname)], functyp))
  )
/for(buildFref)
let discard4 = processconst(isrecordconstant, alltypes)
for entrypoint = slot.0, sd ∈ toseq.defines
while toint.entrypoint = 0
do if name.sym.sd ∈ "entrypoint"then
 symboltableentry([mangledname(extnames, sym.sd, thename)], function.[ptr.i64, i64, ptr.i64])
else entrypoint
/for(steponeresult(empty:seq.match5, toseq.defines, extnames, entrypoint)))

Export extnames(steponeresult)set.symdef

type steponeresult is match5map:seq.match5, defines:seq.symdef, extnames:set.symdef, entrypoint:slot

Export match5map(steponeresult)seq.match5

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
  do   let tp = findtemplate.ele
                    if isempty.tp then
              if isIntLit.ele then  
            {  length of recoredconstant as seq may not include length }
              let discard5 = buildconst(ele, alltypes)
               next(args,false)
            else next(args,false)
         else next(args+arg.tp_1,true)
  /for(if defined then
   let discard = addtemplate(sym.xx, 0, emptyinternalbc, "ACTARG"_1, slot.addobject.args)
   notprocessed
  else notprocessed + xx /if)
/for(if nextencoding.empty:match5 = initvalue then
 assert isempty.notprocessed report"processconst problem"
 0
else processconst(notprocessed, alltypes)/if)

Function mangledname(extname:set.symdef, s:symbol, library:word)word
if externalcall.s then name.s
else
 let b = lookup(extname, symdef(s, empty:seq.symbol, 0))
 assert not.isempty.b
 report"Mangled Name problem" + print.s + library
 + for txt = "", sd ∈ toseq.extname do
  if print.sym.sd = "real:-(real)real"then txt + print.sym.sd + print.code.sd + %.paragraphno.sd
  else txt
 /for(txt)
 merge.if paragraphno.b_1 < 0 then[library, "$"_1, "$"_1, toword.-paragraphno.b_1]
 else[library.module.s, "$"_1, "$"_1, toword.paragraphno.b_1]
