
Module codetemplates2

use bits

use codetemplates


use internalbc

use libraryModule

use llvm

use llvmconstants


use persistant

use standard

use symbol

use symref

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

Export type:match5 

Export constdata seq.slot

Export wordref(w:word)int


Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Export symboltableentry(name:seq.word, type:llvmtype)slot

Export match5map(steponeresult)seq.match5

Export defines(steponeresult)seq.symdef

Export type:steponeresult

Export extnames(steponeresult) set.symdef

Export _(m:seq.match5, d:symbol)match5

Export length(match5)int { no of instruction that return results }

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

Function externalcall(sym:symbol) boolean
  isInternal.sym /and 
   name.sym /nin "not getseqtype getseqlength casttoreal 
    intpart  bitcast toreal toint  representation xor
set+-/ * ? => >> << ∨ ∧   "

Function stepone(info:compileinfo, dependentlibs:seq.word, thename:word)steponeresult
let discard1 = initmap5
let alltypes=typedict.info
let libextnames = externnames.dependentlibs
for  used0=empty:seq.symbolref
    ,crecord=empty:seq.symdef
    ,defines=empty:seq.symdef,symrefs=empty:set.symbolref 
    , extnames = libextnames, c ∈ prgcode.info do
  let firstsym=  info_first.c 
    if isrecordconstant.firstsym then 
     let code=for code = empty:seq.symbol,r ∈ c << 1 do  code+info_ r  /for(code)
     let lastsym=last.code
    let sd=  symdef(firstsym,
     if isSequence.lastsym then[Lit.0, Lit.nopara.lastsym] + code >> 1   else code >> 1 )
   next(   used0+ toseq.asset.(c << 1)   ,crecord+sd, defines,symrefs,extnames)
    else 
     let code=for code = empty:seq.symbol,r ∈ c << 1 do  code+info_ r  /for(code)
       if "COMPILED"_1 ∈ getoption.code /or  externalcall.firstsym
       then 
         let discard5 = call(alltypes, firstsym,"CALL"_1,   mangledname(libextnames,firstsym,"loc1",first.c))
       next( used0,crecord,defines,symrefs+first.c,extnames)       
      else  
       let extname =  merge([thename] +  "$$" + toword.toint.first.c )
    next(    used0+ toseq.asset.c ,crecord,defines+symdef(firstsym,code,toint.first.c),symrefs+first.c
    ,add( extnames,firstsym,extname))
/for(   
uses(alltypes,  asset.used0 , crecord , defines , 
 thename, extnames, info,symrefs
))

use otherseq.symbolref

Function uses(alltypes:typedict
, used:set.symbolref
, isrecordconstant:seq.symdef
, indefines:seq.symdef
, thename:word
, extnamesin:set.symdef
,info:compileinfo
,symrefs:set.symbolref
)steponeresult
 let i=binarysearch(toseq.used,symbolref.0)
 let notprocessed=subseq(toseq.used,abs.i,length.toseq.used)
 let frefs=subseq(toseq.used,1,abs.i -1 ) 
for  defines = asset.indefines, extnames = extnamesin, ref ∈ toseq.used do
   let ele=info_ref 
 if isabstract.module.ele then next(defines, extnames)
 else if isconst.ele  then
    if isFref.ele /or isrecordconstant.ele then next( defines, extnames) else 
   let discard5 = buildconst(ele, alltypes)
   next(  defines,  extnames)
  else if isspecial.ele then
   let discard5 = buildspecial(ele, alltypes)
   next(  defines,  extnames)
  else if isGlobal.ele then
    let discard5 = 
    addtemplate(ele
    , 1
    , GEP(r.1
    , i64
    , slot.global([ merge("$$" + toword.toint.ref  )], i64, C64.0)
    )
    )
   next(    defines,  extnames)
  else if inModFor.ele ∨ ele = Optionsym then next(   defines,  extnames)
  else if isBuiltin.ele then
   if wordname.ele = "createthreadY"_1 then
    let rt = parameter.para.module.ele
    let l = 
     for l = empty:seq.llvmtype, e ∈ paratypes.ele << 3 do l + tollvmtype(alltypes, e)/for(l + tollvmtype(alltypes, rt))
    let discard5 = addtemplate(ele, 0, emptyinternalbc, wordname.ele, nopara.ele , l)
    next(   defines,  extnames)
   else next(  defines,  extnames)
  else  if ref /in symrefs then next(  defines,  extnames)
  else  if not.isInternal.ele
   /or externalcall.ele then
     let discard5 = call(alltypes, ele,"CALL"_1,   mangledname(extnames,ele,"loc2",ref))
    next(  defines,  extnames)
    else
     let r = toint.ref
    let extname =  merge([thename]   +"$$" + toword.r    )
    next( defines + symdef(ele, empty:seq.symbol,toint.ref)   , add(extnames, ele, extname)
    )
/for( let defines2 = 
 for acc = empty:set.symbol, sd ∈ toseq.defines do
  let ele2=sym.sd
  let name=mangledname(extnames, ele2,"defines",symbolref(paragraphno.sd))
  let discard = funcdec(alltypes, ele2,name)
  let discard5 = call(alltypes, ele2,"CALL"_1,  name)
  acc+ele2
 /for(  
  {let check= 
   for acc2="", sym /in    subseq(symbolrefdecode.info,1,newmaplength) do
    if  library.module.sym ≠ "stdxlib"_1 /or isabstract.module.sym /or sym /in acc then acc2
    else acc2+print.sym+library.module.sym+EOL
    /for(acc2)
  assert isempty.check report "failing in codetemplates2 "+ check}
 toseq.defines)
let discard2 = buildFref( frefs, info,extnames)
let discard4 = processconst(isrecordconstant,alltypes)
steponeresult(empty:seq.match5, defines2, extnames))

Export extnames(steponeresult) set.symdef

type steponeresult is match5map:seq.match5, defines:seq.symdef,extnames:set.symdef

Export match5map(steponeresult)seq.match5

Export defines(steponeresult)seq.symdef,

Export type:steponeresult

Function entrypointsymbol(extnames:set.symdef,a:compileinfo) slot  
  for acc=C64.0 ,sym /in symbolrefdecode.a do
    if isconstantorspecial.sym /or name.sym /nin "entrypoint" then acc
    else Frefslot(sym,extnames,typedict.a,symbolref.0)
 /for(acc)

 
Function addlibwords(extnames:set.symdef,typedict:typedict) slot
 let f1=symbol(moduleref."main2","addlibrarywords",typeref."liblib libraryModule",typeint)
 Frefslot(f1,extnames,typedict,symbolref.0)
 

 Function  Frefslot (sym:symbol,extnames:set.symdef,typedict:typedict,ref:symbolref) slot 
  let functyp = ptr.tollvmtype(typedict, sym)
      ptrtoint(functyp, symboltableentry([ mangledname(extnames, sym,"locFref",ref)], functyp)) 


function buildFref(frefs:seq.symbolref, info:compileinfo, extnames:set.symdef)seq.match5
let alltypes=typedict.info
for acc = empty:seq.match5, ref /in frefs do
let refbase=symbolref(-toint.ref)
let basesym=info_refbase
 let functyp = ptr.tollvmtype(alltypes, basesym)
 let discard = 
  addtemplate(Fref.basesym
  , 0
  , emptyinternalbc
  ,"ACTARG"_1
  ,  Frefslot(basesym,extnames,alltypes,refbase)
  )
 acc
/for(acc)

function add(extnames:set.symdef,sym:symbol,name:word) set.symdef
if isconstantorspecial.sym ∨ isabstract.module.sym ∨ not.isempty.getCode(extnames, sym)then extnames
else symdef(sym, [Word.name]) ∪ extnames
      
function externnames(dependentlibs:seq.word)set.symdef
for org = empty:set.symdef, ll ∈ loadedLibs do
 if(libname.ll)_1 ∉ dependentlibs then org
 else
 for acc = org, idx = 1, sym ∈ decoderef.ll do
   if isconstantorspecial.sym ∨ isabstract.module.sym ∨ not.isempty.getCode(org, sym)then
    next(acc, idx + 1)
   else next(symdef(sym, [Word.merge(libname.ll + "$$" + toword.idx)]) ∪ acc, idx + 1)
 /for(acc)
/for(org)

 Function processconst(toprocess:seq.symdef,alltypes:typedict)int
if isempty.toprocess then 0
else
 for notprocessed = empty:seq.symdef, changed = false, xx ∈ toprocess do
  let processed = 
   for args = empty:seq.int, defined = true, ele ∈ code.xx
   while defined
   do let tp = findtemplate.ele
   if isempty.tp then 
     let discard6=if name.module.ele /in "$int" then let discard5 = buildconst(ele, alltypes) 0 else 0 
     next(empty:seq.int, false)else next(args + arg.tp_1, true)
   /for(if defined then
    let discard = addtemplate(sym.xx, 0, emptyinternalbc,"ACTARG"_1, slot.addobject.args)
    true
   else false /if)
  next(if processed then notprocessed else notprocessed + xx, changed ∨ processed)
 /for(assert changed
 report"problem processconst"
 + for txt = "", xx2 ∈ notprocessed do
  let txt2 = 
   for txt2 = "", ele ∈ code.xx2 do
    let tp = findtemplate.ele
    if isempty.tp then txt2 + print.ele else txt2
   /for(txt2)
  txt + txt2
 /for(txt)
 if not.changed then 0 else processconst(notprocessed,alltypes) /if)
 
 Function mangledname(extname:set.symdef, s:symbol,loc:seq.word)word
 mangledname(extname,s,loc,symbolref.0)
 
 Function mangledname(extname:set.symdef,s:symbol,loc:seq.word,ref:symbolref)word
   if name.module.s ∈ "internal"then 
    if externalcall.s then  name.s 
    else 
      merge.[toword.toint.ref,"$"_1,"$"_1,toword.toint.ref]
   else
 let t=  name.first.getCode(extname,s)
    assert  toint.ref > 0 /or loc_1 /in "codegen" /or name.s /in "entrypoint addlibrarywords" report "HERE f"+loc+print.s
  {  assert toint.ref /le 0 /or merge.[library.module.s,"$"_1,"$"_1,toword.toint.ref]=t  report "XXX"+print.s
     +t+merge.[library.module.s,"$"_1,"$"_1,toword.toint.ref]}
    t
