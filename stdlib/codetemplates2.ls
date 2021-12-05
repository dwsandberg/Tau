#!/bin/sh tau   stdlib stdlib

Module codetemplates2

use bits

use codetemplates


use internalbc

use libraryModule

use llvm

use llvmconstants

use mangle

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

Function stepone(info:compileinfo, dependentlibs:seq.word, thename:word)steponeresult
let discard1 = initmap5
let alltypes=typedict.info
let newmaplength=newmaplength.info
let symdecode = symbolrefdecode.info
for acc = empty:set.symbol
, fref = empty:set.symbol
, crecord = empty:seq.symdef
, defines = empty:set.symdef
, extnames = externnames.dependentlibs
, processed=empty:set.symbol
,c ∈ prgcode.info
do
 let ele=symdecode_(toint.first.c)
 let sd = 
  symdef(ele
  , for code1 = empty:seq.symbol, r ∈ c << 1 do code1 + symdecode_(toint.r)/for(code1)
  )
 if isrecordconstant.ele then 
  let code1 = code.sd
  let code = 
   if isSequence.last.code1 then[Lit.0, Lit.nopara.last.code1] + code1 >> 1 else code1 >> 1
   next(acc /cup asset.code, fref, crecord + symdef(ele,code), defines,  extnames,processed+ele)
   else if isGlobal.ele then
   let discard5 = 
    addtemplate(ele
    , 1
    , GEP(r.1
    , i64
    , slot.global([ merge("$" + toword.toint.symbolref.ele + "$")], i64, C64.0)
    )
    )
   next(acc, fref, crecord, defines,  extnames,processed+ele)
  else if inModFor.ele ∨ ele = Optionsym then next(acc, fref, crecord, defines,  extnames,processed+ele)
  else if isBuiltin.ele then
   if wordname.ele = "createthreadY"_1 then
    let rt = parameter.para.module.ele
    let l = 
     for l = empty:seq.llvmtype, e ∈ paratypes.ele << 3 do l + tollvmtype(alltypes, e)/for(l + tollvmtype(alltypes, rt))
    let discard5 = addtemplate(ele, 0, emptyinternalbc, wordname.ele, nopara.ele , l)
    next(acc, fref, crecord, defines,  extnames,processed+ele)
   else next(acc, fref, crecord, defines,  extnames,processed+ele)
  else
   let d = code.sd
   let options = getoption.d
  let callit = 
   "COMPILED"_1 ∈ options
   ∨ if isInternal.ele then
 extname.ele
    ∉ "DIVint GTint MULreal SUBreal not getseqtype getseqlength ORDreal casttoreal setint intpart ADDreal SUBint EQboolean 
 SHLint setptr bitcast DIVreal ORDint toreal tointbit ADDint EQint tointbyte SHRint ANDbits representation MULint xor 
 ORbits"
else isempty.d
    if callit then
    let discard5 = call(alltypes, ele,"CALL"_1,   mangledname(extnames,ele))
    next(acc, fref, crecord, defines,  extnames,processed+ele)
   else
    let r = toint.first.c
    let extname = 
    merge([thename]
    + if r ≤ newmaplength then"$$" + toword.r else"$$" + toword.r + "$"/if)
    next(acc /cup asset.d, fref, crecord, defines + sd,   add( extnames,ele,extname),processed+ele)
/for(let q=processed
 let new = 
 for new = empty:set.symbol, sym ∈ toseq.acc do if sym ∈ q then new else new + sym /for(new)
uses(alltypes, q, new, fref, crecord
, defines, newmaplength, thename, extnames, symdecode
))

Function uses(alltypes:typedict
, processed:set.symbol
, toprocess:set.symbol
, infref:set.symbol
, isrecordconstant:seq.symdef
, indefines:set.symdef
, newmaplength:int
, thename:word
, extnamesin:set.symdef
,symboldecode:seq.symbol
)steponeresult
for fref = infref, defines = indefines, extnames = extnamesin, @e ∈ toseq.toprocess do
 if isabstract.module.@e then next(fref, defines, extnames)
 else
  let ele = @e
  if isFref.ele ∧ (basesym.ele ∈ processed ∨ basesym.ele ∈ toprocess)then next(fref + @e, defines, extnames)
  else if isconst.ele ∧ not.isFref.ele then
    assert not.isrecordconstant.@e report "PROBLEM2"
   let discard5 = buildconst(ele, alltypes)
   next( fref,  defines,  extnames)
  else if isspecial.ele then
   let discard5 = buildspecial(ele, alltypes)
   next( fref,  defines,  extnames)
  else if isGlobal.ele then
   let discard5 = 
    addtemplate(ele
    , 1
    , GEP(r.1
    , i64
    , slot.global([ merge("$" + toword.toint.symbolref.ele + "$")], i64, C64.0)
    )
    )
   next( fref,  defines,  extnames)
  else if inModFor.ele ∨ @e = Optionsym then next( fref,  defines,  extnames)
  else if isBuiltin.ele then
   if wordname.ele = "createthreadY"_1 then
    let rt = parameter.para.module.ele
    let l = 
     for l = empty:seq.llvmtype, e ∈ paratypes.ele << 3 do l + tollvmtype(alltypes, e)/for(l + tollvmtype(alltypes, rt))
    let discard5 = addtemplate(ele, 0, emptyinternalbc, wordname.ele, nopara.ele , l)
    next( fref,  defines,  extnames)
   else next( fref,  defines,  extnames)
  else
   let  yy= if isFref.ele then basesym.ele else ele
   if isInternal.yy
   ∧ extname.yy
   ∈ "DIVint GTint MULreal SUBreal not getseqtype getseqlength ORDreal casttoreal setint intpart ADDreal SUBint EQboolean 
 SHLint setptr bitcast DIVreal ORDint toreal tointbit ADDint EQint tointbyte SHRint ANDbits representation MULint xor 
 ORbits" then
     let r = findindex(yy,symboldecode )
     assert  r < length.symboldecode report "problem onestep"+print.yy
    let extname = 
     merge([thename]
     + if r ≤ newmaplength then"$$" + toword.r else"$$" + toword.r + "$"/if)
    next(if isFref.ele then fref + ele else fref
    , defines + symdef(@e, empty:seq.symbol)
    , add(extnames, yy, extname)
    )
   else
      let discard5 = call(alltypes, yy,"CALL"_1,   mangledname(extnames,yy))
    next( if isFref.ele then fref+ele else fref,  defines,  extnames)
/for( let defines2 = 
 for acc = 0, sd ∈ toseq.defines do
  let ele=sym.sd
  let name=mangledname(extnames, ele)
  let discard = funcdec(alltypes, ele,name)
  let discard5 = call(alltypes, ele,"CALL"_1,  name)
  acc
 /for(toseq.defines)
let discard2 = buildFref( toseq.fref, alltypes,extnames)
let discard4 = processconst.isrecordconstant
steponeresult(empty:seq.match5, defines2, extnames))

Export extnames(steponeresult) set.symdef

type steponeresult is match5map:seq.match5, defines:seq.symdef,extnames:set.symdef

Export match5map(steponeresult)seq.match5

Export defines(steponeresult)seq.symdef,

Export type:steponeresult

function buildFref(other:seq.symbol, alltypes:typedict, extnames:set.symdef)seq.match5
for acc = empty:seq.match5, e ∈ other do
 let f1 = basesym.e
 let functyp = ptr.tollvmtype(alltypes, f1)
 let discard = 
  addtemplate(e
  , 0
  , emptyinternalbc
  ,"ACTARG"_1
  , ptrtoint(functyp, symboltableentry([ mangledname(extnames, f1)], functyp))
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

 Function processconst(toprocess:seq.symdef)int
if isempty.toprocess then 0
else
 for notprocessed = empty:seq.symdef, changed = false, xx ∈ toprocess do
  let processed = 
   for args = empty:seq.int, defined = true, ele ∈ code.xx
   while defined
   do let tp = findtemplate.ele
   if isempty.tp then next(empty:seq.int, false)else next(args + arg.tp_1, true)
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
 if not.changed then 0 else processconst.notprocessed /if)