#!/bin/sh tau   stdlib stdlib

Module compilerfront

use libraryModule

use mytype

use pass2

use passparse

use passsymbol

use postbind

use standard

use symbol

use symref

use typedict

use seq.libraryModule

use seq.modref

use set.modref

use seq.mytype

use set.mytype

use seq.passsymbols

use set.passsymbols

use set.passtypes

use encoding.symbol

use seq.symbol

use set.symbol

use seq.symbolref

use set.symbolref

use seq.symdef

use set.symdef

use seq.symtextpair

use set.word

use seq.seq.mytype

use seq.encodingpair.symbol

use seq.seq.symbolref

use seq.set.symdef

use seq.seq.word

Export type:liblib

Export getlibrarysrc(seq.word)seq.seq.word

Export words(liblib)seq.encodingpair.seq.char

Export type:typedict

Export coretype(mytype, typedict)mytype

----

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Export libraryModule(modname:modref, exports:seq.symbolref, types:seq.seq.mytype)libraryModule

Export type:libraryModule

Export exports(libraryModule)seq.symbolref

Export modname(libraryModule)modref

Export types(libraryModule)seq.seq.mytype

Function compilerfront(option:seq.word, libname:seq.word, allsrc:seq.seq.word, dependentlibs:seq.word, exports:seq.word)compileinfo
{ assert false report allsrc @+("", @e)}
{ let libinfo=libinfo.dependentlibs }
let lib = last.libname
let libinfo = libmodules2.dependentlibs
{ assert isempty.mods.libinfo report for txt="testingx", sd=prg.libinfo do if name.module.sym.sd /in"llvm"then txt 
+print.sym.sd+print.code.sd+EOL else txt /for(txt)}
if option = "library"then
 let zz1 = prg.libinfo
 let discard = for acc = symbolref.sym.zz1_1, d ∈ zz1 do symbolref.sym.d /for(acc)
 compileinfo(prg.libinfo, emptytypedict, empty:seq.libraryModule, empty:seq.seq.word)
else
 let libpasstypes = 
  for acc = empty:set.passtypes, m ∈ mods.libinfo do
   let tmp = 
    for tmp = empty:set.mytype, t ∈ types.libinfo do
     let mt = abstractModref.first.t
     let mt2 = if isabstract.mt then replaceT(parameter.first.t, mt)else mt
     if mt2 = modname.m then tmp + first.t else tmp
    /for(tmp)
   acc + passtypes(modname.m, tmp, typedict.m)
  /for(acc)
 { assert isempty.libpasstypes report for txt="types", t=types.libinfo do txt+print.first.t /for(txt)+"passtypes 
"+for txt="", p=toseq.libpasstypes do txt+print.p /for(txt)}
 let mode = 
  if option = "text"then"text"_1 else"body"_1
 { figure out how to interpret text form of type }
 let modsx = resolvetypes(libpasstypes, allsrc, lib)
 { figure out how to interpret text form of symbol }
 let t5 = resolvesymbols(allsrc, lib, modsx, asset.mods.libinfo)
 { assert false report for libs=empty:seq.word, p=toseq.modules.t5 do libs+library.modname.p+name.modname.p+EOL 
 /for(libs)}
 { parse the function bodies }
 let prg10 = 
  for abstract = empty:seq.passsymbols, simple = empty:seq.passsymbols, m ∈ toseq.modules.t5 do
   if isabstract.modname.m then next(abstract + m, simple)else next(abstract, simple + m)
  /for(passparse(asset.abstract, asset.simple, lib, toseq.code.t5 + prg.libinfo, allsrc, mode))
 let typedict = buildtypedict(empty:set.symbol, types.t5 + types.libinfo)
 if mode = "text"_1 then
  let zz1 = toseq.prg10
  let discard = 
   for acc = symbolref.sym.zz1_1, d ∈ zz1 do if paragraphno.d > 0 then symbolref.sym.d else acc /for(acc)
  compileinfo(zz1, emptytypedict, empty:seq.libraryModule, allsrc)
 else
  { assert isempty.mods.libinfo report print(typedict0)+"NNN"+for txt="", t=types.t5 do txt+print.t+EOL /for(txt 
)}
  let templates = 
   for acc = empty:seq.symdef, p ∈ toseq.prg10 do if para.module.sym.p = typeT then acc + p else acc /for(asset.acc)
  let roots = 
   for acc = [ symbol(modTausupport,"outofbounds", seqof.typeword)], f ∈ toseq.modules.t5 do
    if name.module.f ∉ exports then acc
    else if issimple.module.f then acc + toseq.exports.f
    else
     for acc2 = empty:seq.symbol, sym ∈ toseq.defines.f do acc2 + getCode(prg10, sym)/for(for acc3 = acc, sym2 ∈ toseq.asset.acc2 do
      if isabstract.module.sym2 ∨ isconstantorspecial.sym2 ∨ isBuiltin.sym2 
       /or name.module.sym2 /in "$for"
      then acc3 else acc3 + sym2
     /for(acc3))
   /for(acc)
  let prg10a = processOptions(prg10, toseq.modules.t5,"NOINLINE")
  let pb = postbind(roots, prg10a, templates, typedict)
  let afteroption = processOptions(prg.pb, toseq.modules.t5,"COMPILETIME NOINLINE INLINE PROFILE STATE")
  let result = 
   if option = "wasm"then
    for acc0 = afteroption, root ∈ toseq.asset.roots do
     for acc = acc0, sym ∈ toseq.expand(4, afteroption, root)do addoption(acc, sym,"INLINE")/for(acc)
    /for(acc0)
   else afteroption
  if option = "pass1"then compileinfo(toseq.result
  , typedict.pb
  , tolibraryModules(typedict, toseq.modules.t5, exports)
  , empty:seq.seq.word
  ) else 
  let  prg5=pass2.result ∪ templates
  let libmods=tolibraryModules(typedict, toseq.modules.t5, exports)
  {let tmps= libprg(typedict,prg5,libmods,asset.roots)}
  compileinfo(toseq.prg5
  , typedict.pb
  , libmods
  , empty:seq.seq.word
  )

 
Function libcode(prg:set.symdef,code1:seq.symbol, toexport:set.symbol)seq.symbol
let code = removeoptions.code1
let optionsx = getoption.code1
let z = 
 if length.code < 15 then
  let x =  removerecordconstant(prg,code)
  if"VERYSIMPLE"_1 ∈ optionsx then x
  else if for acc = true, @e ∈ x do
   acc ∧ (isconst.@e ∨ isBuiltin.@e ∧ para.module.@e ∈ [ typereal, typeint] ∨ isspecial.@e ∨ @e ∈ toexport)
  /for(acc)then
   x
  else empty:seq.symbol
 else empty:seq.symbol
if"COMPILETIME"_1 ∈ optionsx ∨ not.isempty.z then z + Words.optionsx + Optionsym else z

function libprg(alltypes:typedict,prg:set.symdef, mods:seq.libraryModule,roots:set.symbol) compileinfo
 let libprg=for acc = empty:seq.symbolref, m ∈ mods do acc + exports.m 
 /for(let decode=symbolrefdecode
  for acc2 = empty:set.symbol, r ∈ toseq.asset.acc do 
   acc2 +  decode_(toint.r)
   /for(close(prg,acc2,true)))
 let genprg=close(prg,roots,false)
 let profilearcs = 
 for acc = empty:seq.symbolref, sd ∈ toseq.genprg do
  if"PROFILE"_1 ∉ getoption.code.sd then acc
  else
   for txt = acc, sym ∈ toseq.asset.code.sd do
    if isconstantorspecial.sym ∨ isInternal.sym then txt
     else txt +  symbolref.sym.sd+ symbolref.sym
   /for(txt)
 /for(acc)
  let primary=tosyms.libprg /cup asset.profilearcs
 let secondary=tosyms.genprg \ primary
 let libcode=symbolref(libprg,primary,secondary)
 let gencode=symbolref(genprg,primary,secondary)
  let symdecode = 
 for acc = empty:seq.symbol,  sd ∈ toseq.libprg +toseq.genprg do acc + sym.sd /for(acc)
 compileinfo(alltypes, gencode, empty:seq.seq.word, symdecode
 , mods)

  { decode=primary+secondary, maxprimary=length.primary
      gencode }
      "hi"
 
 function tosyms(prg:set.symdef) set.symbolref
   for acc=empty:seq.symbolref ,sd /in toseq.prg do acc+symbolref.sym.sd /for(asset.acc)
  
function   close(prg:set.symdef,symlist: set.symbol,libdesc:boolean) set.symdef
  if isempty.symlist then prg else 
  for defs = empty:set.symdef, toprocess=empty:seq.symbol, sym ∈ toseq.symlist do
   let sd=if not.libdesc /or isabstract.module.sym then 
      symdef(sym,getCode(prg, sym))
      else symdef(sym,libcode(prg,getCode(prg, sym),symlist))
        next(defs+sd,toprocess+if isFref.sym then
              [basesym.sym]
      else if isrecordconstant.sym then
          removerecordconstant(prg,[sym])
      else code.sd)
   /for( 
       close(prg,asset.toprocess \ symlist,libdesc))
   
   use otherseq.symbolref
   
 function symbolref(prg:set.symdef, primary:set.symbolref,secondary:set.symbolref)
 seq.seq.symbolref
 for acc0=empty:seq.seq.symbolref, sd /in toseq.prg do 
  if isempty.code.sd then acc0 else 
 for acc = empty:seq.symbolref, r ∈ [sym.sd]+code.sd do 
    let ref=symbolref.r
    let one=binarysearch(toseq.primary, ref)
    let two=if one > 0 then one else 
       binarysearch(toseq.secondary, ref)+cardinality.primary
    acc + symbolref.two 
  /for(acc0+acc)
  /for(acc0)
  
   
  
  

function expand(level:int, prg:set.symdef, symin:symbol)set.symbol
for acc = empty:set.symbol, sym ∈ getCode(prg, symin)do
 if isspecial.sym ∨ isconst.sym ∨ name.module.sym ∈ "internal builtin UTF8 seq"then acc
 else if name.sym ∈ "putfile jsgetfile"then acc + symin
 else if level = 0 then acc
 else
  let s = expand(level - 1, prg, sym)
  if isempty.s then acc else acc ∪ expand(level - 1, prg, sym) + symin
/for(acc)

Export type:compileinfo

Export roots(s:compileinfo)set.symbol

Export code(compileinfo)seq.seq.symbolref

Export mods(compileinfo)seq.libraryModule

Export typedict(compileinfo)typedict

Export symbolrefdecode(compileinfo)seq.symbol

Export src(compileinfo)seq.seq.word

Function prg(s:compileinfo)seq.symdef
let symdecode = symbolrefdecode.s
for acc4 = empty:seq.symdef, c ∈ code.s do
 let sym = symdecode_(toint.first.c)
 acc4
 + symdef(sym
 , for acc = empty:seq.symbol, r ∈ c << 2 do acc + symdecode_(toint.r)/for(acc)
 )
/for(acc4)

Function compileinfo(prg:seq.symdef, alltypes:typedict, mods:seq.libraryModule, src:seq.seq.word )compileinfo
compileinfo(alltypes, cvtL3(asset.prg, 1, empty:seq.seq.symbolref), src, symbolrefdecode, mods)

function cvtL3(prg:set.symdef, i:int, in:seq.seq.symbolref)seq.seq.symbolref
let x = encoding:seq.encodingpair.symbol
if i > length.x then in
else
 cvtL3(prg
 , length.x + 1
 , for acc = in, p ∈ subseq(x, i, length.x)do
  let f = lookup(prg, symdef(data.p, empty:seq.symbol))
  if isempty.f ∨ isempty.code.f_1 then acc
  else
   acc
   + for acc2 = [ symbolref.data.p, symbolref.Lit.paragraphno.f_1], sym ∈ code.f_1 do
    acc2
    + if isFref.sym then
     let discard = symbolref.basesym.sym
     symbolref.sym
    else if isrecordconstant.sym then
     let discard = 
      for acc3 = symbolref.Lit.0, sym2 ∈ removerecordconstant(prg,[ sym])do symbolref.sym2 /for(acc3)
     symbolref.sym
    else symbolref.sym
   /for(acc2)
 /for(acc)
 )
 


Function addoption(p:set.symdef, s:symbol, option:seq.word)set.symdef
{ must maintain library of symbol in p }
let f = lookup(p, symdef(s, empty:seq.symbol))
let code = if isempty.f then empty:seq.symbol else code.f_1
let current = asset.getoption.code
if current = asset.option then p
else
 let newcode = removeoptions.code + Words.toseq(current ∪ asset.option) + Optionsym
 symdef(if isempty.f then s else sym.f_1, newcode) ∪ p

type loadedresult is mods:seq.passsymbols, types:seq.seq.mytype, prg:seq.symdef

Export mods(loadedresult)seq.passsymbols

Export types(loadedresult)seq.seq.mytype

Export prg(loadedresult)seq.symdef

Export type:loadedresult

Function libmodules2(dependentlibs:seq.word)loadedresult
for org = loadedresult(empty:seq.passsymbols, empty:seq.seq.mytype, empty:seq.symdef)
, ll ∈ loadedLibs
do
 if(libname.ll)_1 ∈ dependentlibs then toloadedresult(org, ll)else org
/for(org)

function externalname(sym:symbol, ll:liblib, prg:set.symdef, idx:int)seq.word
if library.module.sym = (libname.ll)_1 then [ merge(libname.ll + "$$" + toword.idx)]
else externalname.getCode(prg, sym)

function toloadedresult(org:loadedresult, ll:liblib)loadedresult
let orgprg = asset.prg.org
let prg0 = 
 for acc = orgprg, c ∈ code.ll do
  let sym = (decoderef.ll)_(toint.c_1)
  let code = 
   for acc2 = empty:seq.symbol, r ∈ c << 1 do acc2 + (decoderef.ll)_(toint.r)/for(if isabstract.module.sym then acc2
   else
    let externalname = externalname(sym, ll, orgprg, toint.c_1)
    addoption(acc2, externalname)/if)
  symdef(sym, code) ∪ acc
 /for(acc)
let prg = 
 for acc = prg0, idx = 1, sym ∈ decoderef.ll do
  if isconstantorspecial.sym ∨ isabstract.module.sym then next(acc, idx + 1)
  else
   let code = getCode(prg0, sym)
   let externalname = externalname.code
   if not.isempty.externalname then next(acc, idx + 1)
   else
    next(symdef(sym, addoption(code, externalname(sym, ll, empty:set.symdef, idx))) ∪ acc, idx + 1)
 /for(acc)
for mods = mods.org, types1 = types.org, m ∈ newmods.ll do
 let modx = 
  for exports = empty:seq.symbol, types = empty:seq.mytype, r ∈ exports.m do
   let sym = (decoderef.ll)_(toint.r)
   next(exports + sym
   , if name.sym = "type"_1 then types + resulttype.sym else types
   )
  /for(passsymbols(modname.m
  , empty:set.modref
  , empty:set.symbol
  , asset.exports
  , empty:set.symbol
  , asset.types
  , empty:seq.symtextpair
  ))
 next(mods + modx, types1 + types.m)
/for(loadedresult(mods, types1, toseq.prg))

Function processOptions(prg:set.symdef, mods:seq.passsymbols, option:seq.word)set.symdef
let z = symbol(moduleref."stdlib standard","<", typeint, typeint, typeboolean)
let c1 = getCode(prg, z)
let pp = 
 for acc = prg, m ∈ mods do
  if name.module.m ∈ option then
   for acc2 = acc, sym ∈ toseq.exports.m do addoption(acc2, sym, [ name.module.m])/for(acc2)
  else acc
 /for(acc)
let c2 = getCode(prg, z)
assert c1 = c2 report"SFD" + print.c1 + EOL + print.c2
pp

Function tolibraryModules(alltypes:typedict, t5:seq.passsymbols, exports:seq.word)seq.libraryModule
{does this need typedec????}
for acc = empty:seq.libraryModule, typedec = empty:seq.seq.mytype, m2 ∈ t5 do
 if name.module.m2 ∉ exports then next(acc, typedec)
 else
  let d2 = if isabstract.module.m2 then defines.m2 else exports.m2
  let exps = 
   for acc3 = empty:seq.symbolref, e ∈ toseq.d2 do if isunbound.e then acc3 else acc3 + symbolref.e /for(acc3)
  let types = 
   for acc5 = empty:seq.seq.mytype, s ∈ toseq.d2 do
    if istype.s then
     if isseq.resulttype.s then acc5 + [ resulttype.s, typeint]
     else
      let c = 
       for c = empty:seq.mytype, t ∈ flatflds(alltypes, resulttype.s)do
        c + if isencoding.t ∨ { t=typeword ∨ } t = typechar then typeint else t
       /for(c)
      acc5 + ([ resulttype.s] + c)
    else acc5
   /for(acc5)
  next(acc + libraryModule(module.m2, exps, types), typedec + types)
/for(acc) 