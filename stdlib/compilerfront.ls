Module compilerfront

use libraryModule

use mytype

use passparse

use passsymbol

use postbind

use standard

use symbol

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

use seq.seq.symbolref

use seq.set.symdef

use seq.seq.word

Export type:liblib

Export getlibrarysrc(seq.word)seq.seq.word

Export words(liblib)seq.encodingpair.seq.char

Export type:typedict

----

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Export libraryModule(modname:modref, exports:seq.symbolref, types:seq.seq.mytype)libraryModule

Export type:libraryModule

Export exports(libraryModule)seq.symbolref

Export modname(libraryModule)modref

Export types(libraryModule)seq.seq.mytype

Function extract(which:seq.word, s:seq.word)seq.word
let libclause = break(s, "uses exports", true)
 assert length.libclause > 2 report"PROBLEM in libraryclause"+s
if which = "exports"then 
libclause_3 << 1
else if which = "library"then
assert length.libclause_1 > 0 report"PROBLEM in libraryclause"+s
[libclause_1_2]
else
 assert which = "uses"report"PROBLEM in libraryclause"+s
 libclause_2 << 1

Function compilerfront3(option:seq.word, allsrc:seq.seq.word, libinfo:loadedresult)midpoint
let libclause = break(allsrc_1, "uses exports", true)
let lib = libclause_1_2
let exports = {libclause_3 << 1}extract("exports", allsrc_1)
if option = "library"then
 let zz1 = prg.libinfo
 let discard = for acc = symbolref.sym.zz1_1, d ∈ zz1 do symbolref.sym.d /for(acc)
 midpoint(option, asset.prg.libinfo, emptytypedict, empty:seq.libraryModule, empty:seq.seq.word)
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
 {figure out how to interpret text form of type}
 let modsx = resolvetypes(libpasstypes, allsrc, lib)
 {figure out how to interpret text form of symbol}
 let t5 = resolvesymbols(allsrc, lib, modsx, asset.mods.libinfo)
 {parse the function bodies}
 let prg10 = 
  for abstract = empty:seq.passsymbols, simple = empty:seq.passsymbols, m ∈ toseq.modules.t5 do
   if isabstract.modname.m then next(abstract + m, simple)else next(abstract, simple + m)
  /for(let allmods = asset(abstract + simple)
  let prga = 
   prescan2.compile(allmods, asset.abstract, lib, allsrc, option = "text", empty:set.symdef)
  let requireUnbound = buildrequires(prga + toseq.code.t5 + prg.libinfo)
  let prg = compile(allmods, asset.simple, lib, allsrc, option = "text", requireUnbound)
  asset(prga + toseq.code.t5 + prg.libinfo + prg))
 if option = "text"then
  let zz1 = toseq.prg10
  let discard = 
   for acc = symbolref.sym.zz1_1, d ∈ zz1 do if paragraphno.d > 0 then symbolref.sym.d else acc /for(acc)
  midpoint(option, asset.zz1, emptytypedict, empty:seq.libraryModule, allsrc)
 else
  let roots = 
   for acc = [outofboundssymbol], f ∈ toseq.modules.t5 do
    if name.module.f ∉ exports then acc
    else if issimple.module.f then acc + toseq.exports.f
    else
     for acc2 = empty:seq.symbol, sym ∈ toseq.defines.f do acc2 + getCode(prg10, sym)/for(for acc3 = acc, sym2 ∈ toseq.asset.acc2 do
      if isabstract.module.sym2 ∨ isconstantorspecial.sym2 ∨ isBuiltin.sym2
      ∨ name.module.sym2 ∈ "$for"then
       acc3
      else acc3 + sym2
     /for(acc3))
   /for(acc)
  let typedict = buildtypedict(empty:set.symbol, types.t5 + types.libinfo)
  if option = "hhh"then
   let hmods = 
    for acc = empty:seq.passsymbols, m ∈ toseq.modules.t5 do
     acc
     + passsymbols(modname.m
     , empty:set.modref
     , if isabstract.module.m then defines.m else empty:set.symbol
     , exports.m
     , empty:set.symbol
     , typedict.m
     , empty:seq.symtextpair
     )
    /for(acc)
   midpoint(option
   , for acc = empty:set.symdef, d ∈ toseq.prg10 do if issimple.module.sym.d then acc else acc + d /for(acc)
   , typedict
   , tolibraryModules(typedict, toseq.modules.t5, exports)
   , empty:seq.seq.word
   )
  else
   let templates = 
    for acc = empty:seq.symdef, p ∈ toseq.prg10 do if para.module.sym.p = typeT then acc + p else acc /for(asset.acc)
   let prg10a = processOptions(prg10, toseq.modules.t5, "NOINLINE")
   let pb = postbind(roots, prg10a, templates, typedict)
   let afteroption = processOptions(prg.pb, toseq.modules.t5, "COMPILETIME NOINLINE INLINE PROFILE STATE")
   let libmods = tolibraryModules(typedict, toseq.modules.t5, exports)
   if option = "pass1"then
    midpoint(option, afteroption, typedict.pb, libmods, empty:seq.seq.word)
   else midpoint(option, afteroption, templates, typedict, libmods, [first.allsrc])

function midpoint(option:seq.word
, prg:set.symdef
, typedict:typedict
, libmods:seq.libraryModule
, libclause:seq.seq.word
)midpoint
midpoint(option, prg, empty:set.symdef, typedict, libmods, libclause)

Export prg(midpoint)set.symdef

Export option(midpoint)seq.word

Export templates(midpoint)set.symdef

Export typedict(midpoint)typedict

Export type:midpoint

Export prg(midpoint)set.symdef

Export templates(midpoint)set.symdef

Export src(midpoint)seq.seq.word

Export libmods(midpoint)seq.libraryModule

type midpoint is option:seq.word
, prg:set.symdef
, templates:set.symdef
, typedict:typedict
, libmods:seq.libraryModule
, src:seq.seq.word


Export type:compileinfo

Export roots(s:compileinfo)set.symbol

Export code(compileinfo)seq.seq.symbolref

Export mods(compileinfo)seq.libraryModule

Export typedict(compileinfo)typedict

Export symbolrefdecode(compileinfo)seq.symbol

Export src(compileinfo)seq.seq.word

Function prg(s:compileinfo)seq.symdef
for acc4 = empty:seq.symdef, c ∈ code.s do
 let sym = s_(c_1)
 acc4 + symdef(sym, for acc = empty:seq.symbol, r ∈ c << 2 do acc + s_r /for(acc))
/for(acc4)

Function addoption(p:set.symdef, s:symbol, option:seq.word)set.symdef
{must maintain library of symbol in p}
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

Export loadedresult(mods:seq.passsymbols, types:seq.seq.mytype, prg:seq.symdef)loadedresult

Function empty:loadedresult loadedresult loadedresult(empty:seq.passsymbols, empty:seq.seq.mytype, empty:seq.symdef)

Function toloadedresult(org:loadedresult, libinfo:compileinfo, libname:word)loadedresult
let orgprg = asset.prg.org
let prg0 = 
 for acc = orgprg, c ∈ code.libinfo do
  if toint.first.c = 0 then acc
  else
   for code = empty:seq.symbol, r ∈ c << 1 do code + libinfo_r /for(symdef(libinfo_(c_1), code) ∪ acc)
 /for(acc)
let prg = 
 for acc = prg0, idx = 1, sym ∈ symbolrefdecode.libinfo do
  if isconstantorspecial.sym ∨ isabstract.module.sym ∨ library.module.sym ≠ libname then next(acc, idx + 1)
  else next(symdef(sym, addoption(getCode(acc, sym), "COMPILED")) ∪ acc, idx + 1)
 /for(toseq.acc)
loadedresult(for mods = mods.org, m ∈ mods.libinfo do
 for exports = empty:seq.symbol, types = empty:seq.mytype, r ∈ exports.m do
  let sym = libinfo_r
  next(exports + sym
  , if name.sym = "type"_1 then types + resulttype.sym else types
  )
 /for(mods
 + passsymbols(modname.m
 , empty:set.modref
 , empty:set.symbol
 , asset.exports
 , empty:set.symbol
 , asset.types
 , empty:seq.symtextpair
 ))
/for(mods)
, for acc = types.org, m2 ∈ mods.libinfo do acc + types.m2 /for(acc)
, prg
)

Function processOptions(prg:set.symdef, mods:seq.passsymbols, option:seq.word)set.symdef
for acc = prg, m ∈ mods do
 if name.module.m ∈ option then
  for acc2 = acc, sym ∈ toseq.exports.m do addoption(acc2, sym, [name.module.m])/for(acc2)
 else acc
/for(acc)

Function tolibraryModules(alltypes:typedict, t5:seq.passsymbols, exports:seq.word)seq.libraryModule
for acc = empty:seq.libraryModule, m2 ∈ t5 do
 if name.module.m2 ∉ exports then acc
 else
  let d2 = if isabstract.module.m2 then defines.m2 else exports.m2
  let exps = 
   for acc3 = empty:seq.symbolref, e ∈ toseq.d2 do if isunbound.e then acc3 else acc3 + symbolref.e /for(acc3)
  let types = 
   for acc5 = empty:seq.seq.mytype, s ∈ toseq.d2 do
    if istype.s then
     if isseq.resulttype.s then acc5 + [resulttype.s, typeint]
     else
      let c = 
       for c = empty:seq.mytype, t ∈ flatflds(alltypes, resulttype.s)do
        c + if isencoding.t ∨ {t=typeword ∨}t = typechar then typeint else t
       /for(c)
      acc5 + ([resulttype.s] + c)
    else acc5
   /for(acc5)
  acc + libraryModule(module.m2, exps, types)
/for(acc) 