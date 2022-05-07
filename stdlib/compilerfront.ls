Module compilerfront

use mytype

use passparse

use passsymbol

use postbind

use standard

use symbol

use symbol2

use typedict

use seq.modExports

use seq.modref

use set.modref

use otherseq.mytype

use seq.mytype

use set.mytype

use seq.passsymbols

use set.passsymbols

use set.passtypes

use encoding.symbol

use seq.symbol

use set.symbol

use seq.symdef

use set.symdef

use seq.symtextpair

use set.word

use seq.seq.mytype

use set.seq.mytype

use seq.set.symdef

use seq.seq.word

Export type:typedict

-----

Export exports(modExports)seq.symbol

Export modname(modExports)modref

Export types(modExports)seq.seq.mytype

Export modExports(modname:modref, exports:seq.symbol, types:seq.seq.mytype)modExports

Export type:modExports

function types(libinfo:midpoint)seq.seq.mytype
for acc = empty:seq.seq.mytype, m ∈ libmods.libinfo do acc + types.m /for(acc)

function mods(mp:midpoint)seq.passsymbols
for acc = empty:seq.passsymbols, m ∈ libmods.mp do acc + toPasssymbols.m /for(acc)

function toPasssymbols(a:modExports)passsymbols
passsymbols(modname.a
, empty:set.modref
, empty:set.symbol
, asset.exports.a
, empty:set.symbol
, for types = empty:set.mytype, sym ∈ exports.a do
 if name.sym = "type"_1 then types + resulttype.sym else types
/for(types)
, empty:seq.symtextpair
)

Function compilerfront3(option:seq.word, allsrc:seq.seq.word, libinfo:midpoint)midpoint
let lib = first.extractValue(first.allsrc, "Library library")
let exports = extractValue(first.allsrc, "exports")
if option = "library"then
 midpoint(option, prg.libinfo, emptytypedict, empty:seq.modExports, empty:seq.seq.word)
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
  let requireUnbound = buildrequires(prga + toseq.code.t5 + toseq.prg.libinfo)
  let prg = compile(allmods, asset.simple, lib, allsrc, option = "text", requireUnbound)
  asset(prga + toseq.code.t5 + toseq.prg.libinfo + prg))
 if option = "text"then
  {let zz1=toseq.prg10 let discard=for acc=symbolref.sym.zz1_1, d ∈ zz1 do if paragraphno.d > 0 then symbolref.sym.d else 
acc /for(acc)}
  midpoint(option, asset.toseq.prg10, emptytypedict, empty:seq.modExports, allsrc)
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
   , toModules(typedict, toseq.modules.t5, exports)
   , empty:seq.seq.word
   )
  else
   let templates = 
    for acc = empty:seq.symdef, p ∈ toseq.prg10 do if para.module.sym.p = typeT then acc + p else acc /for(asset.acc)
   let prg10a = processOptions(prg10, toseq.modules.t5, "NOINLINE")
   let pb = postbind(roots, prg10a, templates, typedict)
   let afteroption = processOptions(prg.pb, toseq.modules.t5, "COMPILETIME NOINLINE INLINE PROFILE STATE")
   let libmods = toModules(typedict, toseq.modules.t5, exports)
   if option = "pass1"then
    midpoint(option, afteroption, typedict.pb, libmods, empty:seq.seq.word)
   else midpoint(option, afteroption, templates, typedict, libmods, [first.allsrc])

Export midpoint(option:seq.word, prg:set.symdef, typedict:typedict, libmods:seq.modExports, src:seq.seq.word)midpoint

Export prg(midpoint)set.symdef

Export option(midpoint)seq.word

Export templates(midpoint)set.symdef

Export typedict(midpoint)typedict

Export type:midpoint

Export src(midpoint)seq.seq.word

Export libmods(m:midpoint)seq.modExports

Function addoption(p:set.symdef, s:symbol, option:seq.word)set.symdef
{must maintain library of symbol in p}
let f = lookup(p, symdef(s, empty:seq.symbol))
let code = if isempty.f then empty:seq.symbol else code.f_1
let current = asset.getoption.code
if current = asset.option then p
else
 let newcode = removeoptions.code + Words.toseq(current ∪ asset.option) + Optionsym
 symdef(if isempty.f then s else sym.f_1, newcode) ∪ p

Function processOptions(prg:set.symdef, mods:seq.passsymbols, option:seq.word)set.symdef
for acc = prg, m ∈ mods do
 if name.module.m ∈ option then
  for acc2 = acc, sym ∈ toseq.exports.m do addoption(acc2, sym, [name.module.m])/for(acc2)
 else acc
/for(acc)

Function toModules(alltypes:typedict, t5:seq.passsymbols, exports:seq.word)seq.modExports
for acc = empty:seq.modExports, m2 ∈ t5 do
 if name.module.m2 ∉ exports then acc
 else
  let d2 = if isabstract.module.m2 then defines.m2 else exports.m2
  let exps = 
   for acc3 = empty:seq.symbol, e ∈ toseq.d2 do if isunbound.e then acc3 else acc3 + e /for(acc3)
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
  acc + modExports(module.m2, exps, types)
/for(acc)

function uses(toprocess:seq.symbol, org:set.symdef, new:set.symdef)set.symdef
for newsym = empty:seq.symbol, newsd = new, sym ∈ toprocess do
 let t = lookup(new, symdef(sym, empty:seq.symbol, 0))
 if not.isempty.t then next(newsym, newsd)
 else
  let t2 = lookup(org, symdef(sym, empty:seq.symbol, 0))
  if isempty.t2 then next(newsym, newsd + symdef(sym, empty:seq.symbol, cardinality.newsd))
  else
   next(for acc = newsym, sym2 ∈ code.t2_1 do
    if isspecial.sym2 then acc
    else if isconst.sym2 then
     if not.hasfref.sym2 then acc
     else if isFref.sym2 then acc + basesym.sym2
     else
      let r = findfref(sym2, empty:set.symbol, org)
      for acc2 = acc, sym3 ∈ toseq.r do if isrecordconstant.sym3 then acc2 else acc2 + sym3 /for(acc2)
    else acc + sym2
   /for(acc)
   , newsd + symdef(sym, code.t2_1, cardinality.newsd)
   )
/for(if isempty.new then newsd else uses(toseq.asset.newsym, org, newsd)/if)

function findfref(sym:symbol, result:set.symbol, org:set.symdef)set.symbol
for new = empty:set.symbol, out = result, e ∈ code.lookup(org, symdef(sym, empty:seq.symbol, 0))_1 do
 if hasfref.e then if isFref.e then next(new, out + basesym.e)else next(new + e, result)
 else next(new, result)
/for(let t = new \ out
for acc = result, sym3 ∈ toseq.t do findfref(sym3, acc, org)/for(acc))

if isempty.t then result else findfref(t, result)) 