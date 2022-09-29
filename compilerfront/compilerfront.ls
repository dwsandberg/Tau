Module compilerfront

use seq.commoninfo

use seq.modExports

use set.modref

use mytype

use seq.mytype

use seq.seq.mytype

use set.mytype

use passparse

use passsymbol

use seq.passsymbols

use set.passsymbols

use set.passtypes

use postbind

use standard

use symbol

use seq.symbol

use seq.seq.symbol

use set.symbol

use symbol2

use symboldict

use seq.symdef

use set.symdef

use typedict

use seq.seq.word

use set.word

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
, empty:seq.symdef
)

Function compilerfront3(option:seq.word, allsrc:seq.seq.word, libinfo:midpoint)midpoint
assert not.isempty.allsrc report"empty source"
let lib0 = extractValue(first.allsrc, "Library library")
assert not.isempty.lib0 report"no library specified"
let lib = first.lib0
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
 let allmods = asset(abstract.t5 + simple.t5)
 let prga = compile(allmods, asset.abstract.t5, lib, allsrc, option = "text", empty:set.symdef)
 let prgb = if option = "text"then prga else prescan2.prga
 let requireUnbound = buildrequires(prgb + toseq.code.t5 + toseq.prg.libinfo)
 let prg = compile(allmods, asset.simple.t5, lib, allsrc, option = "text", requireUnbound)
 let prg10 = asset(prgb + toseq.code.t5 + toseq.prg.libinfo + prg)
 if option = "text"then
  for acc = empty:set.symdef, sd ∈ toseq.prg10 do if library.module.sym.sd = lib then acc + sd else acc /for(let libmods = 
   for acc5 = empty:seq.modExports, m2 ∈ toseq.modules.t5 do acc5 + modExports(module.m2, toseq.exports.m2, empty:seq.seq.mytype)/for(acc5)
  midpoint(option, acc, requireUnbound, emptytypedict, {empty:seq.modExports}libmods, allsrc))
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
  let templates = 
   for acc = empty:seq.symdef, p ∈ toseq.prg10 do if para.module.sym.p = typeT then acc + p else acc /for(asset.acc)
  let pb = postbind(roots, prg10, templates, typedict)
  let afteroption = addExportOptions(asset.simple.t5, prg.pb, allsrc)
  let libmods = toModules(typedict, toseq.modules.t5, exports)
  if option = "pass1"then
   midpoint(option, afteroption, typedict.pb, libmods, empty:seq.seq.word)
  else midpoint(option, afteroption, templates, typedict, libmods, [first.allsrc])

Export midpoint(option:seq.word, prg:set.symdef, typedict:typedict, libmods:seq.modExports, src:seq.seq.
 word)midpoint

Export prg(midpoint)set.symdef

Export option(midpoint)seq.word

Export templates(midpoint)set.symdef

Export typedict(midpoint)typedict

Export type:midpoint

Export src(midpoint)seq.seq.word

Export libmods(m:midpoint)seq.modExports

Function addoption(p:set.symdef, s:symbol, option:seq.word)set.symdef
if isempty.option then p
else
 {must maintain library of symbol in p}
 let f = getSymdef(p, s)
 if isempty.f then symdef(s, [Words.toseq.asset.option, Optionsym], 0) ∪ p
 else
  let code = code.f_1
  let current = asset.getoption.code
  let newoptions = current ∪ asset.option
  if current = newoptions then p
  else
   let newcode = removeoptions.code + Words.toseq.newoptions + Optionsym
   symdef(sym.f_1, newcode, paragraphno.f_1) ∪ p

Function toModules(alltypes:typedict, t5:seq.passsymbols, exports:seq.word)seq.modExports
for acc = empty:seq.modExports, m2 ∈ t5 do
 if name.module.m2 ∉ exports then acc
 else
  let d2 = if isabstract.module.m2 then defines.m2 ∪ exports.m2 else exports.m2
  let exps = 
   for acc3 = empty:seq.symbol, e ∈ toseq.d2 do if isunbound.e then acc3 else acc3 + e /for(acc3)
  let types = 
   for acc5 = empty:seq.seq.mytype, s ∈ toseq.d2 do
    if istype.s then
     if isseq.resulttype.s then acc5 + [resulttype.s, typeint]
     else
      let c = 
       for c = empty:seq.mytype, t ∈ flatflds(alltypes, resulttype.s)do c + if isencoding.t ∨ t = typechar then typeint else t /for(c)
      acc5 + ([resulttype.s] + c)
    else acc5
   /for(acc5)
  acc + modExports(module.m2, exps, types)
/for(acc)

function roots(s1:seq.modExports)set.symbol
for exports = empty:seq.symbol, m ∈ s1 do exports + exports.m /for(asset.exports)

function close(prg:set.symdef, toprocess:set.symbol, processed:set.symbol, len:int)set.symbol
let toexport = toprocess \ processed
for new = empty:seq.symbol, sym ∈ toseq.toexport do
 let code = removeoptions.getCode(prg, sym)
 if len > 0 ∧ length.code ≥ len ∧ not.isabstract.module.sym then new
 else
  for acc = new, sym2 ∈ code do
   if isrecordconstant.sym2 then acc + sym2
   else if isFref.sym2 then acc + basesym.sym2
   else if isconstantorspecial.sym2 then acc
   else if name.module.sym2 ∈ "internal"then
    if name.sym2 ∈ "stacktrace"then acc + sym2 else acc
   else if name.module.sym2 ∈ "builtin $for $base"then acc else acc + sym2
  /for(acc)
/for(if isempty.toexport then processed else close(prg, asset.new, processed ∪ toprocess, len)/if)

Function prepareback(prg10:set.symdef, midin:midpoint, dependentlibs:midpoint)midpoint
{OPTION PROFILE}
let uses = extractValue(first.src.midin, "uses")
let libname = first.extractValue(first.src.midin, "Library")
let typedict = typedict.midin
let oldmods = libmods.midin
let libextnames = 
 for acc = empty:seq.symdef, sd ∈ toseq.prg.dependentlibs do if paragraphno.sd = 0 then acc else acc + sd /for(asset.acc)
let tmp = 
 for acc = empty:seq.symbol, sym ∈ toseq.roots.oldmods do
  if not.isabstract.module.sym ∧ not.isInternal.sym then acc + Fref.sym else acc
 /for(Constant2(acc + Sequence(typeint, length.acc)))
let maybereferenced0 = close(prg10, roots.oldmods + tmp, empty:set.symbol, 0)
let symdict = symboldict(maybereferenced0, empty:seq.commoninfo)
let stacktracesym = 
 symbol(moduleref([if isempty.uses then libname else last.uses] + "impDependent")
 , "stackTraceImp"
 , seqof.typeword
 )
let bb = getSymdef(libextnames, stacktracesym)
let startaddresses = if isempty.bb then empty:seq.symbol else[stacktracesym]
let divide = 
 for addresses = startaddresses
 , other = empty:seq.symbol
 , dupsyms = empty:seq.symbol
 , sym1 ∈ toseq.maybereferenced0
 do
  let sym = clearrequiresbit.sym1
  let dup = 
   if not.isunbound.sym ∨ isabstract.module.sym then false
   else
    for acc = true, x ∈ toseq.lookupbysig(symdict, sym)while acc do isunbound.x /for(not.acc)
  if dup then next(addresses, other, dupsyms + sym)
  else if isabstract.module.sym ∨ isconst.sym ∨ isBuiltin.sym ∨ isGlobal.sym then
   next(addresses, other + sym, dupsyms)
  else next(addresses + sym, other, dupsyms)
 /for([addresses, other, dupsyms])
let dupsyms = divide_3
let other = divide_2
let addresses = divide_1
for prgX = if isempty.bb then empty:set.symdef
else asset.[symdef(stacktracesym, empty:seq.symbol, paragraphno.bb_1)]
, prgA = empty:set.symdef
, idx = 1
, sym ∈ addresses + other
do
 if not.isrecordconstant.sym ∧ isconstantorspecial.sym then next(prgX, prgA, idx)
 else
  let abstract = isabstract.module.sym
  let sd0 = 
   if isGlobal.sym then[symdef(sym, empty:seq.symbol, idx)]
   else if isInternal.sym then[symdef(sym, empty:seq.symbol, -idx)]else empty:seq.symdef
  let sd = if isempty.sd0 then toseq.getSymdef(prg10, sym)else sd0
  if isempty.sd then next(prgX, prgA, if abstract then idx else idx + 1)
  else
   let new = 
    if isGlobal.sym ∨ isInternal.sym then sd_1
    else
     let code = 
      for acc = empty:seq.symbol, sy ∈ code.sd_1 do
       let sym2 = 
        clearrequiresbit.if sy ∈ dupsyms then
         let x = lookupbysig(symdict, sy)
         if x_1 = sy then x_2 else x_1
        else sy
       acc
       + if library.module.sym2 ∈ "*"then
        let basesym = basesym.sym2
        let b = getSymdef(libextnames, basesym)
        if not.isempty.b then if isFref.sym2 then Fref.sym.b_1 else sym.b_1 else sym2
       else sym2
      /for(acc)
     if isrecordconstant.sym ∨ libname = library.module.sym ∨ abstract then symdef(sym, code, idx)
     else
      let b = getSymdef(libextnames, sym)
      if not.isempty.b then symdef(sym.b_1, empty:seq.symbol, paragraphno.b_1)
      else symdef(sym, code, -idx)
   if abstract then next(prgX, prgA + new, idx)else next(prgX + new, prgA, idx + 1)
/for(let oldmods1 = 
 for acc = empty:seq.modExports, m1 ∈ oldmods do
  for exps = empty:seq.symbol, sy ∈ exports.m1 do
   exps
   + if sy ∈ dupsyms then
    let x = lookupbysig(symdict, sy)
    if x_1 = sy then x_2 else x_1
   else sy
  /for(acc + modExports(modname.m1, exps, types.m1))
 /for(acc)
midpoint(""
, prgX
, prgA
, typedict
, oldmods1
, ["Library=" + libname + "uses=" + uses + "stacktrace="
+ [library.module.stacktracesym, name.module.stacktracesym, name.stacktracesym]
]
))

Function libcode(m:midpoint)seq.symdef
let prg = prg.m ∪ templates.m
let toexport = close(prg, roots.libmods.m, empty:set.symbol, 15)
for acc = empty:seq.symdef, sym ∈ toseq.toexport do
 if isrecordconstant.sym then acc
 else
  let sd = getSymdef(prg, sym)
  let code1 = if isempty.sd then empty:seq.symbol else code.sd_1
  let libcode = 
   if isabstract.module.sym then code1
   else
    let code = removeoptions.code1
    let optionsx = getoption.code1
    let z = 
     if length.code < 15 then
      let x = removerecordconstant(prg, code)
      if"VERYSIMPLE"_1 ∈ optionsx then x
      else
       for acc2 = true, @e ∈ x do acc2 ∧ (isconstantorspecial.@e ∨ isBuiltin.@e ∨ @e ∈ toexport)/for(if acc2 then x else empty:seq.symbol /if)
     else empty:seq.symbol
    if"COMPILETIME"_1 ∈ optionsx ∨ not.isempty.z then z + Words.optionsx + Optionsym else z
  acc + symdef(sym, libcode, if isempty.sd then 0 else paragraphno.sd_1)
/for(acc)

function removerecordconstant(p:set.symdef, s:seq.symbol)seq.symbol
for code = empty:seq.symbol, sym ∈ s do
 if not.isrecordconstant.sym then code + sym else code + removerecordconstant(p, getCode(p, sym))
/for(code) 