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

use otherseq.symdef

use seq.symdef

use set.symdef

use typedict

use seq.seq.word

use set.word

Export type:midpoint {From symbol2}

Export libmods(m:midpoint) seq.modExports {From symbol2}

Export option(midpoint) seq.word {From symbol2}

Export prg(midpoint) set.symdef {From symbol2}

Export src(midpoint) seq.seq.word {From symbol2}

Export templates(midpoint) set.symdef {From symbol2}

Export typedict(midpoint) typedict {From symbol2}

Export midpoint(option:seq.word
 , prg:set.symdef
 , typedict:typedict
 , libmods:seq.modExports
 , src:seq.seq.word) midpoint
{From symbol2}

Export type:modExports {From symbol2}

Export exports(modExports) seq.symbol {From symbol2}

Export modname(modExports) modref {From symbol2}

Export types(modExports) seq.seq.mytype {From symbol2}

Export modExports(modname:modref, exports:seq.symbol, types:seq.seq.mytype) modExports
{From symbol2}

Export type:typedict {From typedict}

function types(libinfo:midpoint) seq.seq.mytype
for acc = empty:seq.seq.mytype, m ∈ libmods.libinfo do acc + types.m /do acc

function mods(mp:midpoint) seq.passsymbols
for acc = empty:seq.passsymbols, m ∈ libmods.mp do acc + toPasssymbols.m /do acc

function toPasssymbols(a:modExports) passsymbols
passsymbols(modname.a
 , empty:set.modref
 , empty:set.symbol
 , asset.exports.a
 , empty:set.symbol
 , for types = empty:set.mytype, sym ∈ exports.a do
  if name.sym = "type"_1 then types + resulttype.sym else types
 /do types
 , empty:seq.symdef)

Function compilerfront3(option:seq.word, allsrc:seq.seq.word, libinfo:midpoint) midpoint
assert not.isempty.allsrc report "empty source"
let lib0 = extractValue(first.allsrc, "Library library")
assert not.isempty.lib0 report "no library specified"
let lib = first.lib0
let exports = extractValue(first.allsrc, "exports")
let modules = 
 for txt = empty:set.word, p ∈ allsrc do
  if length.p > 1 ∧ first.p ∈ "Module module" then txt + p_2 else txt
 /do txt
assert isempty.toseq(asset.exports \ (modules + merge([lib] + "$EP")))
report
 "Export clause of library $(lib) contain unknown module (s)
  $(toseq(asset.exports \ modules))"
,
if option = "library" then
 midpoint(option, prg.libinfo, emptytypedict, empty:seq.modExports, empty:seq.seq.word)
else
 let libpasstypes = 
  for acc = empty:set.passtypes, m ∈ mods.libinfo do
   let tmp = 
    for tmp = empty:set.mytype, t ∈ types.libinfo do
     let mt = abstractModref.first.t
     let mt2 = if isAbstract.mt then replaceT(parameter.first.t, mt) else mt,
     if mt2 = modname.m then tmp + first.t else tmp
    /do tmp
   ,
   acc + passtypes(modname.m, tmp, typedict.m)
  /do acc
 {figure out how to interpret text form of type}
 let modsx = resolvetypes(libpasstypes, allsrc, lib)
 {figure out how to interpret text form of symbol}
 let t5 = resolvesymbols(allsrc, lib, modsx, asset.mods.libinfo)
 {parse the function bodies}
 let allmods = asset(abstract.t5 + simple.t5)
 let prga = compile(allmods, asset.abstract.t5, lib, allsrc, option = "text", empty:set.symdef)
 let typedict = 
  if option = "text" then
   emptytypedict
  else
   buildtypedict(empty:set.symbol, types.t5 + types.libinfo)
 let prgb = if option = "text" then prga else prescan2(prga, typedict)
 let requireUnbound = buildrequires(prgb + toseq.code.t5 + toseq.prg.libinfo)
 let prg = compile(allmods, asset.simple.t5, lib, allsrc, option = "text", requireUnbound)
 let prg10 = 
  asset(prgb + toseq.code.t5 + toseq.prg.libinfo
  + if option = "text" then prg else prescan2(prg, typedict) /if)
 ,
 if option = "text" then
  for acc = empty:set.symdef, sd ∈ toseq.prg10 do
   if library.module.sym.sd = lib then acc + sd else acc
  /do
   let libmods = 
    for acc5 = empty:seq.modExports, m2 ∈ toseq.modules.t5 do
     acc5 + modExports(module.m2, toseq.exports.m2, empty:seq.seq.mytype)
    /do acc5
   ,
   midpoint(option, acc, requireUnbound, emptytypedict, {empty:seq.modExports} libmods, allsrc)
 else
  let roots = 
   for acc = [outofboundssymbol], f ∈ toseq.modules.t5 do
    if name.module.f ∉ exports then
     acc
    else if isSimple.module.f then
     acc + toseq.exports.f
    else
     for acc2 = empty:seq.symbol, sym ∈ toseq.defines.f do
      acc2 + getCode(prg10, sym)
     /do
      for acc3 = acc, sym2 ∈ toseq.asset.acc2 do
       if isAbstract.module.sym2 ∨ isconstantorspecial.sym2 ∨ isBuiltin.sym2 ∨ inModFor.sym2 then
        acc3
       else
        acc3 + sym2
      /do acc3
   /do acc
  let templates = 
   for acc = empty:seq.symdef, p ∈ toseq.prg10 do
    if para.module.sym.p = typeT then acc + p else acc
   /do asset.acc
  ,
  if option = "prebind" then
   midpoint(option
    , prg10
    , typedict
    , toModules(typedict, toseq.modules.t5, exports)
    , empty:seq.seq.word)
  else
   let pb = postbind(roots, prg10, templates, typedict)
   let afteroption = addExportOptions(asset.simple.t5, prg.pb, allsrc)
   let libmods = toModules(typedict, toseq.modules.t5, exports),
   if option = "pass1" then
    midpoint(option, afteroption, typedict.pb, libmods, empty:seq.seq.word)
   else
    midpoint(option, afteroption, templates, typedict, libmods, [first.allsrc])

Function toModules(alltypes:typedict, t5:seq.passsymbols, exports:seq.word) seq.modExports
for acc = empty:seq.modExports, m2 ∈ t5 do
 if name.module.m2 ∉ exports then
  acc
 else
  let d2 = if isAbstract.module.m2 then defines.m2 ∪ exports.m2 else exports.m2
  let exps = 
   for acc3 = empty:seq.symbol, e ∈ toseq.d2 do
    if isunbound.e then acc3 else acc3 + e
   /do acc3
  let types = 
   for acc5 = empty:seq.seq.mytype, s ∈ toseq.d2 do
    if istype.s then
     if isseq.resulttype.s then
      acc5 + [resulttype.s, typeint]
     else
      let c = 
       for c = empty:seq.mytype, t ∈ flatflds(alltypes, resulttype.s) do
        c + if isencoding.t ∨ t = typechar then typeint else t
       /do c
      ,
      acc5 + ([resulttype.s] + c)
    else
     acc5
   /do acc5
  ,
  acc + modExports(module.m2, exps, types)
/do acc

function roots(s1:seq.modExports) set.symbol
for exports = empty:seq.symbol, m ∈ s1 do exports + exports.m /do asset.exports

function close(prg:set.symdef, toprocess:set.symbol, processed:set.symbol, len:int) set.symbol
let toexport = toprocess \ processed,
for new = empty:seq.symbol, sym ∈ toseq.toexport do
 let code = getCode(prg, sym),
 if len > 0 ∧ length.code ≥ len ∧ not.isAbstract.module.sym then
  new
 else
  for acc = new, sym2 ∈ code do
   if isrecordconstant.sym2 then
    acc + sym2
   else if isFref.sym2 then
    acc + basesym.sym2
   else if isconstantorspecial.sym2 then
    acc
   else if name.module.sym2 ∈ "internal" then
    if name.sym2 ∈ "stacktrace" then acc + sym2 else acc
   else if name.module.sym2 ∈ "builtin $for" then acc else acc + sym2
  /do acc
/do if isempty.toexport then processed else close(prg, asset.new, processed ∪ toprocess, len)

Function prepareback(midin:midpoint, dependentlibs:midpoint) midpoint
{OPTION XPROFILE}
let uses = extractValue(first.src.midin, "uses")
let libname = first.extractValue(first.src.midin, "Library")
let initprofile0 = 
 for acc = empty:seq.modExports
  , tausupport = empty:seq.modExports
  , x ∈ libmods.dependentlibs
 do
  if name.modname.x ∈ "initialize" then
   next(acc + x, tausupport)
  else if name.modname.x ∈ "tausupport" then next(acc, [x]) else next(acc, tausupport)
 /do tausupport + acc
let baselib = 
 if isempty.initprofile0 ∨ name.modname.first.initprofile0 ∉ "tausupport" then
  libname
 else
  library.modname.first.initprofile0
let initprofile = 
 if isempty.initprofile0 then
  initprofile0
 else if name.modname.first.initprofile0 ∉ "tausupport" then initprofile0 << 1 else initprofile0
let prg10 = 
 for acc = prg.midin, e ∈ initprofile do
  for acc2 = acc, sy ∈ exports.e do acc2 ∪ getSymdef(prg.dependentlibs, sy) /do acc2
 /do acc
let libextnames0 = 
 for acc = empty:seq.symdef
  , stackTrace = empty:seq.symdef
  , sd ∈ toseq.prg.dependentlibs
 do
  if paragraphno.sd = 0 then
   next(acc, stackTrace)
  else if name.sym.sd ∈ "stackTraceImp" then
   next(acc + sd, [sd])
  else
   next(acc + sd, stackTrace)
 /do stackTrace + acc
let libextnames = asset.libextnames0
let maybereferenced0 = close(prg.midin ∪ templates.midin, libmods.midin + initprofile0)
{assert libname /nin" common" report for txt ="", sym /in toseq.maybereferenced0 do txt+"
 /br"+%.sym+library.module.sym /for (txt)}
let stacktrace0 = 
 if not.isempty.libextnames0 ∧ name.sym.first.libextnames0 ∈ "stackTraceImp" then
  asset.[first.libextnames0]
 else
  empty:set.symdef
,
for stackTrace = stacktrace0
 , prgX = stacktrace0
 , prgA = empty:set.symdef
 , idx = 1
 , sym ∈ toseq.maybereferenced0
do
 if not.isrecordconstant.sym ∧ isconstantorspecial.sym then
  next(stackTrace, prgX, prgA, idx)
 else
  let abstract = isAbstract.module.sym
  let new = 
   if isGlobal.sym then
    [symdef(sym, empty:seq.symbol, idx)]
   else if isInternal.sym then
    [symdef4(sym, empty:seq.symbol, idx, "ThisLibrary")]
   else
    let sd = toseq.getSymdef(prg10, sym),
    if isempty.sd then
     empty:seq.symdef
    else
     let code = 
      for acc = empty:seq.symbol, sym2 ∈ code.sd_1 do
       acc
       + if library.module.sym2 ∈ "*" then
        let basesym = basesym.sym2
        let b = getSymdef(libextnames, basesym),
        if not.isempty.b then if isFref.sym2 then Fref.sym.b_1 else sym.b_1 else sym2
       else
        sym2
      /do acc
     ,
     [
      if isrecordconstant.sym ∨ libname = library.module.sym ∨ abstract then
       symdef4(sym, code, idx, getOptionsBits.sd_1)
      else
       let b = getSymdef(libextnames, sym),
       if not.isempty.b then
        symdef(sym.b_1, empty:seq.symbol, paragraphno.b_1)
       else
        symdef4(sym, code, idx, "ThisLibrary $(getOptions.sd_1)")
      ]
  ,
  if isempty.new then
   next(stackTrace, prgX, prgA, if abstract then idx else idx + 1)
  else if abstract then
   next(stackTrace, prgX, prgA + new_1, idx)
  else
   let tmp = if name.sym.new_1 ∈ "stackTraceImp" then asset.[new_1] else stackTrace,
   next(tmp, prgX + new_1, prgA, idx + 1)
/do
 {let oldmods1 = for acc = empty:seq.modExports, m1 ∈ oldmods do for exps = empty:seq.symbol, sy
  ∈ exports.m1 do exps+sy /for (acc+modExports (modname.m1, exps, types.m1)) /for (acc)}
 let stacktrace2 = 
  if isempty.stackTrace then
   ""
  else
   "stacktrace =
    $([library.module.sym.stackTrace_1, name.module.sym.stackTrace_1, name.sym.stackTrace_1])
    "
 ,
 midpoint(option.midin
  , prgX
  , prgA
  , typedict.midin
  , libmods.midin + initprofile
  , ["Library = $(libname) uses = $(uses) baselib = $(baselib) $(stacktrace2)"])

function close(prg:set.symdef, libmods:seq.modExports) set.symbol
let tmp = 
 for acc = empty:seq.symbol, sym ∈ toseq.roots.libmods do
  if not.isAbstract.module.sym ∧ not.isInternal.sym then acc + Fref.sym else acc
 /do Constant2(acc + Sequence(typeint, length.acc))
,
close(prg, roots.libmods, empty:set.symbol, 0)

Function outlib(m:midpoint) midpoint
let prg = prg.m ∪ templates.m,
for acc = empty:seq.symdef, sd ∈ toseq.prg do
 if isrecordconstant.sym.sd then
  acc
 else if isAbstract.module.sym.sd then
  acc + symdef4(sym.sd, removeFref.code.sd, 0, getOptionsBits.sd)
 else if length.code.sd > 30 then
  acc + symdef4(sym.sd, empty:seq.symbol, paragraphno.sd, getOptionsBits.sd)
 else
  let code = removeFref.removerecordconstant(prg, code.sd),
  acc + symdef4(sym.sd, code, paragraphno.sd, getOptionsBits.sd)
/do midpoint("X", asset.acc, empty:set.symdef, emptytypedict, libmods.m, empty:seq.seq.word)

function removerecordconstant(p:set.symdef, s:seq.symbol) seq.symbol
for code = empty:seq.symbol, sym ∈ s do
 if not.isrecordconstant.sym then
  code + sym
 else
  code + removerecordconstant(p, getCode(p, sym))
/do code

function removeFref(code:seq.symbol) seq.symbol
for codeNoFref = empty:seq.symbol, sy ∈ code do
 if isFref.sy then codeNoFref + PreFref + basesym.sy else codeNoFref + sy
/do codeNoFref

Function starmap(m:midpoint) midpoint
let baselib = first.extractValue(first.src.m, "baselib"),
for acc = empty:set.symdef, sd ∈ toseq.prg.m do
 for acc2 = empty:seq.symbol, sy ∈ code.sd do
  acc2 + clearrequiresbit.replacestar(sy, baselib)
 /do
  let newsym = replacestar(sym.sd, baselib),
  acc
  + if isInternal.sym.sd then
   symdef4(newsym, acc2, 2, "ThisLibrary $(getOptions.sd)")
  else
   symdef4(newsym, acc2, paragraphno.sd, getOptionsBits.sd)
/do midpoint(option.m, acc, templates.m, typedict.m, libmods.m, src.m) 