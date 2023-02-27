Module compilerfront

use symbolconstant

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

Export modExports(modname:modref, exports:seq.symbol, types:seq.seq.mytype) modExports {From symbol2}

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

function %(s:symdef) seq.word %.sym.s

use set.symbol

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
 {assert false report for acc = empty:set.symdef, sd ∈ toseq.prg10 do if library.module.sym.sd = lib
  then acc+sd else acc /do let z = (requireUnbound /cap acc), %.cardinality.z+%.cardinality.asset (
  [clearrequiresbit.sym.z_1, setrequires.sym.z_1]),}
 if option = "text" then
  for acc = empty:set.symdef, sd ∈ toseq.prg10 do
   if library.module.sym.sd = lib then acc + sd else acc
  /do
   let libmods = 
    for acc5 = empty:seq.modExports, m2 ∈ toseq.modules.t5 do
     acc5 + modExports(module.m2, toseq.exports.m2, empty:seq.seq.mytype)
    /do acc5
   ,
   midpoint5(option, acc, requireUnbound, emptytypedict, libmods, allsrc)
 else if option = "prebind" then
  midpoint(option
   , prg10
   , typedict
   , toModules(typedict, toseq.modules.t5, exports)
   , empty:seq.seq.word)
 else
  let mtmp = postbind(exports, modules.t5, prg10, typedict)
  let libmods = toModules(typedict, toseq.modules.t5, exports)
  let simple = asset.simple.t5,
  midpoint5(option
   , addExportOptions(simple, prg.mtmp, allsrc)
   , addExportOptions(simple, templates.mtmp, allsrc)
   , typedict
   , libmods
   , [first.allsrc])

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
 for acc = prg.midin ∪ templates.midin, e ∈ initprofile do
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
let libmods = libmods.midin + initprofile0
let discard = 
 for acc = empty:seq.symbol, sym ∈ toseq.roots.libmods do
  if not.isAbstract.module.sym ∧ not.isInternal.sym then acc + Fref.sym else acc
 /do Constant2(libname, acc + Sequence(typeint, length.acc))
let maybereferenced0 = close(prg10, roots.libmods, empty:set.symbol, 0)
{assert libname /nin" common" report for txt ="", sym /in toseq.maybereferenced0 do txt+"
 /br"+%.sym+library.module.sym /for (txt)}
let stacktrace0 = 
 if not.isempty.libextnames0 ∧ name.sym.first.libextnames0 ∈ "stackTraceImp" then
  asset.[starmap(baselib, first.libextnames0)]
 else
  empty:set.symdef
,
for stackTrace = stacktrace0
 , prgX = stacktrace0
 , idx = 1
 , sym ∈ toseq.maybereferenced0
do
 if not.isrecordconstant.sym ∧ isconstantorspecial.sym then
  next(stackTrace, prgX, idx)
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
   next(stackTrace, prgX, if abstract then idx else idx + 1)
  else if abstract then
   next(stackTrace, prgX + new_1, idx)
  else
   let tmp = if name.sym.new_1 ∈ "stackTraceImp" then asset.[new_1] else stackTrace,
   next(tmp, prgX + starmap(baselib, new_1), idx + 1)
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
  , typedict.midin
  , libmods.midin + initprofile
  , ["Library = $(libname) uses = $(uses) baselib = $(baselib) $(stacktrace2)"])

function showrc(s:seq.symdef) seq.word
for acc = "", sd ∈ s do
 if isrecordconstant.sym.sd then
  acc + "/br" + %.sym.sd + "code:" + %.code.sd
 else
  acc
/do acc

Function outlib(m:midpoint) midpoint
let roots = 
 for
  exports = asset.[Getfld.typeptr, Getfld.typeint, symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)]
  , md ∈ mods.m
 do
  if isAbstract.modname.md then
   for acc = exports, sy ∈ toseq.exports.md do
    acc ∪ asset(getCode(prg.m, sy) + sy)
   /do acc
  else
   exports ∪ exports.md
 /do exports
,
for acc = empty:seq.symdef, rc = empty:seq.symbol, root ∈ toseq.roots do
 if isconstantorspecial.root then
  if isrecordconstant.root then next(acc, rc + root) else next(acc, rc)
 else
  let tmp = getSymdef(prg.m, root),
  if isempty.tmp then
   next(acc, rc)
  else
   let sd = tmp_1,
   if isAbstract.module.sym.sd then
    next(acc + symdef4(sym.sd, code.sd, 0, getOptionsBits.sd), rc)
   else
    let newsymdef = 
     for includecode = length.code.sd ≤ 30, sy ∈ code.sd
     while includecode
     do
      isconstantorspecial.sy ∨ sy ∈ roots
     /do
      {???? using next of outer loop causes error}
      let newoptions = toseq(asset.getOptions.sd ∩ asset."STATE COMPILETIME NOINLINE"),
      if includecode then
       symdef4(sym.sd, code.sd, paragraphno.sd, newoptions)
      else
       symdef4(sym.sd, empty:seq.symbol, paragraphno.sd, newoptions)
    ,
    next(acc + newsymdef, rc + getrecordconst.code.sd)
/do
 let libname = extractValue(first.src.m, "Library")_1
 let exportedTypeDefs = 
  for exportedTypeDefs = empty:seq.mytype, x ∈ libmods.m do
   for acc5 = exportedTypeDefs, t ∈ types.x do acc5 + first.t /do acc5
  /do asset.exportedTypeDefs
 ,
 for typeused = empty:seq.mytype, sd0 ∈ acc do
  typeused + resulttype.sym.sd0 + types.sym.sd0
 /do
  for acc5 = empty:seq.mytype, t3 ∈ toseq.asset.typeused do
   acc5 + reduce.t3
  /do
   for moretypes = empty:seq.seq.mytype, t4 ∈ toseq(asset.acc5 \ exportedTypeDefs) do
    if library.abstractModref.t4 = libname then
     let flds = flatflds(typedict.m, t4)
     assert not.isempty.flds report "outlib problem $(t4)",
     moretypes + ([t4] + flds)
    else
     moretypes
   /do
    midpoint("X"
     , asset(acc + f45(empty:set.symbol, asset.rc, empty:seq.symdef))
     , emptytypedict
     , libmods.m + modExports(moduleref.[libname, first."?"], empty:seq.symbol, moretypes)
     , empty:seq.seq.word)

function reduce(t:mytype) seq.mytype
let a = abstracttype.t,
if a = t then [t] else reduce.parameter.t + a

use otherseq.mytype

function getrecordconst(s:seq.symbol) seq.symbol
for code = empty:seq.symbol, sym ∈ s do
 if not.isrecordconstant.sym then code else code + sym
/do code

function f45(have:set.symbol, toprocess:set.symbol, symdefs:seq.symdef) seq.symdef
for new = empty:seq.symbol, acc = symdefs, sym ∈ toseq.toprocess do
 let t = fullconstantcode.sym,
 next(new + getrecordconst.t, acc + symdef(sym, t, 0))
/do
 let k = asset.new \ have,
 if isempty.k then acc else f45(k ∪ have, k, acc)

use otherseq.symbol

function starmap(baselib:word, sd:symdef) symdef
for acc2 = empty:seq.symbol, sy ∈ code.sd do
 acc2 + clearrequiresbit.replacestar(sy, baselib)
/do
 let newsym = replacestar(sym.sd, baselib),
 if isInternal.sym.sd then
  symdef4(newsym, acc2, 2, "ThisLibrary $(getOptions.sd)")
 else
  symdef4(newsym, acc2, paragraphno.sd, getOptionsBits.sd) 