Module compilerfront

use seq.modExports

use set.modref

use mytype

use otherseq.mytype

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

use otherseq.symbol

use seq.symbol

use seq.seq.symbol

use set.symbol

use symbol2

use symbolconstant

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

Export midpoint(
 option:seq.word
 , prg:set.symdef
 , typedict:typedict
 , libmods:seq.modExports
 , src:seq.seq.word
) midpoint
{From symbol2}

Export type:modExports {From symbol2}

Export exports(modExports) seq.symbol {From symbol2}

Export modname(modExports) modref {From symbol2}

Export types(modExports) seq.seq.mytype {From symbol2}

Export modExports(modname:modref, exports:seq.symbol, types:seq.seq.mytype) modExports
{From symbol2}

Export type:typedict {From typedict}

function types(libinfo:midpoint) seq.seq.mytype
for acc = empty:seq.seq.mytype, m ∈ libmods.libinfo do acc + types.m,
acc

function mods(mp:midpoint) seq.passsymbols
for acc = empty:seq.passsymbols, m ∈ libmods.mp do acc + toPasssymbols.m,
acc

function toPasssymbols(a:modExports) passsymbols
passsymbols(
 modname.a
 , empty:set.modref
 , empty:set.symbol
 , asset.exports.a
 , empty:set.symbol
 , (
  for types = empty:set.mytype, sym ∈ exports.a
  do if name.sym = 1#"type" then types + resulttype.sym else types,
  types
 )
 , empty:seq.symdef
)

function %(s:symdef) seq.word %.sym.s

Function extractExports(allsrc:seq.seq.word, exportlist:seq.word) seq.word
let idx = findindex(exportlist, 1#"/"),
if idx > n.exportlist then
exportlist
else
 for inexport = false, exports2 = "", p ∈ allsrc
 do
  if isempty.p then
  next(inexport, exports2)
  else if 1#p ∈ "Module module" then
  next(2#p ∈ exportlist << idx, exports2)
  else if inexport ∧ 1#p ∈ "use" then
  next(inexport, exports2 + 2#p)
  else next(inexport, exports2),
 exportlist >> (n.exportlist - idx + 1) + exports2

Function compilerfront3(
 option:seq.word
 , allsrc:seq.seq.word
 , libname:word
 , exports:seq.word
 , libinfo:midpoint
) midpoint
{OPTION PROFILE}
let lib = libname,
if option = "library" then
midpoint(option, prg.libinfo, emptytypedict, empty:seq.modExports, empty:seq.seq.word)
else
 let libpasstypes =
  for acc = empty:set.passtypes, m ∈ mods.libinfo
  do
   let tmp =
    for tmp = empty:set.mytype, t ∈ types.libinfo
    do
     let mt = abstractModref.1#t
     let mt2 = if isAbstract.mt then replaceT(parameter.1#t, mt) else mt,
     if mt2 = modname.m then tmp + 1#t else tmp,
    tmp,
   acc + passtypes(modname.m, tmp, typedict.m),
  acc
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
  else buildtypedict(empty:set.symbol, types.t5 + types.libinfo)
 let prgb = if option = "text" then prga else prescan2(prga, typedict)
 let requireUnbound = buildrequires(prgb + toseq.code.t5 + toseq.prg.libinfo)
 let prg = compile(allmods, asset.simple.t5, lib, allsrc, option = "text", requireUnbound)
 let prg10 = asset(
  prgb
   + toseq.code.t5
   + toseq.prg.libinfo
   + if option = "text" then prg else prescan2(prg, typedict)
 ),
  if option = "text" then
   for acc = empty:set.symdef, sd ∈ toseq.prg10
   do if library.module.sym.sd = lib then acc + sd else acc
   let libmods =
    for acc5 = empty:seq.modExports, m2 ∈ toseq.modules.t5
    do acc5 + modExports(module.m2, toseq.exports.m2, empty:seq.seq.mytype),
    acc5,
   midpoint5(option, acc, requireUnbound, emptytypedict, libmods, allsrc)
  else if option = "prebind" then
  midpoint(option, prg10, typedict, toModules(typedict, toseq.modules.t5, exports), empty:seq.seq.word)
  else
   let mtmp = postbind(exports, modules.t5, prg10, typedict)
   let libmods = toModules(typedict, toseq.modules.t5, exports)
   let simple = asset.simple.t5,
   midpoint5(
    option
    , addExportOptions(simple, prg.mtmp, allsrc)
    , addExportOptions(simple, templates.mtmp, allsrc)
    , typedict
    , libmods
    , [1#allsrc]
   )

Function toModules(alltypes:typedict, t5:seq.passsymbols, exports:seq.word) seq.modExports
for acc = empty:seq.modExports, m2 ∈ t5
do
 if name.module.m2 ∉ exports then
 acc
 else
  let d2 = if isAbstract.module.m2 then defines.m2 ∪ exports.m2 else exports.m2
  let exps = for acc3 = empty:seq.symbol, e ∈ toseq.d2 do if isunbound.e then acc3 else acc3 + e, acc3
  let types =
   for acc5 = empty:seq.seq.mytype, s ∈ toseq.d2
   do
    if istype.s then
     if isseq.resulttype.s then
     acc5 + [resulttype.s, typeint]
     else
      let c =
       for c = empty:seq.mytype, t ∈ flatflds(alltypes, resulttype.s)
       do c + if isencoding.t ∨ t = typechar then typeint else t,
       c,
      acc5 + ([resulttype.s] + c)
    else acc5,
   acc5,
  acc + modExports(module.m2, exps, types),
acc

function roots(s1:seq.modExports) set.symbol
for exports = empty:seq.symbol, m ∈ s1 do exports + exports.m,
asset.exports

function close(
 prg:set.symdef
 , toprocessin:set.symbol
 , processedin:set.symbol
 , len:int
) set.symbol
for toprocess = toprocessin, processed = processedin, continue = true
while continue
do
 let toexport = toprocess \ processed
 for new = empty:seq.symbol, sym ∈ toseq.toexport
 do
  let code = getCode(prg, sym),
   if len > 0 ∧ n.code ≥ len ∧ not.isAbstract.module.sym then
   new
   else
    for acc = new, sym2 ∈ code
    do
     if isrecordconstant.sym2 then
     acc + sym2
     else if isFref.sym2 then
     acc + basesym.sym2
     else if isconstantorspecial.sym2 then
     acc
     else if name.module.sym2 ∈ "internal" then
     if name.sym2 ∈ "stacktrace" then acc + sym2 else acc
     else if name.module.sym2 ∈ "builtin $for" then
     acc
     else acc + sym2,
    acc,
  if isempty.toexport then
  next(toprocess, processed, false)
  else next(asset.new, processed ∪ toprocess, true),
processed

Function prepareback(midin:midpoint, dependentlibs:midpoint) midpoint
{OPTION XPROFILE}
let uses = extractValue(1#src.midin, "uses")
let libname = libname.midin
let initprofile0 =
 for acc = empty:seq.modExports, tausupport = empty:seq.modExports, x ∈ libmods.dependentlibs
 do
  if name.modname.x ∈ "initialize" then
  next(acc + x, tausupport)
  else if name.modname.x ∈ "tausupport" then
  next(acc, [x])
  else next(acc, tausupport),
 tausupport + acc
let baselib =
 if isempty.initprofile0 ∨ name.modname.1#initprofile0 ∉ "tausupport" then
 libname
 else library.modname.1#initprofile0
let initprofile =
 if isempty.initprofile0 then
 initprofile0
 else if name.modname.1#initprofile0 ∉ "tausupport" then
 initprofile0 << 1
 else initprofile0
let prg10 =
 for acc = prg.midin ∪ templates.midin, e ∈ initprofile
 do for acc2 = acc, sy ∈ exports.e do acc2 ∪ getSymdef(prg.dependentlibs, sy), acc2,
 acc
let libextnames0 =
 for acc = empty:seq.symdef, stackTrace = empty:seq.symdef, sd ∈ toseq.prg.dependentlibs
 do
  if paragraphno.sd = 0 then
  next(acc, stackTrace)
  else if name.sym.sd ∈ "stackTraceImp" then
  next(acc + sd, [sd])
  else next(acc + sd, stackTrace),
 stackTrace + acc
let libextnames = asset.libextnames0
let libmods = libmods.midin + initprofile0
let discard =
 for acc = empty:seq.symbol, sym ∈ toseq.roots.libmods
 do if not.isAbstract.module.sym ∧ not.isInternal.sym then acc + Fref.sym else acc,
 Constant2(libname, acc + Sequence(typeint, n.acc))
let maybereferenced0 = close(prg10, roots.libmods, empty:set.symbol, 0)
let stacktrace0 =
 if not.isempty.libextnames0 ∧ name.sym.1#libextnames0 ∈ "stackTraceImp" then
 asset.[starmap(baselib, 1#libextnames0)]
 else empty:set.symdef
for stackTrace = stacktrace0, prgX = stacktrace0, idx = 1, sym ∈ toseq.maybereferenced0
do
 if not.isrecordconstant.sym ∧ isconstantorspecial.sym then
 next(stackTrace, prgX, idx)
 else
  let abstract = isAbstract.module.sym
  let new =
   if isGlobal.sym then
   [symdef(sym, empty:seq.symbol, idx)]
   else
    let sd = toseq.getSymdef(prg10, sym),
     if isInternal.sym then
     [symdef4(
      sym
      , empty:seq.symbol
      , idx
      , if isempty.sd ∨ 1#"COMPILETIME" ∉ getOptions.1#sd then
       "ThisLibrary"
       else "ThisLibrary COMPILETIME"
     )]
     else if isempty.sd then
     empty:seq.symdef
     else
      let code =
       for acc = empty:seq.symbol, sym2 ∈ code.1#sd
       do
        acc
         + 
         if library.module.sym2 ∈ "*" then
          let basesym = basesym.sym2
          let b = getSymdef(libextnames, basesym),
          if not.isempty.b then if isFref.sym2 then Fref.sym.1#b else sym.1#b else sym2
         else sym2,
       acc,
      [
       if isrecordconstant.sym ∨ libname = library.module.sym ∨ abstract then
       symdef4(sym, code, idx, getOptionsBits.1#sd)
       else
        let b = getSymdef(libextnames, sym),
         if not.isempty.b then
         symdef(sym.1#b, empty:seq.symbol, paragraphno.1#b)
         else symdef4(sym, code, idx, "ThisLibrary^(getOptions.1#sd)")
      ],
   if isempty.new then
   next(stackTrace, prgX, if abstract then idx else idx + 1)
   else if abstract then
   next(stackTrace, prgX + 1#new, idx)
   else
    let tmp = if name.sym.1#new ∈ "stackTraceImp" then asset.[1#new] else stackTrace,
    next(tmp, prgX + starmap(baselib, 1#new), idx + 1)
let stacktrace2 =
 if isempty.stackTrace then
 ""
 else "stacktrace =
 ^([library.module.sym.1#stackTrace, name.module.sym.1#stackTrace, name.sym.1#stackTrace])",
midpoint(
 option.midin
 , prgX
 , typedict.midin
 , libmods.midin + initprofile
 , ["Library =^(libname) uses =^(uses) baselib =^(baselib)^(stacktrace2)"]
)

function showrc(s:seq.symdef) seq.word
for acc = "", sd ∈ s
do
 if isrecordconstant.sym.sd then
 acc + "/br" + %.sym.sd + "code:" + %.code.sd
 else acc,
acc

Function outlib(m:midpoint) midpoint
for
 roots = asset.[Getfld.typeptr, Getfld.typeint, symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)]
 , md ∈ mods.m
do
 if isAbstract.modname.md then
 for acc = roots, sy ∈ toseq.exports.md do acc ∪ asset(getCode(prg.m, sy) + sy), acc
 else roots ∪ exports.md
for acc = empty:seq.symdef, rc = empty:seq.symbol, root ∈ toseq.roots
do
 if isconstantorspecial.root then
 if isrecordconstant.root then next(acc, rc + root) else next(acc, rc)
 else
  let tmp = getSymdef(prg.m, root),
   if isempty.tmp then
   next(acc, rc)
   else
    let sd = 1#tmp,
     if isAbstract.module.sym.sd then
     next(acc + symdef4(sym.sd, code.sd, 0, getOptionsBits.sd), rc)
     else
      let newoptions = toseq(asset.getOptions.sd ∩ asset."STATE COMPILETIME NOINLINE")
      for includecode = n.code.sd ≤ 30, sy ∈ code.sd
      while includecode
      do isconstantorspecial.sy ∨ sy ∈ roots,
      next(
       acc
        + symdef4(sym.sd, if includecode then code.sd else empty:seq.symbol, paragraphno.sd, newoptions)
       , rc + getrecordconst.code.sd
      )
let libname = libname.m
let exportedTypeDefs =
 for exportedTypeDefs = empty:seq.mytype, x ∈ libmods.m
 do for acc5 = exportedTypeDefs, t ∈ types.x do acc5 + 1#t, acc5,
 asset.exportedTypeDefs
for typeused = empty:seq.mytype, sd0 ∈ acc do typeused + resulttype.sym.sd0 + types.sym.sd0
for acc5 = empty:seq.mytype, t3 ∈ toseq.asset.typeused do acc5 + reduce.t3
for moretypes = empty:seq.seq.mytype, t4 ∈ toseq(asset.acc5 \ exportedTypeDefs)
do
 if library.abstractModref.t4 = libname then
  let flds = flatflds(typedict.m, t4)
  assert not.isempty.flds report "outlib problem^(t4)",
  moretypes + ([t4] + flds)
 else moretypes,
midpoint(
 "X"
 , asset(acc + f45(empty:set.symbol, asset.rc, empty:seq.symdef))
 , emptytypedict
 , libmods.m + modExports(moduleref.[libname, 1#"?"], empty:seq.symbol, moretypes)
 , empty:seq.seq.word
)

function reduce(t:mytype) seq.mytype
let a = abstracttype.t,
if a = t then [t] else reduce.parameter.t + a

function getrecordconst(s:seq.symbol) seq.symbol
for code = empty:seq.symbol, sym ∈ s do if not.isrecordconstant.sym then code else code + sym,
code

function f45(have:set.symbol, toprocess:set.symbol, symdefs:seq.symdef) seq.symdef
for new = empty:seq.symbol, acc = symdefs, sym ∈ toseq.toprocess
do let t = fullconstantcode.sym, next(new + getrecordconst.t, acc + symdef(sym, t, 0))
let k = asset.new \ have,
if isempty.k then acc else f45(k ∪ have, k, acc)

function starmap(baselib:word, sd:symdef) symdef
for acc2 = empty:seq.symbol, sy ∈ code.sd do acc2 + clearrequiresbit.replacestar(sy, baselib)
let newsym = replacestar(sym.sd, baselib),
if isInternal.sym.sd then
symdef4(newsym, acc2, 2, "ThisLibrary^(getOptions.sd)")
else symdef4(newsym, acc2, paragraphno.sd, getOptionsBits.sd) 