Module compilerfront

use seq.modExports

use seq1.modref

use set.modref

use mytype

use seq.mytype

use seq.seq.mytype

use set.mytype

use orderModules

use passparse

use passsymbol

use set.passsymbols

use set.passtypes

use postbind

use standard

use seq1.symbol

use seq.symbol

use seq.seq.symbol

use set.symbol

use symbol1

use seq.symdef

use set.symdef

use typedict

use seq.seq.word

use set.word

Export type:midpoint {From symbol1}

Export libmods(m:midpoint) seq.modExports {From symbol1}

Export option(midpoint) seq.word {From symbol1}

Export prg(midpoint) set.symdef {From symbol1}

Export src(midpoint) seq.seq.word {From symbol1}

Export templates(midpoint) set.symdef {From symbol1}

Export typedict(midpoint) typedict {From symbol1}

Export midpoint(
option:seq.word
, prg:set.symdef
, typedict:typedict
, libmods:seq.modExports
, src:seq.seq.word
) midpoint
{From symbol1}

Export type:modExports {From symbol1}

Export exports(modExports) seq.symbol {From symbol1}

Export modname(modExports) modref {From symbol1}

Export types(modExports) seq.seq.mytype {From symbol1}

Export modExports(modname:modref, exports:seq.symbol, types:seq.seq.mytype) modExports
{From symbol1}

Export type:typedict {From typedict}

function types(libinfo:midpoint) seq.seq.mytype
for acc = empty:seq.seq.mytype, m ∈ libmods.libinfo
do acc + types.m,
acc

function mods(mp:midpoint) seq.passsymbols
for acc = empty:seq.passsymbols, m ∈ libmods.mp
do acc + toPasssymbols.m,
acc

function toPasssymbols(a:modExports) passsymbols
passsymbols(
 modname.a
 , empty:set.modref
 , empty:set.symbol
 , asset.exports.a
 , empty:set.symbol
 , for types = empty:set.mytype, sym ∈ exports.a
 do if name.sym = "type" sub 1 then types + resulttype.sym else types,
 types
 , empty:seq.symdef
)

function %(s:symdef) seq.word %.sym.s

Function extractExports(allsrc:seq.seq.word, exportlist:seq.word) seq.word
let idx = findindex(exportlist, "/" sub 1),
if idx > n.exportlist then exportlist
else
 for inexport = false, exports2 = "", p ∈ allsrc
 do
  if isempty.p then next(inexport, exports2)
  else if p sub 1 ∈ "Module module" then next(p sub 2 ∈ exportlist << idx, exports2)
  else if inexport ∧ p sub 1 ∈ "use" then next(inexport, exports2 + p sub 2)
  else next(inexport, exports2),
 exportlist >> (n.exportlist - idx + 1) + exports2

use token

Function compilerfront3(
option:seq.word
, allsrc:seq.seq.word
, libname:word
, exports:seq.word
, libinfo:midpoint
) midpoint
{OPTION PROFILEX}
let lib = libname,
if option = "library" then midpoint(option, prg.libinfo, emptytypedict, empty:seq.modExports, empty:seq.seq.word)
else
 for libpasstypes = empty:set.passtypes, m ∈ mods.libinfo
 do
  let tmp =
   for tmp = empty:set.mytype, t ∈ types.libinfo
   do
    let mt = abstractModref.t sub 1
    let mt2 = if isAbstract.mt then replaceT(parameter.t sub 1, mt) else mt,
    if mt2 = modname.m then tmp + t sub 1 else tmp,
   tmp,
  libpasstypes + passtypes(modname.m, tmp, typedict.m)
 {figure out how to interpret text form of type}
 let discard = tknencoding
 let modsx = resolvetypes(libpasstypes, allsrc, lib)
 {figure out how to interpret text form of symbol}
 let t5 = resolvesymbols(allsrc, lib, modsx, asset.mods.libinfo)
 {parse the function bodies}
 let allmods = asset(abstract.t5 + simple.t5)
 let prga = compile(allmods, asset.abstract.t5, lib, allsrc, option = "text", empty:set.symdef)
 let typedict =
  if option = "text" then emptytypedict
  else buildtypedict(empty:set.symbol, types.t5 + types.libinfo)
 let prgb = if option = "text" then prga else prescan2(prga, typedict)
 let requireUnbound = buildrequires(prgb + toseq.code.t5 + toseq.prg.libinfo)
 let prg = compile(allmods, asset.simple.t5, lib, allsrc, option = "text", requireUnbound),
 let prg10 =
  asset(
   prgb
    + toseq.code.t5
    + toseq.prg.libinfo
    + (if option = "text" then prg else prescan2(prg, typedict))
  ),
 if option = "text" then
  for acc = empty:set.symdef, sd ∈ toseq.prg10
  do
   if library.module.sym.sd ∈ "internallib:(lib)" ∧ paragraphno.sd > 0 then
    if (allsrc sub paragraphno.sd) sub 1 ∈ "Function function Builtin builtin" then acc + sd
    else acc
   else acc
  let libmods =
   for acc5 = empty:seq.modExports, m2 ∈ toseq.modules.t5
   do acc5 + modExports(module.m2, toseq.exports.m2, empty:seq.seq.mytype),
   acc5,
  midpoint5(option, acc, requireUnbound, emptytypedict, libmods, allsrc)
 else if option = "prebind" then
  midpoint(
   option
   , prg10
   , typedict
   , toModules(typedict, toseq.modules.t5, exports)
   , empty:seq.seq.word
  )
 else
  let mtmp = postbind(exports, modules.t5, prg10, typedict)
  let libmods = toModules(typedict, toseq.modules.t5, exports)
  let simple = asset.simple.t5,
  let prg12 = addExportOptions(simple, prg.mtmp, allsrc) + makeOrderSym(prg.mtmp, allmods, libname),
  midpoint5(
   option
   , prg12
   , addExportOptions(simple, templates.mtmp, allsrc)
   , typedict
   , libmods
   , [allsrc sub 1]
  )

Function toModules(alltypes:typedict, t5:seq.passsymbols, exports:seq.word) seq.modExports
let all = "*" sub 1 ∈ exports
for acc = empty:seq.modExports, m2 ∈ t5
do
 if not.all ∧ name.module.m2 ∉ exports then acc
 else
  let d2 = if isAbstract.module.m2 then defines.m2 ∪ exports.m2 else exports.m2
  let exps =
   for acc3 = empty:seq.symbol, e ∈ toseq.d2
   do if isunbound.e then acc3 else acc3 + e,
   acc3,
  let types =
   for acc5 = empty:seq.seq.mytype, s ∈ toseq.d2
   do
    if istype.s then
     if isseq.resulttype.s then acc5 + [resulttype.s, typeint]
     else
      let c =
       for c = empty:seq.mytype, t ∈ flatflds(alltypes, resulttype.s)
       do c + if isencoding.t then typeint else t,
       c,
      acc5 + ([resulttype.s] + c)
    else acc5,
   acc5,
  acc + modExports(module.m2, exps, types),
acc

function roots(s1:seq.modExports) set.symbol
for exports = empty:seq.symbol, m ∈ s1
do exports + exports.m,
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
  if len > 0 ∧ n.code ≥ len ∧ not.isAbstract.module.sym then new
  else
   for acc = new, sym2 ∈ code
   do
    let kind = kind.sym2,
    if kind ∈ [kconstantrecord, kstacktrace] then acc + sym2
    else if kind = kfref then acc + basesym.sym2
    else if isconstantorspecial.sym2 then acc
    else if isInternal.sym2 then acc
    else acc + sym2,
   acc,
 if isempty.toexport then next(toprocess, processed, false)
 else next(asset.new, processed ∪ toprocess, true),
processed

Function prepareback(midin:midpoint, dependentlibs:midpoint, uses:seq.word) midpoint
{OPTION XPROFILE}
let libname = libname.midin
let initprofile0 =
 for acc = empty:seq.modExports, tausupport = empty:seq.modExports, x ∈ libmods.dependentlibs
 do
  if name.modname.x ∈ "initialize" then next(acc + x, tausupport)
  else if name.modname.x ∈ "tausupport" then next(acc, [x])
  else next(acc, tausupport),
 tausupport + acc
let baselib =
 if isempty.initprofile0 ∨ name.modname.initprofile0 sub 1 ∉ "tausupport" then libname
 else library.modname.initprofile0 sub 1
let initprofile =
 if isempty.initprofile0 then initprofile0
 else if name.modname.initprofile0 sub 1 ∉ "tausupport" then initprofile0 << 1
 else initprofile0
let prg10 =
 for acc = prg.midin ∪ templates.midin, e ∈ initprofile
 do
  for acc2 = acc, sy ∈ exports.e
  do acc2 ∪ getSymdef(prg.dependentlibs, sy),
  acc2,
 acc
let libextnames0 =
 for acc = empty:seq.symdef, stackTrace = empty:seq.symdef, sd ∈ toseq.prg.dependentlibs
 do
  if paragraphno.sd = 0 then next(acc, stackTrace)
  else if name.sym.sd ∈ "stackTraceImp" then next(acc + sd, [sd])
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
 if not.isempty.libextnames0 ∧ name.sym.libextnames0 sub 1 ∈ "stackTraceImp" then asset.[starmap(baselib, libextnames0 sub 1)]
 else empty:set.symdef
for stackTrace = stacktrace0, prgX = stacktrace0, idx = 1, sym ∈ toseq.maybereferenced0
do
 if kind.sym ≠ kconstantrecord ∧ isconstantorspecial.sym then next(stackTrace, prgX, idx)
 else
  let abstract = isAbstract.module.sym
  let new =
   if kind.sym = kglobal then [symdef(sym, empty:seq.symbol, idx)]
   else
    let sd = toseq.getSymdef(prg10, sym),
    if isInternal.sym then
     [
      symdef4(
       sym
       , empty:seq.symbol
       , idx
       , if isempty.sd ∨ COMPILETIME ∉ options.sd sub 1 then ThisLibrary
       else ThisLibrary + COMPILETIME
      )
     ]
    else if isempty.sd then empty:seq.symdef
    else
     let code =
      for acc = empty:seq.symbol, sym2 ∈ code.sd sub 1
      do
       acc
        + if library.module.sym2 ∈ "*" then
        let basesym = basesym.sym2
        let b = getSymdef(libextnames, basesym),
        if not.isempty.b then if kind.sym2 = kfref then Fref.sym.b sub 1 else sym.b sub 1
        else sym2
       else sym2,
      acc,
     [
      if kind.sym = kconstantrecord ∨ libname = library.module.sym ∨ abstract then symdef4(sym, code, idx, options.sd sub 1)
      else
       let b = getSymdef(libextnames, sym),
       if not.isempty.b then symdef(sym.b sub 1, empty:seq.symbol, paragraphno.b sub 1)
       else symdef4(sym, code, idx, ThisLibrary + options.sd sub 1)
     ],
  if isempty.new then next(stackTrace, prgX, if abstract then idx else idx + 1)
  else if abstract then next(stackTrace, prgX + new sub 1, idx)
  else
   let tmp = if name.sym.new sub 1 ∈ "stackTraceImp" then asset.[new sub 1] else stackTrace,
   next(tmp, prgX + starmap(baselib, new sub 1), idx + 1)
let stacktrace2 =
 if isempty.stackTrace then ""
 else "stacktrace::([library.module.sym.stackTrace sub 1, name.module.sym.stackTrace sub 1, name.sym.stackTrace sub 1])",
midpoint(
 option.midin
 , prgX
 , typedict.midin
 , libmods.midin + initprofile
 , ["uses::(uses) baselib::(baselib):(stacktrace2)"]
)

Function outlib(m:midpoint) midpoint
for
 roots = asset.[
  Getfld.typeptr
  , Getfld.typeint
  , symbol(internalmod, "GEP", [seqof.typeptr, typeint], typeptr)
 ]
 , md ∈ mods.m
do
 if isAbstract.modname.md then
  for acc = roots, sy ∈ toseq.exports.md
  do acc ∪ asset(getCode(prg.m, sy) + sy),
  acc
 else roots ∪ exports.md
for acc = empty:seq.symdef, rc = empty:seq.symbol, root ∈ toseq.roots
do
 if isconstantorspecial.root then if kind.root = kconstantrecord then next(acc, rc + root) else next(acc, rc)
 else
  let tmp = getSymdef(prg.m, root),
  if isempty.tmp then next(acc, rc)
  else
   let sd = tmp sub 1,
   if isAbstract.module.sym.sd then next(acc + symdef4(sym.sd, code.sd, 0, options.sd), rc)
   else
    let newoptions = options.sd ∩ (STATE + COMPILETIME + NOINLINE)
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
 do
  for acc5 = exportedTypeDefs, t ∈ types.x do acc5 + t sub 1,
  acc5,
 asset.exportedTypeDefs
for typeused = empty:seq.mytype, sd0 ∈ acc
do typeused + resulttype.sym.sd0 + types.sym.sd0
for acc5 = empty:seq.mytype, t3 ∈ toseq.asset.typeused
do acc5 + reduce.t3
for moretypes = empty:seq.seq.mytype, t4 ∈ toseq(asset.acc5 \ exportedTypeDefs)
do
 if library.abstractModref.t4 = libname then
  let flds = flatflds(typedict.m, t4)
  assert not.isempty.flds report "outlib problem:(t4)",
  moretypes + ([t4] + flds)
 else moretypes,
midpoint(
 "X"
 , asset(acc + f45(empty:set.symbol, asset.rc, empty:seq.symdef))
 , emptytypedict
 , libmods.m + modExports(moduleref.[libname, "?" sub 1], empty:seq.symbol, moretypes)
 , empty:seq.seq.word
)

function reduce(t:mytype) seq.mytype
let a = abstracttype.t,
if a = t then [t] else reduce.parameter.t + a

function getrecordconst(s:seq.symbol) seq.symbol
for code = empty:seq.symbol, sym ∈ s
do if kind.sym ≠ kconstantrecord then code else code + sym,
code

function f45(have:set.symbol, toprocess:set.symbol, symdefs:seq.symdef) seq.symdef
for new = empty:seq.symbol, acc = symdefs, sym ∈ toseq.toprocess
do
 let t = fullconstantcode.sym,
 next(new + getrecordconst.t, acc + symdef(sym, t, 0))
let k = asset.new \ have,
if isempty.k then acc else f45(k ∪ have, k, acc)

function starmap(baselib:word, sd:symdef) symdef
for acc2 = empty:seq.symbol, sy ∈ code.sd
do acc2 + clearrequiresbit.replacestar(sy, baselib)
let newsym = replacestar(sym.sd, baselib),
if isInternal.sym.sd then symdef4(newsym, acc2, 2, ThisLibrary + options.sd)
else symdef4(newsym, acc2, paragraphno.sd, options.sd) 
