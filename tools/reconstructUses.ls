Module reconstructUses

use seq.modExports

use otherseq.modref

use set.modref

use set.set.modref

use mytype

use seq.mytype

use set.mytype

use standard

use seq.sym/modref

use set.sym/modref

use seq.symbol

use set.symbol

use symbol2

use set.symdef

Export type:sym/modref

function %(a:seq.word) seq.word a

Function exportedmodref(m:midpoint) set.sym/modref
for acc = empty:set.sym/modref, md ∈ libmods.m
do for acc2 = acc, sym ∈ exports.md do acc2 + sym/modref(fixLengthSym.sym, modname.md), acc2,
acc

type sym/modref is sym:symbol, in:modref

function >1(a:sym/modref, b:sym/modref) ordering sym.a >1 sym.b ∧ in.a >1 in.b

function >2(a:sym/modref, b:sym/modref) ordering sym.a >1 sym.b

function %(a:sym/modref) seq.word %.sym.a + %.in.a

function addtypes(exports:seq.symbol, modname:modref, prg:set.symdef) seq.symbol
{OPTION PROFILE}
let exporttypes = for acc = empty:seq.mytype, sym ∈ exports do acc + types.sym + resulttype.sym, acc
let usestypes =
 for acc = exporttypes, sd ∈ toseq.prg
 do if module.sym.sd = modname then acc + types.sym.sd + resulttype.sym.sd else acc,
 removeseq.acc \ asset.[typereal, typeint, typeT]
for acc = empty:seq.symbol, t ∈ toseq.usestypes
do let m2 = tomodref.t, if m2 = modname then acc else acc + deepcopySym.t,
acc

Function fixLengthSym(sym:symbol) symbol
if isBuiltin.sym ∧ name.sym = 1_"length" then
symbol(moduleref("* seq", parameter.1_paratypes.sym), "length", paratypes.sym, typeint)
else sym

Function fixLengthSym(syms:seq.symbol) seq.symbol
for acc = empty:seq.symbol, sym ∈ syms do acc + fixLengthSym.sym,
acc

function lookupModule(m:midpoint, modname:word) modExports
for acc = 1_libmods.m, md ∈ libmods.m do if name.modname.md = modname then md else acc,
acc

function exports(m:midpoint, modr:modref) seq.symbol
let mr = lookupModule(m, name.modr),
if isSimple.modr then
exports.mr
else for acc = empty:seq.symbol, sym ∈ exports.mr do acc + replaceTsymbol(para.modr, sym), acc

Function reconstruceUses(
 m:midpoint
 , modname:word
 , dict:set.symbol
 , exported:set.sym/modref
 , olduses:seq.seq.word
) set.modref
let md = lookupModule(m, modname)
let exports = fixLengthSym.exports.md,
if isempty.exports then
empty:set.modref
else
 {find symbols reference in defining module including type references}
 let uses5 =
  for uses = exports, symlist = exports, sd ∈ toseq.prg.m
  do
   if module.sym.sd = modname.md then
   next(uses + code.sd, symlist + sym.sd)
   else next(uses, symlist),
  asset(uses + addtypes(symlist, modname.md, prg.m))
 {find symbols referenced in expanding templates}
 let uses6 = uses5 ∪ requires(uses5, templates.m, dict, false)
 let thismodule =
  if isAbstract.module.1_exports then
  moduleref("*" + modname, typeT)
  else moduleref("*" + modname)
 let include0 =
  for acc = empty:set.symbol, sym ∈ exports
  do if module.sym = thismodule then acc + sym else acc,
  acc
 for uses = [thismodule], unhandled = empty:set.set.modref, included = include0, symx ∈ toseq.uses6
 do
  if
   isconstantorspecial.symx
   ∨ name.module.symx ∈ "$for"
   ∨ module.symx = thismodule
   ∨ isunbound.symx
  then
  next(uses, unhandled, included + symx)
  else
   let sym = fixLengthSym.symx,
    if sym ∈ included then
    next(uses, unhandled, included)
    else
     let inmod = inModule(exported - sym/modref(sym, thismodule), sym),
      if n.inmod = 1 then
      next(uses + 1_inmod, unhandled, included ∪ asset.exports(m, 1_inmod))
      else next(uses, unhandled + inmod, included),
 asset.chooseUses(uses, unhandled, modname, olduses, exported) - thismodule

function chooseUses(
 uses:seq.modref
 , unhandled:set.set.modref
 , modname:word
 , olduses:seq.seq.word
 , exported:set.sym/modref
) seq.modref
{first make sure the parameter of the uses are included in the module}
let in =
 for acc = empty:set.mytype, u ∈ uses
 do if isSimple.u ∨ para.u ∈ [typeint, typeT] then acc else acc + para.u
 for new = unhandled, t ∈ toseq.acc do new + inModule(exported, deepcopySym.t),
 new
{now try and resolve unhandled module sets}
for acc = empty:set.set.modref, newuses = asset.uses, u ∈ toseq.in
do
 if isempty.u ∨ not.isempty(u ∩ newuses) then
 {ignore empty sets and sets with one of the modules already in uses} next(acc, newuses)
 else if n.u = 1 then
 {add the single modref to uses} next(acc, newuses + 1_u)
 else next(acc + u, newuses)
let tmp =
 if not.isempty.acc then
  for acc2 = empty:seq.modref, x ∈ toseq.1_acc do if %.x ∈ olduses then acc2 + x else acc2,
  acc2
 else empty:seq.modref,
if n.tmp = 1 then
chooseUses(toseq.newuses + 1_tmp, acc, modname, olduses, exported)
else if n.newuses > n.asset.uses then
chooseUses(toseq.newuses, acc, modname, olduses, exported)
else toseq.newuses

function >1(a:set.modref, b:set.modref) ordering toseq.a >1 toseq.b

function inModule(exported:set.sym/modref, sym:symbol) set.modref
let t = toseq.findelement2(exported, sym/modref(sym, internalmod))
let tmp =
 if not.isempty.t ∨ isSimple.module.sym then
 t
 else
  for acc2 = t, sm ∈ toseq.exported
  do
   if replaceTsymbol(para.module.sym, sym.sm) = sym then
   acc2 + sym/modref(sym, replaceT(in.sm, para.module.sym))
   else acc2,
  acc2
for acc = empty:set.modref, e ∈ tmp do acc + in.e,
acc

Function requires(
 uses5:set.symbol
 , templates:set.symdef
 , dict:set.symbol
 , addtemplate:boolean
) set.symbol
for acc = empty:seq.symbol, sym ∈ toseq.uses5
do
 if isconstantorspecial.sym ∨ name.module.sym ∈ "$FOR internal" ∨ isSimple.module.sym then
 acc
 else
  for acc2 = empty:seq.symbol, sd ∈ toseq.templates
  do
   if replaceTsymbol(para.module.sym, sym.sd) = sym then
   (if addtemplate then acc2 + sym.sd else acc2) + replaceT(para.module.sym, code.sd, dict)
   else acc2,
  acc + acc2,
asset.acc

function removeseq(s:seq.mytype) set.mytype
for acc = empty:set.mytype, t ∈ s do acc + removeseq.t,
acc

function removeseq(t:mytype) mytype if isseq.t then removeseq.parameter.t else t

Function includecomment(modtext:seq.word) int
let i = findindex(modtext, 1_"/p"),
if i > n.modtext then
i
else if
 subseq(modtext, i + 1, i + 1) = "*"
 ∨ subseq(modtext, i + 1, i + 2) ∈ ["/keyword uses"]
then
i + includecomment(modtext << i)
else if
 subseq(modtext, i + 1, i + 2)
 ∈ [
  "/keyword Function"
  , "/keyword type"
  , "/keyword function"
  , "/keyword Export"
  , "/keyword unbound"
  , "/keyword Builtin"
  , "/keyword builtin"
 ]
 ∨ subseq(modtext, i + 1, i + 1) = "Export"
then
i
else i + includecomment(modtext << i)

function replaceT(with:mytype, a:seq.symbol, dict:set.symbol) seq.symbol
for acc = empty:seq.symbol, sym ∈ a
do
 let b = replaceTsymbol(with, sym)
 let k = findelement2(dict, b),
 acc + if isempty.k then b else 1_k,
acc 