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

use symbol

use seq.symbol

use set.symbol

use symbol2

use set.symdef

Export type:sym/modref

function %(a:seq.word) seq.word a

Function exportedmodref(m:midpoint) set.sym/modref
for acc = empty:set.sym/modref, md ∈ libmods.m do
 for acc2 = acc, sym ∈ exports.md do
  acc2 + sym/modref(fixLengthSym.sym, modname.md)
 /for (acc2)
/for (acc)

type sym/modref is sym:symbol, in:modref

function >1(a:sym/modref, b:sym/modref) ordering sym.a >1 sym.b ∧ in.a >1 in.b

function >2(a:sym/modref, b:sym/modref) ordering sym.a >1 sym.b

function %(a:sym/modref) seq.word %.sym.a + %.in.a

function addtypes(exports:seq.symbol, modname:modref, prg:set.symdef) seq.symbol
let exporttypes = 
 for acc = empty:seq.mytype, sym ∈ exports do acc + types.sym + resulttype.sym /for (acc)
let usestypes = 
 for acc = exporttypes, sd ∈ toseq.prg do
  if module.sym.sd = modname then acc + types.sym.sd + resulttype.sym.sd else acc
 /for (removeseq.acc \ asset.[typereal, typeint, typeT])
for acc = empty:seq.symbol, t ∈ toseq.usestypes do
 let m2 = tomodref.t
 if m2 = modname then acc else acc + deepcopySym.t
/for (acc)

Function fixLengthSym(sym:symbol) symbol
if isBuiltin.sym ∧ name.sym = first."length" then
 symbol(moduleref("* seq", parameter.first.paratypes.sym)
  , "length"
  , paratypes.sym
  , typeint)
else
 sym

Function fixLengthSym(syms:seq.symbol) seq.symbol
for acc = empty:seq.symbol, sym ∈ syms do acc + fixLengthSym.sym /for (acc)

function lookupModule(m:midpoint, modname:word) modExports
for acc = first.libmods.m, md ∈ libmods.m do
 if name.modname.md = modname then md else acc
/for (acc)

function exports(m:midpoint, modr:modref) seq.symbol
let mr = lookupModule(m, name.modr)
if issimple.modr then
 exports.mr
else
 for acc = empty:seq.symbol, sym ∈ exports.mr do
  acc + replaceTsymbol(para.modr, sym)
 /for (acc)

Function reconstruceUses(m:midpoint, modname:word, dict:set.symbol, exported:set.sym/modref, olduses:seq.seq.word) set.modref
let md = lookupModule(m, modname)
let exports = fixLengthSym.exports.md
if isempty.exports then
 empty:set.modref
else
 {find symbols reference in defining module including type references}
 let uses5 = 
  for uses = exports, symlist = exports, sd ∈ toseq.prg.m do
   if module.sym.sd = modname.md then
    next(uses + code.sd, symlist + sym.sd)
   else
    next(uses, symlist)
  /for (asset(uses + addtypes(symlist, modname.md, prg.m)))
 {find symbols referenced in expanding templates}
 let uses6 = uses5 ∪ requires(uses5, templates.m, dict, false)
 let thismodule = 
  if isabstract.module.first.exports then
   moduleref("*" + modname, typeT)
  else
   moduleref("*" + modname)
 let include0 = 
  for acc = empty:set.symbol, sym ∈ exports do
   if module.sym = thismodule then acc + sym else acc
  /for (acc)
 for uses = [thismodule]
  , unhandled = empty:set.set.modref
  , included = include0
  , symx ∈ toseq.uses6
 do
  if isconstantorspecial.symx ∨ name.module.symx ∈ "$for" ∨ module.symx = thismodule
  ∨ isunbound.symx then
   next(uses, unhandled, included + symx)
  else
   let sym = fixLengthSym.symx
   if sym ∈ included then
    next(uses, unhandled, included)
   else
    let inmod = inModule(exported - sym/modref(sym, thismodule), sym)
    if cardinality.inmod = 1 then
     next(uses + inmod_1, unhandled, included ∪ asset.exports(m, inmod_1))
    else
     next(uses, unhandled + inmod, included)
 /for (asset.chooseUses(uses, unhandled, modname, olduses, exported) - thismodule)

function chooseUses(uses:seq.modref
 , unhandled:set.set.modref
 , modname:word
 , olduses:seq.seq.word
 , exported:set.sym/modref) seq.modref
{first make sure the parameter of the uses are included in the module}
let in = 
 for acc = empty:set.mytype, u ∈ uses do
  if issimple.u ∨ para.u ∈ [typeint, typeT] then acc else acc + para.u
 /for (for new = unhandled, t ∈ toseq.acc do new + inModule(exported, deepcopySym.t) /for (new))
{now try and resolve unhandled module sets}
for acc = empty:set.set.modref, newuses = asset.uses, u ∈ toseq.in do
 if isempty.u ∨ not.isempty(u ∩ newuses) then
  {ignore empty sets and sets with one of the modules already in uses} next(acc, newuses)
 else if cardinality.u = 1 then
  {add the single modref to uses} next(acc, newuses + u_1)
 else
  next(acc + u, newuses)
/for (
 let tmp = 
  if not.isempty.acc then
   for acc2 = empty:seq.modref, x ∈ toseq.acc_1 do
    if %.x ∈ olduses then acc2 + x else acc2
   /for (acc2)
  else
   empty:seq.modref
 if length.tmp = 1 then
  chooseUses(toseq.newuses + tmp_1, acc, modname, olduses, exported)
 else if cardinality.newuses > cardinality.asset.uses then
  chooseUses(toseq.newuses, acc, modname, olduses, exported)
 else
  {assert modname ∈" callconfig impDependent typedict compileTimeT symbol2" ∨ isempty.acc report for txt
   =" HNBH"+modname, x ∈ toseq.acc do txt+" /br $(toseq.x)" /for (txt)+" olduses"+%n.olduses}
  toseq.newuses
)

function >1(a:set.modref, b:set.modref) ordering toseq.a >1 toseq.b

function inModule(exported:set.sym/modref, sym:symbol) set.modref
let t = toseq.findelement2(exported, sym/modref(sym, internalmod))
let tmp = 
 if not.isempty.t ∨ issimple.module.sym then
  t
 else
  for acc2 = t, sm ∈ toseq.exported do
   if replaceTsymbol(para.module.sym, sym.sm) = sym then
    acc2 + sym/modref(sym, replaceT(in.sm, para.module.sym))
   else
    acc2
  /for (acc2)
for acc = empty:set.modref, e ∈ tmp do acc + in.e /for (acc)

Function requires(uses5:set.symbol, templates:set.symdef, dict:set.symbol, addtemplate:boolean) set.symbol
for acc = empty:seq.symbol, sym ∈ toseq.uses5 do
 if isconstantorspecial.sym ∨ name.module.sym ∈ "$for internal" ∨ issimple.module.sym then
  acc
 else
  for acc2 = empty:seq.symbol, sd ∈ toseq.templates do
   if replaceTsymbol(para.module.sym, sym.sd) = sym then
    if addtemplate then acc2 + sym.sd else acc2 /if + replaceT(para.module.sym, code.sd, dict)
   else
    acc2
  /for (acc + acc2)
/for (asset.acc)

function removeseq(s:seq.mytype) set.mytype
for acc = empty:set.mytype, t ∈ s do acc + removeseq.t /for (acc)

function removeseq(t:mytype) mytype if isseq.t then removeseq.parameter.t else t

Function includecomment(modtext:seq.word) int
let i = findindex(modtext, first."/p")
if subseq(modtext, i + 1, i + 1) = "*"
∨ subseq(modtext, i + 1, i + 2) ∈ ["/keyword uses"] then
 i + includecomment(modtext << i)
else if subseq(modtext, i + 1, i + 1) = "/keyword"
∧ subseq(modtext, i + 2, i + 2)
∈ ["Function", "type", "function", "Export", "unbound"
 , "Builtin", "builtin"]
∨ subseq(modtext, i + 1, i + 1) = "Export" then
 i
else
 i + includecomment(modtext << i)

function replaceT(with:mytype, a:seq.symbol, dict:set.symbol) seq.symbol
for acc = empty:seq.symbol, sym ∈ a do
 let b = replaceTsymbol(with, sym)
 let k = findelement2(dict, b)
 acc + if isempty.k then b else k_1
/for (acc) 