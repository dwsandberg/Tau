Module reconstructUses

use seq.modExports

use otherseq.modref

use otherseq.seq.modref

use set.seq.modref

use set.modref

use seq.mytype

use set.mytype

use standard

use otherseq.sym/modref

use set.sym/modref

use symbol

use seq.symbol

use set.symbol

use symbol2

use set.symdef

use otherseq.seq.word

Function exportedmodref(m:midpoint)set.sym/modref
for acc = empty:set.sym/modref, md ∈ libmods.m do
 for acc2 = acc, sym ∈ exports.md do acc2 + sym/modref(builtintoseq.sym, modname.md)/for(acc2)
/for(acc)

Export type:sym/modref

type sym/modref is sym:symbol, in:modref

function ?(a:sym/modref, b:sym/modref)ordering sym.a ? sym.b ∧ in.a ? in.b

function ?2(a:sym/modref, b:sym/modref)ordering sym.a ? sym.b

function %(a:sym/modref)seq.word %.sym.a + %.in.a

function addtypes(exports:seq.symbol, modname:modref, prg:set.symdef)seq.symbol
let exporttypes = 
 for acc = empty:seq.mytype, sym ∈ exports do acc + types.sym + resulttype.sym /for(acc)
let usestypes = 
 for acc = exporttypes, sd ∈ toseq.prg do
  if module.sym.sd = modname then acc + types.sym.sd + resulttype.sym.sd else acc
 /for(removeseq.acc \ asset.[typereal, typeint, typeT])
for acc = empty:seq.symbol, t ∈ toseq.usestypes do
 let m2 = tomodref.t
 if m2 = modname then acc else acc + deepcopySym.t
/for(acc)

Function builtintoseq(sym:symbol)symbol
if isBuiltin.sym ∧ name.sym = first."length"then
 symbol(moduleref("* seq", parameter.first.paratypes.sym)
 , "length"
 , paratypes.sym
 , typeint
 )
else sym

Function builtintoseq(syms:seq.symbol)seq.symbol
for acc = empty:seq.symbol, sym ∈ syms do acc + builtintoseq.sym /for(acc)

Function reconstruceUses(m:midpoint, modname:word, dict:set.symbol, exported:set.sym/modref, olduses:seq.seq.word)set.modref
let md = 
 for acc = first.libmods.m, md ∈ libmods.m do if name.modname.md = modname then md else acc /for(acc)
let exports = builtintoseq.exports.md
{find symbols reference in defining module including type references}
let uses5 = 
 for uses = exports, symlist = exports, sd ∈ toseq.prg.m do
  if module.sym.sd = modname.md then next(uses + code.sd, symlist + sym.sd)
  else next(uses, symlist)
 /for(asset(uses + addtypes(symlist, modname.md, prg.m)))
{find symbols referenced in expanding templates}
let uses6 = uses5 ∪ requires(uses5, templates.m, dict, false)
for acc2 = empty:set.modref, multiple = empty:seq.seq.modref, symx ∈ toseq.uses6 do
 if isconstantorspecial.symx ∨ name.module.symx ∈ "$for" ∨ module.symx = modname.md
 ∨ isunbound.symx then
  next(acc2, multiple)
 else
  let sym = builtintoseq.symx
  {assert name.module.sym /nin"builtin"/or name.sym /nin"length"/or(%.modname.md+%.paratypes.sym)/in["UTF8
    seq.byte", "format seq.word"]report"K"+print.sym+%.modname.md+%.paratypes.sym}
  let inmod = 
   for acc = empty:seq.modref, e ∈ toseq.findelement2(exported, sym/modref(sym, modname.md))do if in.e = modname.md then acc else acc + in.e /for(if name.module.sym ∈ "internal builtin"then acc else acc + module.sym /if)
  assert first."internal" ∉ %.inmod
  report"internal" + %.sym + %.inmod + " /p"
  + %.toseq.findelement2(exported, sym/modref(sym, modname.md))
  if isempty.inmod then next(acc2, multiple)
  else if length.inmod = 1 then next(acc2 + first.inmod, multiple)else next(acc2, multiple + inmod)
/for(let xxx = check(acc2, md, asset.multiple, olduses)
let hh = 
 for txt = empty:seq.seq.modref, ref2 ∈ toseq.xxx do
  if issimple.ref2 ∨ tomodref.removeseq.para.ref2 ∈ xxx then txt
  else
   let t = removeseq.para.ref2
   let d = deepcopySym.t
   if d ∈ uses5 ∨ tomodref.t = modname.md ∨ t ∈ [typeint, typeT]then txt
   else
    let inmod = 
     for acc = empty:seq.modref, e ∈ toseq.findelement2(exported, sym/modref(d, modname.md))do acc + in.e /for(acc)
    if isempty(asset.inmod ∩ xxx) ∧ not.isempty.inmod then txt + inmod else txt
 /for(txt)
let xxx2 = if length.hh = 1 ∧ length.hh_1 = 1 then xxx + hh_1_1 else xxx
for acc3 = xxx2, ref2 ∈ toseq.xxx2 do
 if name.ref2 ∈ "otherseq"then acc3 - moduleref("* seq", para.ref2)else acc3
/for(acc3))

Function requires(uses5:set.symbol, templates:set.symdef, dict:set.symbol, addtemplate:boolean)set.symbol
for acc = empty:seq.symbol, sym ∈ toseq.uses5 do
 if isconstantorspecial.sym ∨ name.module.sym ∈ "$for internal" ∨ issimple.module.sym then acc
 else
  for acc2 = empty:seq.symbol, sd ∈ toseq.templates do
   if replaceTsymbol(para.module.sym, sym.sd) = sym then
    if addtemplate then acc2 + sym.sd else acc2 /if
    + replaceT(para.module.sym, code.sd, dict)
   else acc2
  /for(acc + acc2)
/for(asset.acc)

function check(uses:set.modref, md:modExports, multiple:set.seq.modref, olduses:seq.seq.word)set.modref
let newuses = 
 for newuses = uses, e ∈ toseq.multiple do if cardinality.asset.e = 1 then newuses + first.e else newuses /for(newuses)
let ff = toseq.filter2(newuses, filter2(newuses, multiple))
{assert name.modname.md /nin"codegennew"report"HHH"+%n.toseq.ff+" /p uses"+%.toseq.newuses+%n.olduses}
for finaluses = newuses, f ∈ ff do
 if length.f = 1 then finaluses + first.f
 else
  let x = 
   for acc = empty:seq.modref, x ∈ f while isempty.acc do if %.x ∈ olduses then[x]else acc /for(acc)
  assert not.isempty.x report"JKLS" + %.modname.md + %n.ff + " /p" + %.olduses
  finaluses + first.x
/for(finaluses)

function filter2(s:set.modref, a:set.seq.modref)set.seq.modref
for acc = empty:set.seq.modref, uses = s, e ∈ toseq.a do
 let e2 = asset.e
 if cardinality.e2 = 1 then next(acc, uses + e2_1)
 else if isempty(uses ∩ e2)then next(acc + toseq.e2, uses)else next(acc, uses)
/for(for acc2 = empty:seq.modref, x ∈ toseq.acc do
 let t = uses ∩ asset.x
 if not.isempty.t then acc2 + t_1
 else for acc3 = acc2, m ∈ x do acc3 + m /for(acc3)
/for(for acc4 = acc, mr ∈ toseq(uses ∪ asset.maxcover.acc2 \ s)do acc + [mr]/for(acc4)))

function maxcover(x:seq.modref)seq.modref
if isempty.x then empty:seq.modref
else
 for oldcoverage = empty:seq.modref, current = empty:seq.modref, last = first.x, mi ∈ x do
  if last = mi then next(oldcoverage, current + mi, last)
  else
   next(if length.current > length.oldcoverage then current else oldcoverage
   , [mi]
   , mi
   )
 /for(let t = if length.current > length.oldcoverage then current else oldcoverage
 if length.t < 2 then empty:seq.modref else[first.t]/if)

function removeseq(s:seq.mytype)set.mytype for acc = empty:set.mytype, t ∈ s do acc + removeseq.t /for(acc)

function removeseq(t:mytype)mytype if isseq.t then removeseq.parameter.t else t

Function includecomment(modtext:seq.word)int
let i = findindex(first." /p", modtext)
if subseq(modtext, i + 1, i + 1) = "*"then i + includecomment(modtext << i)
else if subseq(modtext, i + 1, i + 2)
∈ [" /keyword Function", " /keyword type", " /keyword function"]
∨ subseq(modtext, i + 1, i + 1) ∈ ["Export", "unbound", "Builtin"]then
 i
else
 {assert subseq(modtext, (i+1), (i+2))/in["__", "In addition"]report"X"+subseq(modtext, (i+1), (i+2))+"L"}i
 + includecomment(modtext << i)

function replaceT(with:mytype, a:seq.symbol, dict:set.symbol)seq.symbol
for acc = empty:seq.symbol, sym ∈ a do
 let b = replaceTsymbol(with, sym)
 let k = findelement2(dict, b)
 acc + if isempty.k then b else k_1
/for(acc) 