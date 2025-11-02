Module orderModules

use arc.modref

use graph.arc.modref

use seq.arc.modref

use set.arc.modref

use orderNodes.arc.modref

use seq1.modref

use seq1.seq.modref

use seq.seq.modref

use set.modref

use seq.set.modref

use mytype

use seq1.mytype

use set.mytype

use passsymbol

use seq1.passsymbols

use set.passsymbols

use seq1.seg

use set.seg

use sort.seg

use seq.segmap

use set.segmap

use standard

use seq1.symbol

use set.symbol

use symbol1

use seq1.symdef

use seq.symdef

use set.symdef

use sort.symdef

Export type:passsymbols

Export defines(passsymbols) set.symbol

Export modname(passsymbols) modref

Export uses(passsymbols) set.modref

Function passsymbols(modname:modref, uses:set.modref, defines:set.symbol) passsymbols
passsymbols(
 modname
 , uses
 , defines
 , empty:set.symbol
 , empty:set.symbol
 , empty:set.mytype
 , empty:seq.symdef
)

Function makeOrderSym(prg:set.symdef, allmods:set.passsymbols, libname:word) symdef
symdef(OrderSym, [Constant2(libname, orderModules(prg, allmods))], 0)

Function OrderSym symbol symbol(internalmod, "$$moduleorder", [typeint], typeint)

Function additionalarcs(nodes:set.modref, backarcs:set.arc.modref) set.arc.modref
if true then backarcs
else
 let f1 = findelement2(nodes, moduleref."* encodingsupport")
 let f2 = findelement2(nodes, moduleref."* taublockseq")
 for accM = empty:seq.modref, e ∈ toseq.findelement2(nodes, moduleref."* encoding")
 while isempty.accM
 do if %.para.e = "seq.char" then [e] else accM
 let backarcs1 = if isempty.accM ∨ isempty.f1 then backarcs else backarcs + arc(accM sub 1, f1 sub 1)
 for blockList = toseq.f2, arcs = backarcs1, e ∈ toseq.findelement2(nodes, moduleref."* seq")
 while not.isempty.blockList
 do
  if para.e = para.blockList sub 1 then next(blockList << 1, arcs + arc(e, blockList sub 1))
  else next(blockList, arcs),
 {assert isempty.f1 report":(toseq (arcs \ backarcs))"}
 arcs

function orderModules(prg0:set.symdef, allmods:set.passsymbols) seq.symbol
for modulesUsed = empty:set.modref, map = empty:seq.symbol, sd ∈ toseq.prg0
do
 let this = module.sym.sd,
 if isempty.code.sd ∨ between(kind.sym.sd, kfref, kendblock) ∨ this ∈ modulesUsed then next(modulesUsed, map)
 else next(modulesUsed + this, map + sym.sd)
let backarcs = expand(toseq.modulesUsed, allmods, false)
for nodes = empty:set.modref, e ∈ toseq.backarcs
do nodes + tail.e + head.e
let backarcs2 = additionalarcs(nodes, backarcs)
let before = orderNodes(nodes, backarcs2)
for map2 = map, e ∈ map
do
 let idx = binarysearch(toseq.modulesUsed, module.e),
 replace(map2, idx, e)
for E = empty:seq.symbol, e ∈ reverse.before
do
 if name.e ∈ "()" then
  if name.e ∈ ")" ∧ name.E sub n.E ∈ "(" then E >> 1
  else E + symbol(e, [name.e], typeint)
 else
  let idx = binarysearch(toseq.modulesUsed, e),
  if between(idx, 1, n.modulesUsed) then E + map2 sub idx else E,
E

function addscc(order:seq.modref, scc:seq.modref) seq.modref
if n.scc = 1 then order + scc
else order + moduleref."internal)" + scc + moduleref."internal ("

Export orderNodes(set.modref, set.arc.modref) seq.modref

Function expand(
used:seq.modref
, all:set.passsymbols
, allowUndefinedAbstract:boolean
) set.arc.modref
for arc3 = empty:seq.arc.modref, this ∈ used
do
 let find = lookup(all, passsymbols.this)
 let uses =
  if n.find = 1 then uses.find sub 1
  else if isSimple.this then empty:set.modref
  else
   let findA = lookup(all, passsymbols.moduleref([library.this, name.this], typeT)),
   if isempty.findA ∧ allowUndefinedAbstract then empty:set.modref
   else
    assert n.findA = 1 report "PROBLEM expand:(this):(toseq.all)"
    {replace T in abstract Module}
    for newuses = empty:set.modref, e ∈ toseq.uses.findA sub 1
    do if isAbstract.e then newuses + replaceT(para.this, e) else newuses + e,
    newuses,
 for arcs4 = arc3, tmp ∈ toseq.uses
 do
  if isSimple.tmp then arcs4 + arc(this, tmp)
  else
   let m = tomodref.para.tmp,
   arcs4 + arc(this, tmp) + arc(tmp, m),
 if isSimple.this then arcs4 else arcs4 + arc(this, tomodref.para.this),
asset.arc3

------------------

type seg is no:int, part:seq.symdef

Export type:seg

Export part(seg) seq.symdef

Export no(seg) int

function >1(a:seg, b:seg) ordering no.b >1 no.a

Function %(s:seg) seq.word
for txt = "/p", i = 1, sd ∈ part.s
do
 {assert name.sym.sd /nin" LT" report %.sym.sd+%.code.sd}
 next(txt + "/br:(no.s):(library.module.sym.sd):(options.sd):(sym.sd)", i + 1),
txt

Export >1(a:passsymbols, b:passsymbols) ordering

type segmap is modref:modref, segno:int

function >1(a:segmap, b:segmap) ordering modref.a >1 modref.b

Function tosegs(prg:set.symdef, modorder:seq.symbol) seq.seg
for map0 = empty:seq.modref, e ∈ modorder
do map0 + module.e
for map = empty:set.segmap, no = 1, ingroup = false, e ∈ map0
do
 if name.e ∈ "()" then next(map, no + 1, not.ingroup)
 else if ingroup then next(map + segmap(e, no), no, ingroup)
 else next(map + segmap(e, no), no + 1, ingroup)
let prg2 = {sort by module} sort>3.toseq.prg
for
 acc = empty:seq.seg
 , part = empty:seq.symdef
 , notfound = empty:seq.symdef
 , lastmod = module.sym.(toseq.prg) sub n.prg
 , sd ∈ prg2 + prg2 sub 1
do
 if isempty.code.sd then next(acc, part, notfound, lastmod)
 else
  let thismod = module.sym.sd,
  if thismod = lastmod then next(acc, part + sd, notfound, thismod)
  else if isempty.part then next(acc, [sd], notfound, thismod)
  else
   let find = lookup(map, segmap(lastmod, 0)),
   if isempty.find then next(acc, [sd], notfound + part, thismod)
   else next(acc + seg(segno.find sub 1, part), [sd], notfound, thismod)
let tmp = sort(acc + seg(n.map + 1, notfound))
for combine = empty:seq.seg, last = 0, e ∈ tmp
do
 if no.e = last then next(combine >> 1 + seg(no.e, part.combine sub n.combine + part.e), last)
 else next(combine + e, no.e),
combine

function >3(a:symdef, b:symdef) ordering
{order by module}
module.sym.a >1 module.sym.b ∧ n.code.a >1 n.code.b

Function check(segs:seq.seg, prg:seq.symdef, complete:set.symdef) seq.word
let prgx = asset.prg
for txt = "", acc2 = complete, s ∈ segs
do
 if isempty.part.s then next(txt, acc2)
 else
  let thismod = module.sym.(part.s) sub 1
  for txt1 = txt, acc3 = acc2, sd ∈ part.s
  do
   for txt2 = txt1, pref = false, sym ∈ code.sd
   do
    if pref then next(txt2, false)
    else if between(kind.sym, kfref, kendblock) then next(txt2, false)
    else if kind.sym = kprefref then next(txt2, true)
    else if kind.sym ∉ isOrdinary then next(txt2, false)
    else
     assert name.sym ∉ "PreFref" ∨ name.sym.sd ∈ "postbind handleBuiltin" report ":(no.s) XXX preFref:(sym):(kind.sym) IN:(sym.sd) /p:(code.sd)",
     if thismod = module.sym then next(txt2, false)
     else
      let find = getSymdef(acc3, sym),
      if n.find = 0 ∧ symdef(sym, empty:seq.symbol, 0) ∈ part.s then next(txt2, false)
      else if n.find = 1 then next(txt2, false)
      else
       let find2 = getSymdef(prgx, sym),
       if isempty.find2 ∨ NOINLINE ∈ options.find2 sub 1 then next(txt2, false)
       else
        assert %.sym ≠ "seq.word:sub (int, seq.word) word" report
         for txt22 = "", sd22 ∈ toseq.acc3 do txt22 + "/br:(sym.sd22)",
         "/br:(no.s):(sym) IN:(sym.sd) /p:(segs)",
        next(txt2 + "/br:(no.s):(sym) IN:(sym.sd)", false),
   next(txt2, acc3 + sd),
  next(txt1, acc3),
txt

Function %(e:passsymbols) seq.word "/br:(modname.e):(toseq.uses.e)"

function %%(a:seq.symdef) seq.word
for txt = "", e ∈ a do txt + "/br:(sym.e)",
txt

function open modref moduleref."internal ("

function close modref moduleref."internal)" 
