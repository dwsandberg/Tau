Module cleanExports

use otherseq.myExport

use set.myExport

use otherseq.mytype

use standard

use symbol

use seq.symbol

use symbol2

use set.symdef

use otherseq.word

type myExport is modname:word, sym:symbol, key:seq.word, org:seq.word, paragraphno:int

function %(e:myExport) seq.word
[modname.e] + key.e + keyx.sym.e
+ if name.module.sym.e ≠ modname.e ∧ first.%.module.sym.e ∉ "builtin internal" then
 let b = "{From $(module.sym.e)}"
 if subseq(org.e, length.org.e - length.b + 1, length.org.e) = b then
  org.e
 else
  org.e + b
else
 org.e

function getExportName(s:seq.word) seq.word
if s_3 ∉ ":" then
 [s_2]
else
 for name = [s_2, s_3, s_4], last = s_4, w ∈ s << 4
 while last ∉ "("
 do
  if w ∈ "." ∨ last ∈ "." then
   next(name + w, w)
  else
   next(name, "("_1)
 /for (name)

function >2(a:myExport, b:myExport) ordering modname.a >1 modname.b

function >1(a:myExport, b:myExport) ordering
modname.a >1 modname.b ∧ key.a >1 key.b ∧ keyx.sym.a >1 keyx.sym.a
∧ %.sym.a >1 %.sym.b

function keyx(s:symbol) seq.word
if nopara.s = 1 then
 [merge.%.first.paratypes.s] + if name.s ∈ "type" then "a" else "b"
else if name.s = first.%.resulttype.s then
 [merge.%.resulttype.s] + "c"
else
 "zzzz d"

Function fix(m:midpoint) seq.word %n.toseq.manageExports.m

Function newtext(a:set.myExport, pno:int, modname:word) seq.word
let t = findelement2(a, myExport(modname, Lit.0, "", "", 0))
for acc = "", e ∈ toseq.t do
 if paragraphno.e = pno then
  if name.module.sym.e ≠ modname.e ∧ first.%.module.sym.e ∉ "builtin internal" then
   let b = "{From $(module.sym.e)}"
   if subseq(org.e, length.org.e - length.b + 1, length.org.e) = b then
    acc + org.e
   else
    acc + org.e + b
  else
   acc + org.e
 else
  acc
/for (acc)

Function newtext(a:set.myExport, modname:word) seq.word
let t = findelement2(a, myExport(modname, Lit.0, "", "", 0))
for tt = empty:seq.seq.word, ex ∈ toseq.t do
 tt + %.ex
/for (
 for tt2 = "", l ∈ alphasort.tt do
  tt2 + "/p" + l << (findindex(l, "Export"_1) - 1)
 /for (tt2)
)

Function manageExports(m:midpoint) set.myExport
for exportinfo = empty:seq.myExport
 , modname = "?"_1
 , exports = empty:seq.symbol
 , pno = 0
 , p ∈ src.m
do
 if length.p < 2 then
  next(exportinfo, modname, exports, pno + 1)
 else if first.p ∈ "Module module" then
  let newname = p_2
  let newexports = 
   for acc = empty:seq.symbol, m1 ∈ libmods.m do
    if name.modname.m1 ≠ newname then
     acc
    else
     for acc2 = acc, sym ∈ exports.m1 do
      let t = getSymdef(prg.m, sym)
      if isempty.t ∨ paragraphno.t_1 = 0 ∨ name.module.sym ≠ newname then
       acc2 + sym
      else
       acc2
     /for (acc2)
   /for (acc)
  next(exportinfo, newname, newexports, pno + 1)
 else if first.p ∈ "Export" then
  let clean = cleanexportpara.p
  let kkkl = 
   for acc5 = empty:seq.myExport, sym ∈ exports do
    if getExportName.p = fullname.sym then
     if clean = %(",", paratypes.sym) >> 1 then
      let md = %.module.sym
      acc5
      + myExport(modname, sym, if first.md = modname then "0" else md, p, pno + 1)
     else
      acc5
    else
     acc5
   /for (acc5)
  next(exportinfo + kkkl, modname, exports, pno + 1)
 else
  next(exportinfo, modname, exports, pno + 1)
/for (asset.exportinfo)

function cleanexportpara(s:seq.word) seq.word
for acc = "", last = first.s, w ∈ s << 1
while isempty.acc ∨ last.acc ∉ ")"
do
 if w ∈ "(" then
  next(acc + w, w)
 else if w ∈ ":" then
  next(acc >> 1, w)
 else if w ∈ "{" then
  next(acc + ")", w)
 else if isempty.acc then next(acc, w) else next(acc + w, w)
/for (
 if isempty.acc ∨ first.acc ∉ "(" then
  if subseq(s, 2, 3) = "type:" then getExportName.s << 2 else ""
 else
  acc << 1 >> 1
) 