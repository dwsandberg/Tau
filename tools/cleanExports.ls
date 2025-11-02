Module cleanExports

/use seq1.myExport

use set.myExport

use seq1.mytype

use pretty

use standard

use seq.symbol

use symbol1

use set.symdef

use sort.seq.word

use seq1.word

use sort.word

Export type:myExport

type myExport is modname:word, sym:symbol, key:seq.word, org:seq.word, paragraphno:int

function %(e:myExport) seq.word
[modname.e]
 + key.e
 + keyx.sym.e
 + if name.module.sym.e ≠ modname.e ∧ (%.module.sym.e) sub 1 ∉ "builtin internal" then
 let b = "{From:(module.sym.e)}",
 if subseq(org.e, n.org.e - n.b + 1, n.org.e) = b then org.e else org.e + b
else org.e

function getExportName(s:seq.word) seq.word
if s sub 3 ∉ ":" then [s sub 2]
else
 for name = [s sub 2, s sub 3, s sub 4], last = s sub 4, w ∈ s << 4
 while last ∉ "("
 do if w ∈ "." ∨ last ∈ "." then next(name + w, w) else next(name, "(" sub 1),
 name

function >2(a:myExport, b:myExport) ordering modname.a >1 modname.b

function >1(a:myExport, b:myExport) ordering
modname.a >1 modname.b ∧ key.a >1 key.b ∧ keyx.sym.a >1 keyx.sym.a ∧ %.sym.a >1 %.sym.b

function keyx(s:symbol) seq.word
if nopara.s = 1 then [merge.%.(paratypes.s) sub 1] + (if name.s ∈ "type" then "a" else "b")
else if name.s = (%.resulttype.s) sub 1 then [merge.%.resulttype.s] + "c"
else "zzzz d"

Function newtext(a:set.myExport, pno:int, modname:word) seq.word
let t = findelement2(a, myExport(modname, Lit.0, "", "", 0))
for acc = "", e ∈ toseq.t
do
 if paragraphno.e = pno then
  if name.module.sym.e ≠ modname.e ∧ (%.module.sym.e) sub 1 ∉ "builtin internal" then
   let b = "{From:(module.sym.e)}",
   if subseq(org.e, n.org.e - n.b + 1, n.org.e) = b then acc + org.e
   else acc + org.e + b
  else acc + org.e
 else acc,
acc

Function newtext(a:set.myExport, modname:word) seq.word
let t = findelement2(a, myExport(modname, Lit.0, "", "", 0))
for tt = empty:seq.seq.word, ex ∈ toseq.t do tt + %.ex
for tt2 = "", l ∈ sort>alpha.tt
do tt2 + "/p" + pretty(l << (findindex(l, "Export" sub 1) - 1)),
tt2

Function manageExports(m:midpoint) set.myExport
for
 exportinfo = empty:seq.myExport
 , modname = "?" sub 1
 , exports = empty:seq.symbol
 , pno = 0
 , p ∈ src.m
do
 if n.p < 2 then next(exportinfo, modname, exports, pno + 1)
 else if p sub 1 ∈ "Module module" then
  let newname = p sub 2
  let newexports =
   for acc = empty:seq.symbol, m1 ∈ libmods.m
   do
    if name.modname.m1 ≠ newname then acc
    else
     for acc2 = acc, sym ∈ exports.m1
     do
      let t = getSymdef(prg.m, sym),
      if isempty.t ∨ paragraphno.t sub 1 = 0 ∨ name.module.sym ≠ newname then acc2 + sym
      else acc2,
     acc2,
   acc,
  next(exportinfo, newname, newexports, pno + 1)
 else if p sub 1 ∈ "Export" then
  let clean = cleanexportpara.p
  let kkkl =
   for acc5 = empty:seq.myExport, sym ∈ exports
   do
    if getExportName.p = fullname.sym then
     if clean = %(",", paratypes.sym) >> 1 then
      let md = %.module.sym,
      acc5 + myExport(modname, sym, if md sub 1 = modname then "0" else md, p, pno + 1)
     else acc5
    else acc5,
   acc5,
  next(exportinfo + kkkl, modname, exports, pno + 1)
 else next(exportinfo, modname, exports, pno + 1),
asset.exportinfo

function cleanexportpara(s:seq.word) seq.word
for acc = "", last = s sub 1, w ∈ s << 1
while isempty.acc ∨ acc sub n.acc ∉ ")"
do
 if w ∈ "(" then next(acc + w, w)
 else if w ∈ ":" then next(acc >> 1, w)
 else if w ∈ "{" then next(acc + ")", w)
 else if isempty.acc then next(acc, w)
 else next(acc + w, w),
if isempty.acc ∨ acc sub 1 ∉ "(" then if subseq(s, 2, 3) = "type:" then getExportName.s << 2 else ""
else acc << 1 >> 1 
