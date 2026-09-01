Module prettycompilerfront

This is a comment

This is a second /eol
comment on two lines

/use cleanExports

/use set.myExport

use PEG

use autolink

use seq1.autolink

use set.autolink

use seq.char

use seq1.exportinfo

use set.exportinfo

use file

use seq.file

use genEnumeration

use genPEG

use seq1.int

use set.int

use seq.modinfo

use set.modref

use seq.mytype

use seq1.patternType

use pretty

use reconstructUses

use standard

use set.sym/modref

use arc.symbol

use graph.arc.symbol

use set.arc.symbol

use seq.symbol

use set.symbol

use symbol1

use seq.symdef

use set.symdef

use sort.symdef

use textio

use token

use totext

use word

use seq1.seq.word

use sort.seq.word

use seq1.word

use set.word

use sort.word

function finishmodule(
modtext0:seq.seq.word
, reorguse:boolean
, bind:boolean
, m:midpoint
, modrenames:seq.word
) seq.seq.word
let modname = (modtext0 sub 1) sub 2
for
 modtext = empty:seq.seq.word
 , uses = empty:seq.seq.word
 , ingenerated = false
 , p ∈ modtext0
do
 if ingenerated then next(modtext + p, uses, true)
 else if p = "<<<< Below is auto generated code >>>>" then next(modtext + p, uses, true)
 else if p sub 1 ∈ "Function function Export unbound Builtin builtin precedence type" then next(modtext + pretty.p, uses, ingenerated)
 else if getkey.p ∈ "use" ∧ reorguse then next(modtext, uses + p << 1, ingenerated)
 else next(modtext + p, uses, ingenerated)
let uselist0 =
 if bind ∧ reorguse then
  for dict = empty:set.symbol, sd ∈ toseq.prg.m do dict + sym.sd
  for
   uselist = empty:seq.seq.word
   , ref4 ∈ toseq.reconstruceUses(m, modname, dict, exportedmodref.m, uses)
  do uselist + %.ref4,
  uselist
 else uses
for uselist1 = empty:seq.seq.word, u ∈ uselist0
do
 assert not.isempty.u report "SDF"
 {only first word of u is a module name}
 uselist1 + ([rename(modrenames, u sub 1)] + u << 1)
for idx = 0, e ∈ modtext while getkey.e ∈ "precedence noncode Module" do idx + 1
for newuses = empty:seq.seq.word, e ∈ sortuse(uselist1, "") do newuses + ["use" + e],
subseq(modtext, 1, idx) + newuses + modtext << idx

function levelchange(levelchange:int) seq.word
if levelchange = 0 then "/br"
else if levelchange > 0 then patternseq(levelchange * 2, "//")
else patternseq(-levelchange, "/block")

function TOC(input:seq.seq.word, html:seq.word) seq.seq.word
let h = "/h1 /h2 /h3 /h4 /h5 /h6"
let Module = -1
for kinds = empty:set.int, e ∈ html
do
 let a = findindex("h1 h2 h3 h4 h5 h6", e),
 if a > n.h then if e ∈ "Module" then kinds + Module else kinds else kinds + a,
if isempty.kinds then input
else
 for acc = empty:seq.seq.word, toc = "", count = 1, lasth = 1, lastmod = 0, p ∈ input
 do
  let kind =
   if n.p < 2 then n.h + 2
   else if p sub 1 ∈ "Module" then Module
   else
    let t = findindex(h, last.p),
    if t ≤ n.h then t else n.h + 2,
  if kind > n.h ∨ kind ∉ kinds then next(acc + p, toc, count, lasth, lastmod)
  else
   let tagname = if kind = Module then p sub 2 else toword.count
   let href = "//:(merge("#" + tagname))/href",
   if kind = Module then
    let newacc = acc + p,
    next(newacc, toc + "//:(href):(p)/a", count + 1, lasth, 1)
   else
    next(
     acc + "// //:(tagname)/id:(p >> 1):(last.p)"
     , toc + levelchange(kind - (lastmod + lasth)) + "//:(href):(p >> 1)/a"
     , count + 1
     , kind
     , 0
    ),
 [toc + levelchange(1 - (lastmod + lasth))] + acc

function >4(a:symdef, b:symdef) ordering paragraphno.a >1 paragraphno.b

function print(s:set.autolink) seq.word
for acc = "", e ∈ toseq.s do acc + id.e + file.e + "/br",
acc

function getHeader(s:seq.word) seq.word
let gram =
 maketable."Head Export type:any Type' /action Export type:$.1 $.2 /br:($$)
 / any any:any Type' FPL any Type' /action $.1 $.2:$.3 $.4 $.5 $.6 $.7 /br:($$)
 / any any FPL any Type' /action $.1 $.2 $.3 $.4 $.5 /br:($$)
 * Type'.any /action /All /br:($$)
 FPL(L)/action($.1)/br:($$)
 / /action /br:($$)
 * L !)any /action /All",
run(gram, s) << 1

type exportinfo is modname:word, exporttxt:seq.word, cleaned:seq.word

function exportinfo(modname:word, exporttxt:seq.word) exportinfo
exportinfo(modname, exporttxt, cleanExport.exporttxt)

function %(a:exportinfo) seq.word [modname.a] + exporttxt.a + "/p"

function >2(a:exportinfo, b:exportinfo) ordering modname.a >1 modname.b

function >1(a:exportinfo, b:exportinfo) ordering
modname.a >1 modname.b ∧ cleaned.a >1 cleaned.b

function cleanExport(a:seq.word) seq.word
{removes parameter names and comments}
for acc = "", inpara = false, w ∈ a
while w ∉ "{"
do
 if w ∈ "(" then next(acc + w, true)
 else if w ∈ ")" then next(acc + w, false)
 else if inpara ∧ w ∈ ":" then next(acc >> 1, inpara)
 else next(acc + w, inpara),
acc

function cleanExports(m:midpoint) seq.seq.word
for acc3 = empty:set.exportinfo, modname2 = "?" sub 1, p ∈ src.m
do
 {this loop finds constructors for types}
 if p sub 1 ∈ "Module module" then next(acc3, p sub 2)
 else if p sub 1 ∈ "type" then
  next(
   acc3
   + exportinfo(
    modname2
    , "Export:(p sub 2)(:(p << 3)):(p sub 2):(if "T" sub 1 ∈ p then ".T" else "")"
   )
   , modname2
  )
 else next(acc3, modname2)
for acc = acc3, m1 ∈ libmods.m
do
 {this loop finds symbols exported from modules}
 for acc2 = acc, sym ∈ exports.m1
 do
  let t = getSymdef(prg.m, sym)
  let symdef =
   if isempty.t ∨ paragraphno.t sub 1 = 0 then
    if istype.sym then "Export type::(resulttype.sym)"
    else
     let tmp = %.sym,
     "Export:(tmp << findindex(tmp, ":" sub 1))"
   else getHeader.(src.m) sub paragraphno.t sub 1,
  if name.modname.m1 = name.module.sym ∧ subseq(symdef, 1, 1) = "Function" then acc2
  else
   {cannot easily identify what module"Builtin"was exported from}
   let from =
    if name.modname.m1 = name.module.sym ∨ name.module.sym ∈ "builtin internal" then ""
    else "{From:(module.sym)}",
   acc2 + exportinfo(name.modname.m1, "Export" + symdef << 1 + from),
 acc2
for src2 = empty:seq.seq.word, modname = "?" sub 1, p ∈ src.m
do
 if p sub 1 ∈ "Module module" then next(src2 + p, p sub 2)
 else if p sub 1 ∈ "Export" then
  let match = lookup(acc, exportinfo(modname, p))
  let toadd =
   if n.match ≠ 1 then
    {for txt ="", e ∈ toseq.findelement2(acc, exportinfo(modname,""))do txt+%(cleanExport.p = cleanExport.exporttxt.e)+%.e assert false report"NOMTC"+cleanExport.p+"/p
    "+txt,}
    p
    + "{no match}"
   else
    let new = exporttxt.match sub 1
    let j = findindex(p, "{" sub 1),
    if j > n.p ∨ subseq(p, j + 1, j + 1) = "From" then new
    else
     let extractedComment = subseq(p, j, j + findindex(p << j, "{" sub 1) - 1)
     let k = findindex(new, "{" sub 1),
     subseq(new, 1, k - 1) + extractedComment + subseq(new, k, n.p),
  next(src2 + toadd, modname)
 else next(src2 + p, modname),
src2

function getkey(p:seq.word) word
let keyidx = findindex(p, "/keyword" sub 1)
let key2 = if keyidx > n.p ∨ p sub 1 ∉ "//" then p sub 1 else p sub (keyidx - 1),
if key2 ∈ "Function function Builtin builtin Export Module unbound Unbound precedence type use" then key2
else "noncode" sub 1

Function transform2(
m:midpoint
, output:seq.word
, target:seq.word
, modrenames:seq.word
, bind:boolean
, reorguse:boolean
, html:seq.word
, cleanexports:boolean
, moveexports:boolean
, input2:seq.file
, link:seq.file
, patternmods:seq.word
) seq.file
{let testW = n.input2 = 1 ∧ name.fn.input2 sub 1 ∈"symbolconstant"}
{???? moveexport not implemented, Detection of duplicate Exports}
let patterns =
 if not.bind ∨ isempty.patternmods then empty:seq.patternType
 else getpatterns(m, patternmods)
let srctext0 =
 if bind then
  let changed = changes(m, patterns)
  let prg = if isempty.changed then toseq.prg.m else toseq(asset.changed ∪ prg.m)
  let src = if cleanexports then cleanExports.m else src.m
  let autolinks = if not.isempty.link then getautolinks(m, link) else empty:set.autolink,
  for lastno = 0, acc5 = empty:seq.seq.word, sd ∈ sort>4.prg
  do
   if paragraphno.sd = 0 then next(lastno, acc5)
   else
    let srctext2 = src sub paragraphno.sd,
    if srctext2 sub 1 ∈ "Function function Builtin builtin" then
     let tmp0 = prettyFunction(srctext2, code.sd, autolinks) + "/code",
     next(paragraphno.sd, acc5 + subseq(src, lastno + 1, paragraphno.sd - 1) + tmp0)
    else next(lastno, acc5),
  acc5 + subseq(src, lastno + 1, n.src)
 else
  let discard = tknencoding
  for acc = empty:seq.seq.word, i ∈ input2
  do
   if ext.fn.i ∈ "libinfo" then acc
   else
    let prgrph = breakparagraph.data.i
    for acc1 = acc, skip = false, p ∈ prgrph
    do
     let key = p sub 1,
     if key ∈ "Module module" then next(acc1 + p, false)
     else if skip then next(acc1, skip)
     else if n.p > 3 ∧ key ∈ "precedence" ∧ p sub 3 ∈ "for" then
      let discard1 = addprec(p, false),
      next(acc1 + p, skip)
     else if key ∈ "Function function Builtin builtin" then
      if subseq(p, 1, 2) ∈ ["function genPEG", "function genEnum"] ∧ isempty.html then
       for
        new = empty:seq.seq.word
        , pp ∈ if p sub 2 ∈ "genEnum" then generateEnum.p else generatePEG.p
       do
        new
        + if pp sub 1 ∈ "Function function builtin Builtin type Export" then pretty.pp else pp,
       next(
        acc1 + [pretty.p, "<<<< Below is auto generated code >>>>"] + new + ["Module auto gen end"]
        , true
       )
      else
       let tmp = pretty.p
       {for id ="", e ∈ tmp while e ∉"/id"do if e ∈"//"then""else id+e assert false report"ids"+id+showZ.subseq(tmp, 1, 20)}
       next(acc1 + tmp, skip)
     else next(acc1 + p, skip),
    acc1,
  acc
let srctext = {create table of content}TOC(srctext0, html)
let directory = if isempty.target then "tmp" else target
{break into modules}
let inModule = 1
let skip = 2
for
 modinfo = empty:seq.modinfo
 , modText = empty:seq.seq.word
 , lib2 = directory sub 1
 , mod2dir = ""
 , state = 0
 , p ∈ srctext + "Module ?"
do
 if isempty.p ∨ subseq(p, 1, 2) = "# File" ∧ n.p > 5 then next(modinfo, modText, merge(directory + "/" + p sub 5), mod2dir, state)
 else if p = "Module auto gen end" then next(modinfo, modText, lib2, mod2dir, skip)
 else
  let key = getkey.p,
  if key ∈ "Module module" then
   if state = 0 then
    {first module}
    let newmodinfo = if isempty.modText then modinfo else [modinfo("", modText)],
    next(newmodinfo, [p], lib2, [lib2], inModule)
   else
    let modname = rename(modrenames, (modText sub 1) sub 2)
    let newModText =
     ["// //:(modname)/id Module /keyword" + modname + modText sub 1 << 2] + modText << 1,
    let newway0 = finishmodule(newModText, reorguse, bind, m, modrenames),
    next(modinfo + modinfo(mod2dir + modname, newway0), [p], lib2, [lib2], inModule)
  else if state = skip then next(modinfo, modText + p, lib2, mod2dir, state)
  else next(modinfo, modText + p, lib2, mod2dir, state)
{Create the output files. One sfile is created if producing HTML output. Otherwise, a file is created for each Module. }
if not.isempty.html then
 for maintxt = "", e ∈ modinfo do maintxt + %("/p", body.e),
 [file(filename.output, maintxt)]
else
 let bindpara =
  if not.bind then ""
  else "bind:(if isempty.patterns then "" else "patterns applied::(patterns)")"
 let para =
  (if reorguse then "reorguse" else "")
  + bindpara
  + (if cleanexports then "cleanexports" else "")
  + for txt2 = "", x ∈ input2 do txt2 + "/br" + fullname.fn.x,
  txt2,
 for files = empty:seq.file, summary = "inputs:(para)/p files created", e ∈ modinfo
 do
  if isempty.filename.e then next(files, summary)
  else
   let fn = filename("+" + filename.e + ".ls")
   for newway = empty:seq.seq.word, e2 ∈ body.e do newway + removeMarkup.e2,
   next(files + file(fn, %("/p", newway) >> 1), summary + "/br" + fullname.fn),
 files + file(output, summary)

type modinfo is filename:seq.word, body:seq.seq.word

function getautolinks(m:midpoint, link:seq.file) set.autolink
{this looks at the html files in link and creates autolink entries}
for autolinks0 = empty:set.autolink, sd ∈ toseq.prg.m
do if paragraphno.sd = 0 then autolinks0 else autolinks0 + autolink(id.sym.sd, "")
for autolinks = autolinks0, f ∈ link
do
 if ext.fn.f ∉ "html" then autolinks
 else
  for autolink1 = autolinks, p1 ∈ breakparagraph.[f]
  do
   if isempty.p1 then autolink1
   else
    for autolink2 = autolink1, p ∈ break(p1, "<p>", false)
    do
     {assert">Function</a>"sub 1 ∉ p report":(esc.subseq(p, 1, 4))hereyX:(esc.p)"}
     if subseq(p, 1, 4) ≠ "<a id =:(dq)" ∨ ">Function</a>" sub 1 ∉ p then autolink2
     else
      let i = findindex(p << 4, dq sub 1)
      let linkvalue = subseq(p, 4, i + 4)
      let tmp = asset.[autolink(linkvalue, "../ /nsp" + fullname.fn.f)] ∪ autolink2,
      {assert isempty.find(autolink2, linkvalue)report":(linkvalue)herey:(esc.p)/p
      "+print.find(autolink2, linkvalue)+"/p
      "+print.find(tmp, linkvalue),}
      tmp,
    autolink2,
  autolink1,
autolinks

Function unusedsymbols2(
m:midpoint
, all:boolean
, generated0:boolean
, excessExports:boolean
, ignore0:seq.word
) seq.word
let ignore = if isempty.ignore0 then "genEnum genPEG" else ignore0
let dict =
 for uses = empty:set.symbol, sd ∈ toseq.prg.m do uses + sym.sd,
 uses
let templates =
 for acc = templates.m, sym ∈ toseq.dict
 do
  if isAbstract.module.sym ∧ isempty.getCode(templates.m, sym) then acc + symdef(sym, empty:seq.symbol, 0)
  else acc,
 acc
let roots =
 for acc = empty:set.symbol, sd ∈ toseq.prg.m
 do if COMMAND ∈ options.sd then acc + sym.sd else acc,
 acc
let a2 = closeuse(empty:set.symbol, roots, prg.m, templates, dict)
let a3 =
 for acc = empty:set.symbol, prg = empty:seq.symdef, sym ∈ toseq(dict \ a2)
 do
  let b = getSymdef(prg.m, sym),
  if not.isempty.b ∧ paragraphno.b sub 1 ≠ 0 ⊻ generated0 then next(acc + sym, prg + b sub 1)
  else next(acc, prg),
 if all then acc
 else
  acc
  \ for arcs = empty:set.arc.symbol, sd ∈ prg
  do
   for arcs2 = arcs, sy ∈ toseq(asset.code.sd ∩ acc - sym.sd) do arcs2 + arc(sym.sd, sy),
   arcs2
  let g = newgraph.toseq.arcs,
  nodes.g \ asset.sources.g
let outsyms =
 if excessExports then
  {symbols exported from a module and only used internally to that module}
  let exportedSymbols =
   for acc = empty:seq.symbol, alibmod ∈ libmods.m do acc + exports.alibmod,
   acc
  for
   internaluse = empty:set.symbol
   , externaluse = empty:set.symbol
   , sd ∈ toseq.prg.m + toseq.templates.m
  do
   for internal0 = internaluse, external0 = externaluse, sy ∈ code.sd
   do
    if module.sy = module.sym.sd then next(internal0 + sy, external0)
    else next(internal0, external0 + sy),
   next(internal0, external0),
  internaluse ∩ asset.exportedSymbols \ externaluse \ a3
 else a3
for acc = empty:seq.seq.word, sym ∈ toseq.outsyms
do if name.sym ∈ ignore then acc else acc + %.sym,
"Unused symbols for roots:(toseq.roots)/p:(%n.sort>alpha.acc)"

function rename(renames:seq.word, name:word) word
let i = findindex(renames, name),
if i > n.renames then name else renames sub (i + 1)

function closeuse(
done:set.symbol
, toprocess:set.symbol
, prg:set.symdef
, templates:set.symdef
, dict:set.symbol
) set.symbol
let new0 =
 for acc = empty:seq.symbol, sym ∈ toseq.toprocess do acc + getCode(prg, sym),
 acc
let new1 =
 for acc = empty:seq.symbol, sym ∈ toseq.asset.new0
 do
  let kind = kind.sym,
  if kind.sym ∈ isOrdinary ∨ kind.sym ∈ [kfref] then acc + sym else acc,
 asset.acc \ done
let new2 = requires(new1, templates, dict, true) \ done ∪ new1,
if isempty.new2 then done else closeuse(done ∪ toprocess, new2, prg, templates, dict)

function ⊻(a:boolean, b:boolean) boolean if a then not.b else b

function %(a:arc.symbol) seq.word %.tail.a + %.head.a 