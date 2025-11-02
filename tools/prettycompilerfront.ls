Module prettycompilerfront

use PEG

use seq.char

use cleanExports

use file

use seq.file

use functionHeader

use genEnumeration

use genPEG

use seq.headerType

use seq1.int

use set.int

use set.modref

use set.myExport

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

use set.symlink

use textio

use token

use totext

use word

use seq1.seq.word

use sort.seq.word

use seq1.word

use set.word

use sort.word

function key(p:seq.word) word
if isempty.p then "?" sub 1
else if p sub 1 ∈ "/keyword" then p sub 2
else
 assert p sub 1 ∉ "<a" report p,
 p sub 1

function finishmodule(
modtext:seq.word
, reorguse:boolean
, moveexports:boolean
, bind:boolean
, m:midpoint
, exportinfo:set.myExport
, modrenames:seq.word
, exported:set.sym/modref
, dict:set.symbol
, uses:seq.seq.word
) seq.word
let modname = modtext sub 2,
if not.reorguse ∧ not.moveexports then modtext
else
 let uselist0 =
  if bind ∧ reorguse then
   for uselist = empty:seq.seq.word, ref4 ∈ toseq.reconstruceUses(m, modname, dict, exported, uses)
   do uselist + %.ref4,
   uselist
  else uses
 for uselist1 = empty:seq.seq.word, u ∈ uselist0
 do
  assert not.isempty.u report "SDF"
  {only first word of u is a module name}
  uselist1 + ([rename(modrenames, u sub 1)] + u << 1)
 let uselist = sortuse(uselist1, ""),
 let idx = includecomment.modtext,
 "Module"
  + rename(modrenames, modname)
  + subseq(modtext, 3, idx - 1)
  + for newuses = "", e ∈ uselist do newuses + "/p /keyword use" + e,
 newuses
  + (if moveexports then newtext(exportinfo, modname) else "")
  + modtext << (idx - 1)

function levelchange(levelchange:int) seq.word
if levelchange = 0 then "/br"
else if levelchange > 0 then patternseq(levelchange * 2, "<* block")
else patternseq(-levelchange, "*>")

function TOC(input:seq.seq.word, html:seq.word) seq.seq.word
let h = "<h1> <h2> <h3> <h4> <h5> <h6>"
let Module =-1
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
   else if p sub 1 ∈ "/tag" then findindex(h, p sub 2)
   else n.h + 2,
  if kind > n.h ∨ kind ∉ kinds then next(acc + p + "/p", toc, count, lasth, lastmod)
  else
   let tagname = if kind = Module then p sub 2 else toword.count
   let href = "/tag <a /sp href =:(dq."# /tag:(tagname)") >",
   if kind = Module then
    let newacc = acc + p + "/p",
    if lastmod = 1 then next(newacc, toc + href + (p << 1 + "/tag </a>"), count + 1, lasth, 1)
    else next(newacc, toc + "<* block:(href):(p) /tag </a>", count + 1, lasth, 1)
   else
    next(
     acc + "/tag <a /sp id =:(dq."/tag:(tagname)") />:(p) /p"
     , toc
      + levelchange(kind - (lastmod + lasth))
      + (href + subseq(p, 3, n.p - 2) + "/tag </a>")
     , count + 1
     , kind
     , 0
    ),
 [toc + levelchange(1 - (lastmod + lasth))] + acc

function getHeader3(s:seq.word) seq.word
let gram =
 maketable."Head FName:any Type' FPL any Type' C /action $.1: $.2 $.3 $.4 $.5 $.6 $.7
 /br / FName FPL any Type' C /action $.1 $.2 $.3 $.4 $.5
 /br * Type'.any /action /All
 /br FPL /tag (L) /action /tag ($.1) / /action
 /br * L !) any /action /All
 /br FName ! /sp !+!-! # ! ^ any /action $.1
 /br / /sp any /action /sp $.1
 /br C //br <* comment /tag {N} *> /action //br {$.1}
 /br / <* comment /tag {N} *> /action {$.1}
 /br / /action
 /br * N {N} /action $.0 {$.1}
 /br / !} any /action $.0 $.1",
run(gram, s) << 1

function functionId(p:seq.word) seq.word
{???? need to get type when no parameters}
if p sub 1 ∈ "Function function" then
 for j = 3 while p sub j ∈ ".:" do j + 2
 let z =
  (if j = 3 then subseq(p, 2, 2)
  else subseq(p, 2, {2)+":"+subseq (p, 3,} j - 1))
   + if p sub j ∉ "(" then
   for k = j + 1 while p sub k ∈ "." do k + 2,
   subseq(p, j + 1, k - 1)
  else
   for k = findindex(p, ")" sub 1) + 2
   while p sub k ∈ "."
   do k + 2
   for acc = ":", last = p sub (j + 1), e ∈ subseq(p, j + 2, k - 1) + ","
   do
    if e ∈ ":" ∨ last ∈ ",:)" then next(acc, e)
    else if e ∈ ",)" then next(acc + last + ":", e)
    else next(acc + last, e),
   acc >> 1,
 z
else ""

function >4(a:symdef, b:symdef) ordering paragraphno.a >1 paragraphno.b

use token

use functionHeader

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
let exportinfo = manageExports.m
let patterns =
 if not.bind ∨ isempty.patternmods then empty:seq.patternType
 else getpatterns(m, patternmods)
let srctext0 =
 if bind then
  let changed = changes(m, patterns)
  let prg = if isempty.changed then toseq.prg.m else toseq(asset.changed ∪ prg.m)
  let src = src.m
  let symlinks = if not.isempty.link then getsymlinks(m, link) else empty:set.symlink,
  for lastno = 0, acc5 = empty:seq.seq.word, sd ∈ sort>4.prg
  do
   if paragraphno.sd = 0 then next(lastno, acc5)
   else
    let header = getheader.src sub paragraphno.sd
    let newwords = pretty(header, code.sd, symlinks, true),
    let tmp =
     if not.isempty.html ∧ not.isempty.link then "/sp /tag <a /sp id =:(dq."/tag:(id.sym.sd)") href =:(dq."/tag #:(name.module.sym.sd)") >:(newwords sub 2) /sp /tag </a>:(newwords << 2)"
     else newwords,
    next(paragraphno.sd, acc5 + subseq(src, lastno + 1, paragraphno.sd - 1) + tmp),
  acc5 + subseq(src, lastno + 1, n.src)
 else
  let discard = tknencoding
  for acc = empty:seq.seq.word, i ∈ input2
  do if ext.fn.i ∈ "libinfo" then acc else acc + breakparagraph.data.i,
  for discardresult = "", e ∈ acc
  do
   if n.e > 4 ∧ e sub 1 ∈ "precedence" ∧ e sub 3 ∈ "for" then addprec(e, false)
   else discardresult,
  acc
let srctext = {create table of content} TOC(srctext0, html)
{dict and exported are only used to reconstruct use clauses}
for dict = empty:set.symbol, sd ∈ if bind ∧ reorguse then toseq.prg.m else empty:seq.symdef
do dict + sym.sd
let exported = exportedmodref.m
let directory = if isempty.target then "tmp" else target
{Reorder the paragraphs in the output that has been prettied.}
for
 txt = empty:seq.seq.word
 , modtext = ""
 , uses = empty:seq.seq.word
 , pno = 1
 , p ∈ srctext + "Module ?"
do
 if isempty.p then next(txt, modtext, uses, pno + 1)
 else
  let key = key.p,
  if subseq(p, 1, 2) = "# File" then next(txt, modtext, uses, pno + 1)
  else if p sub 1 ∈ "use" then
   if reorguse then next(txt, modtext, uses + p << 1, pno + 1)
   else next(txt, modtext + "/p /keyword" + p, uses, pno + 1)
  else if key ∈ "Function function type" then
   if not.bind
   ∧ isempty.html
   ∧ subseq(p, 1, 2) ∈ ["function genPEG", "function genEnum"]
   ∧ n.modtext > 1 then
    for
     generatedtext = ""
     , e ∈ [p, "<<<< Below is auto generated code >>>>"]
      + (if p sub 2 ∈ "genEnum" then generateEnum.p else generatePEG.p)
    do
     if e sub 1 ∈ "Function function type Export" then generatedtext + pretty.e + "/p"
     else generatedtext + escapeformat.e + "/p"
    let formatedModuleText =
     finishmodule(
      modtext + "/p" + generatedtext >> 1
      , reorguse
      , moveexports
      , bind
      , m
      , exportinfo
      , modrenames
      , exported
      , dict
      , uses
     ),
    next(txt + formatedModuleText, "", empty:seq.seq.word, pno + 1)
   else
    let tmp =
     if bind ∧ key ∉ "type" then p
     else if p sub 1 ∈ "Function function unbound Builtin builtin" ∧ not.isempty.html then "/sp /tag <a /sp id =:(dq."/tag:(functionId.p)") href =:(dq."#:(subseq(modtext, 2, 2))") >:(p sub 1) /sp /tag </a>:(pretty.p << 2)"
     else pretty.p,
    next(txt, modtext + "/p" + tmp, uses, pno + 1)
  else if key ∈ "unbound Builtin builtin" then next(txt, modtext + "/p" + pretty.p, uses, pno + 1)
  else if key ∈ "Module module" then
   if key.modtext ∉ "Module module" then next(txt + modtext, p, empty:seq.seq.word, pno + 1)
   else
    let formatedModuleText = finishmodule(modtext, reorguse, moveexports, bind, m, exportinfo, modrenames, exported, dict, uses),
    next(txt + formatedModuleText, p, empty:seq.seq.word, pno + 1)
  else
   let newmodtext =
    if key ∈ "Export" then
     if cleanexports ∨ moveexports then
      let p2 = newtext(exportinfo, pno, modtext sub 2),
      if isempty.p2 ∨ moveexports then modtext else modtext + "/p" + pretty.p2
     else modtext + "/p" + pretty.p
    else modtext + "/p" + if not.isempty.html then p else escapeformat.p,
   next(txt, newmodtext, uses, pno + 1)
{Create the output files. One file is created if producing HTML output.Otherwise, A file for each module is created for each Module}
if not.isempty.html then
 for maintxt = "", M ∈ txt
 do
  if isempty.M then maintxt
  else
   maintxt
    + ((if M sub 1 ∈ "Module" then "/tag <span /sp id =:(dq."/tag:(subseq(M, 2, 2))") class =:(dq."keyword") > Module /sp /tag </span> /sp:(M << 1)"
   else M)
    + "/p"),
 [file(output, maintxt)]
else
 let modtodir =
  for modtodir = "", lib = directory sub 1, p1 ∈ if bind then src.m else srctext
  do
   if isempty.p1 then next(modtodir, lib)
   else if p1 sub 1 ∈ "Module module" then next(modtodir + "/br" + rename(modrenames, p1 sub 2) + lib, lib)
   else if subseq(p1, 1, 2) = "# File" ∧ n.p1 > 5 then next(modtodir, merge(directory + "/" + p1 sub 5))
   else next(modtodir, lib),
  modtodir
 let bindpara =
  if not.bind then ""
  else "bind:(if isempty.patterns then "" else "patterns applied::(patterns)")"
 let para =
  (if reorguse then "reorguse" else "")
   + bindpara
   + (if cleanexports then "cleanexports" else "")
   + (if moveexports then "moveexports" else "")
   + for txt2 = "", x ∈ input2 do txt2 + "/br" + fullname.fn.x,
  txt2,
 for files = empty:seq.file, summary = "inputs:(para) /p files created", M ∈ txt
 do
  if subseq(M, 1, 1) ∉ ["Module", "module"] ∨ char1."$" ∈ decodeword.M sub 2 ∨ n.M < 2 then next(files, summary)
  else
   let modname = M sub 2
   let idx = findindex(modtodir, modname),
   let fn = filename("+" + modtodir sub (idx + 1) + modname + ".ls"),
   next(files + file(fn, M), summary + "/br" + fullname.fn),
 files + file(output, summary)

function getsymlinks(m:midpoint, link:seq.file) set.symlink
for symlinks0 = empty:set.symlink, sd ∈ toseq.prg.m
do if paragraphno.sd = 0 then symlinks0 else symlinks0 + symlink(id.sym.sd, "")
for symlinks = symlinks0, f ∈ link
do
 if ext.fn.f ∉ "html" then symlinks
 else
  for symlink1 = symlinks, p ∈ breakparagraph.[f]
  do
   if subseq(p, 1, 4) = "<p> <a id =" then
    let z = findindex(p, ">" sub 1)
    let kind = if z < n.p then p sub (z + 1) else "?" sub 1,
    if kind ∈ "function Function" then
     let z2 = findindex(p << 5, dq sub 1)
     let linkvalue = subseq(p, 6, z2 + 4),
     symlink1 + symlink(linkvalue, "../tag /" + fullname.fn.f)
    else symlink1
   else symlink1,
  symlink1,
symlinks

Function unusedsymbols2(
m:midpoint
, all:boolean
, generated0:boolean
, excessExports:boolean
, ignore0:seq.word
) seq.word
let ignore = if isempty.ignore0 then "genEnum genPEG" else ignore0
let dict =
 for uses = empty:set.symbol, sd ∈ toseq.prg.m
 do uses + sym.sd,
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
   for arcs2 = arcs, sy ∈ toseq(asset.code.sd ∩ acc - sym.sd)
   do arcs2 + arc(sym.sd, sy),
   arcs2
  let g = newgraph.toseq.arcs,
  nodes.g \ asset.sources.g
let outsyms =
 if excessExports then
  {symbols exported from a module and only used internally to that module}
  let exportedSymbols =
   for acc = empty:seq.symbol, alibmod ∈ libmods.m
   do acc + exports.alibmod,
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
"Unused symbols for roots:(toseq.roots) /p:(%n.sort>alpha.acc)"

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
 for acc = empty:seq.symbol, sym ∈ toseq.toprocess
 do acc + getCode(prg, sym),
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
