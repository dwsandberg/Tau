Module prettycompilerfront

use UTF8

use seq.char

use cleanExports

use file

use seq.file

use format

use genEnumeration

use genPEG

use otherseq.int

use set.modref

use set.myExport

use seq.mytype

use newPretty

use otherseq.patternType

use reconstructUses

use standard

use set.sym/modref

use set.arc.symbol

use graph.symbol

use seq.symbol

use set.symbol

use symbol2

use seq.symdef

use set.symdef

use textio

use totext

use otherseq.word

use otherseq.seq.word

use words

function key(p:seq.word) word
if isempty.p then 1_"?" else if 1_p ∈ "/keyword" then 2_p else 1_p

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
let modname = 2_modtext,
if not.reorguse ∧ not.moveexports then
modtext
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
  uselist1 + ([rename(modrenames, 1_u)] + u << 1)
 let uselist = sortuse(uselist1, "")
 {assert false report %n.uselist+" modtext:^(modtext)"}
 let idx = includecomment.modtext,
  "Module"
  + rename(modrenames, modname)
  + subseq(modtext, 3, idx - 1)
  + 
   for newuses = "", e ∈ uselist do newuses + "/p /keyword use" + e,
   newuses + (if moveexports then newtext(exportinfo, modname) else "") + modtext << (idx - 1)

Function transform2(
 m:midpoint
 , o:seq.word
 , target:seq.word
 , modrenames:seq.word
 , bind:boolean
 , reorguse:boolean
 , html:boolean
 , noindex:boolean
 , cleanexports:boolean
 , moveexports:boolean
 , input2:seq.file
 , patternmods:seq.word
) seq.file
let exportinfo = manageExports.m
let patterns =
 if not.bind ∨ isempty.patternmods then
 empty:seq.patternType
 else getpatterns(m, patternmods)
let srctext =
 if bind then
  let changed = changes(m, patterns)
  let prg = if isempty.changed then toseq.prg.m else toseq(asset.changed ∪ prg.m)
  let src = src.m
  for acc4 = src, sd ∈ prg
  do
   if paragraphno.sd = 0 then
   acc4
   else let newwords = totext(src, sd), replace(acc4, paragraphno.sd, newwords),
  acc4
 else
  for acc = empty:seq.seq.word, i ∈ input2
  do if ext.fn.i ∈ "libinfo" then acc else acc + breakparagraph.data.i,
  acc
let exported = exportedmodref.m
let dict = for uses = empty:set.symbol, sd ∈ toseq.prg.m do uses + sym.sd, uses
let directory = if isempty.target then "tmp" else target
for
 txt = empty:seq.seq.word
 , modtext = ""
 , uses = empty:seq.seq.word
 , pno = 1
 , p ∈ srctext + "Module ?"
do
 if isempty.p then
 next(txt, modtext, uses, pno + 1)
 else
  let key = key.p,
   if subseq(p, 1, 2) = "Library =" then
   next(txt, modtext, uses, pno + 1)
   else if 1_p ∈ "use" then
   next(txt, if reorguse then modtext else modtext + "/p /keyword" + p, uses + p << 1, pno + 1)
   else if key ∈ "Function function type" then
    if
     not.bind
     ∧ subseq(p, 1, 2) ∈ ["function PEGgen", "function genEnum"]
     ∧ n.modtext > 1
     ∧ 1^decodeword.2_modtext ≠ char1."?"
    then
     for
      generatedtext = ""
      , e ∈
       [p, "<<<< Below is auto generated code >>>>"]
       + if 2_p ∈ "genEnum" then generateEnum.p else generatePEG.p
     do
      if 1_e ∈ "Function function type Export" then
      generatedtext + pretty.e + "/p"
      else generatedtext + escapeformat.e + "/p"
     let formatedModuleText = finishmodule(
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
    else next(txt, modtext + "/p" + if bind ∧ key ∉ "type" then p else pretty.p, uses, pno + 1)
   else if key ∈ "unbound Builtin builtin" then
   next(txt, modtext + "/p" + pretty.p, uses, pno + 1)
   else if key ∈ "Module module" then
    if key.modtext ∉ "Module module" then
    next(txt + modtext, p, empty:seq.seq.word, pno + 1)
    else
     let formatedModuleText = finishmodule(modtext, reorguse, moveexports, bind, m, exportinfo, modrenames, exported, dict, uses),
     next(txt + formatedModuleText, p, empty:seq.seq.word, pno + 1)
   else
    let newmodtext =
     if key ∈ "Export" then
      if cleanexports ∨ moveexports then
       let p2 = newtext(exportinfo, pno, 2_modtext),
       if isempty.p2 ∨ moveexports then modtext else modtext + "/p" + pretty.p2
      else modtext + "/p" + pretty.p
     else modtext + "/p" + if html then p else escapeformat.p,
    next(txt, newmodtext, uses, pno + 1),
if html then
 for maintxt = "", header = "", M ∈ txt
 do
  if key.M ∉ "Module module" then
  next(maintxt + M + "/p", header)
  else
   let modname = 2_M
   let indextxt = if noindex then "" else "/< hr id =^(merge.dq.[modname]) >",
   next(
    maintxt + indextxt + "/keyword^(M) /p"
    , header + "/< a href =^(merge.dq("#" + modname)) >^(modname) /< /a>"
   ),
 [file(o, if noindex then maintxt else "^(header)^(maintxt)")]
else
 let modtodir =
  for modtodir = "", lib = 1_directory, p1 ∈ if bind then src.m else srctext
  do
   if isempty.p1 then
   next(modtodir, lib)
   else if 1_p1 ∈ "Module module" then
   next(modtodir + "/br" + rename(modrenames, 2_p1) + lib, lib)
   else if 1_p1 ∈ "Library" then
   next(modtodir, merge(directory + "/" + 3_p1))
   else next(modtodir, lib),
  modtodir
 let bindpara =
  if not.bind then
  ""
  else "bind^(if isempty.patterns then "" else "patterns applied:^(patterns)")"
 let para = "^(if reorguse then "reorguse" else "")^(bindpara)
  ^(if cleanexports then "cleanexports" else "")^(if moveexports then "moveexports" else "")
  ^(for txt2 = "", x ∈ input2 do txt2 + "/br" + fullname.fn.x, txt2)"
 for files = empty:seq.file, summary = "inputs^(para) /p files created", M ∈ txt
 do
  if subseq(M, 1, 1) ∉ ["Module", "module"] ∨ char1."$" ∈ decodeword.2_M ∨ n.M < 2 then
  next(files, summary)
  else
   let modname = 2_M
   let idx = findindex(modtodir, modname)
   let fn = filename("+" + (idx + 1)_modtodir + modname + ".ls"),
   next(files + file(fn, M), summary + "/br" + fullname.fn),
 files + file(o, summary)

Function unusedsymbols2(
 m:midpoint
 , all:boolean
 , generated0:boolean
 , excessExports:boolean
 , ignore0:seq.word
) seq.word
let ignore = if isempty.ignore0 then "genEnum genPEG" else ignore0
let dict = for uses = empty:set.symbol, sd ∈ toseq.prg.m do uses + sym.sd, uses
let templates =
 for acc = templates.m, sym ∈ toseq.dict
 do
  if isAbstract.module.sym ∧ isempty.getCode(templates.m, sym) then
  acc + symdef(sym, empty:seq.symbol, 0)
  else acc,
 acc
let roots =
 for acc = empty:set.symbol, sd ∈ toseq.prg.m
 do if 1_"ENTRYPOINT" ∈ getOptions.sd then acc + sym.sd else acc,
 acc
let a2 = closeuse(empty:set.symbol, roots, prg.m, templates, dict)
let a3 =
 for acc = empty:set.symbol, prg = empty:seq.symdef, sym ∈ toseq(dict \ a2)
 do
  let b = getSymdef(prg.m, sym),
   if not.isempty.b ∧ paragraphno.1_b ≠ 0 ⊻ generated0 then
   next(acc + sym, prg + 1_b)
   else next(acc, prg),
  if all then
  acc
  else
   acc
   \ 
    for arcs = empty:set.arc.symbol, sd ∈ prg
    do
     for arcs2 = arcs, sy ∈ toseq(asset.code.sd ∩ acc - sym.sd) do arcs2 + arc(sym.sd, sy),
     arcs2
    let g = newgraph.toseq.arcs,
    nodes.g \ asset.sources.g
let outsyms =
 if excessExports then
  {symbols exported from a module and only used internally to that module}
  let exportedSymbols = for acc = empty:seq.symbol, alibmod ∈ libmods.m do acc + exports.alibmod, acc
  for
   internaluse = empty:set.symbol
   , externaluse = empty:set.symbol
   , sd ∈ toseq.prg.m + toseq.templates.m
  do
   for internal0 = internaluse, external0 = externaluse, sy ∈ code.sd
   do
    if module.sy = module.sym.sd then
    next(internal0 + sy, external0)
    else next(internal0, external0 + sy),
   next(internal0, external0),
  internaluse ∩ asset.exportedSymbols \ externaluse \ a3
 else a3
for acc = empty:seq.seq.word, sym ∈ toseq.outsyms
do if name.sym ∈ ignore then acc else acc + %.sym,
"Unused symbols for roots^(toseq.roots) /p^(%n.alphasort.acc)"

function rename(renames:seq.word, name:word) word
let i = findindex(renames, name),
if i > n.renames then name else (i + 1)_renames

function closeuse(
 done:set.symbol
 , toprocess:set.symbol
 , prg:set.symdef
 , templates:set.symdef
 , dict:set.symbol
) set.symbol
let new0 = for acc = empty:seq.symbol, sym ∈ toseq.toprocess do acc + getCode(prg, sym), acc
let new1 =
 for acc = empty:seq.symbol, sym ∈ toseq.asset.new0
 do
  if
   isspecial.sym
   ∨ iswords.sym
   ∨ isInternal.sym
   ∨ islocal.sym
   ∨ name.module.sym ∈ "$for"
   ∨ isBuiltin.sym
   ∨ isIntLit.sym
   ∨ isRealLit.sym
  then
  acc
  else acc + sym,
 asset.acc \ done
let new2 = requires(new1, templates, dict, true) \ done ∪ new1,
if isempty.new2 then done else closeuse(done ∪ toprocess, new2, prg, templates, dict)

function ⊻(a:boolean, b:boolean) boolean if a then not.b else b

function %(a:arc.symbol) seq.word %.tail.a + %.head.a

function changes(m:midpoint, patterns:seq.patternType) seq.symdef
for psyms = empty:set.symbol, pat ∈ patterns do psyms + psym.pat
for acc4 = empty:seq.symdef, e ∈ toseq.prg.m
do
 if paragraphno.e = 0 ∨ sym.e ∈ psyms then
 acc4
 else
  for newcode = empty:seq.symbol, pat ∈ patterns
  do
   let tmp = replace2(if isempty.newcode then code.e else newcode, pattern.pat, replacement.pat, nopara.pat),
   if isempty.tmp then newcode else tmp,
   if isempty.newcode then
   acc4
   else acc4 + symdef4(sym.e, newcode, paragraphno.e, getOptionsBits.e),
acc4

function getpatterns(m:midpoint, patternmods:seq.word) seq.patternType
if isempty.patternmods then
empty:seq.patternType
else
 for acc = empty:seq.symbol, md ∈ libmods.m
 do if name.modname.md ∈ patternmods then acc + exports.md else acc
 for patterns = empty:seq.patternType, psym ∈ acc
 do
  let code = getCode(prg.m, psym),
   if isempty.code ∨ not.isSequence.1^code ∨ nopara.1^code ≠ 2 then
   patterns
   else
    let para2 = backparse3(code, n.code - 1, true)
    let para1 = backparse3(code, para2 - 1, true),
    setinsert(
     patterns
     , patternType(psym, nopara.psym, subseq(code, para1, para2 - 1), subseq(code, para2, n.code - 1))
    ),
 patterns

type patternType is psym:symbol, nopara:int, pattern:seq.symbol, replacement:seq.symbol

function name(p:patternType) word name.psym.p

function >1(a:patternType, b:patternType) ordering alphaword.name.a >1 alphaword.name.b

function %(p:patternType) seq.word "^(name.p)" 