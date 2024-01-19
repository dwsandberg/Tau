Module makescript

Implements the makeScript command which is used by taubuild.sh.

use UTF8

use seq.UTF8

use set.UTF8

use bits

use otherseq.byte

use seq.seq.byte

use file

use seq.file

use seq.arc.filename

use set.arc.filename

use graph.filename

use otherseq.filename

use set.filename

use otherseq.lineinfo

use set.lineinfo

use standard

use textio

use word

use otherseq.word

use set.word

type lineinfo is output:seq.filename, input:seq.filename, line:seq.word, def:cmddef

function >1(a:lineinfo, b:lineinfo) ordering 1#output.a >1 1#output.b

function %(a:lineinfo) seq.word %.output.a + %.input.a + line.a

Function makeScript(
input:seq.file
, builddir:seq.word
, hashes:seq.file
, output:seq.word
) seq.file
{COMMAND /strong makeScript creates shell script for building code.
/br The commands' primary is is in the shell script taubuild.
/br /strong input build files
/br /strong builddir build directory, usually"+built".
/br /strong hashes two files with one containing lines from the unix command shasum. The two files are compared looking for identical lines which is used to determine which files have not be changed since the last build.}
let txtbytes =
 toseqbyte.textformat."if [[/sp-n true /sp]] ; then
 /br^(makeScriptCore(input, builddir, 1#"script", hashes)) /br else
 /br shahash of source files
 /br"
let databytes = if isempty.hashes then empty:seq.byte else data.1#hashes
let fn = filename.output,
[file(fn, txtbytes + tobyte.10 + databytes + toseqbyte.textformat."/br fi")]

function tolineinfo(line0:seq.word, builddir:seq.word, cmddef:cmddef) lineinfo
let line =
 if subseq(line0, 3, 3) ∈ [":", ": "] then line0
 else %.1#line0 + "input: " + line0 << 1
for
 outfn = empty:seq.filename
 , infn = if cmdlib.cmddef ∉ "shell" then [filename(builddir + "^(cmdlib.cmddef).lib")]
 else empty:seq.filename
 , acc = ""
 , value = ""
 , invalue = false
 , last = 1#line
 , w ∈ line + ".:x"
do
 if w ∉ ":: " then
  if invalue then next(outfn, infn, acc, value + w, invalue, w)
  else next(outfn, infn, acc + w, value, invalue, w)
 else
  let newstate = last ∈ (infiles.cmddef + "output"),
  if not.invalue then next(outfn, infn, acc + w, value, newstate, w)
  else
   let name = 2^acc
   let filenames = if n.value < 2 then empty:seq.filename else tofilenames(builddir + value >> 1),
   let newacc = acc + fullnames.filenames + [last, w],
   if name ∈ "output" then next(filenames, infn, newacc, "", newstate, w)
   else next(outfn, infn + filenames, newacc, "", newstate, w)
assert not.isempty.outfn report "must specify /em output in:/sp^(line)",
if ext.1#outfn ∈ "lib" ∧ 3#toseq.cmddef ∉ "shell" then
 for dependlibs = "/br dependlibs /tag _^(name.1#outfn) /tag =^(dq)", fn ∈ infn
 do if ext.fn ∈ "libinfo" then dependlibs + "built /tag /^(name.fn).bc" else dependlibs,
 lineinfo(
  outfn
  , infn
  , acc >> 3
   + dependlibs
   + dq
   + "/br linklibrary^(name.1#outfn)"
   + "output:"
   + fullnames.outfn
  , cmddef
 )
else lineinfo(outfn, infn, acc >> 3, cmddef)

function substitute(s:seq.word, b:seq.word, replacement:seq.word) seq.word
let i = findindex(s, 1^b),
if i > n.s then s
else if subseq(s, i - n.b + 1, i) = b then subseq(s, 1, i - n.b) + replacement + substitute(s << i, b, replacement)
else subseq(s, 1, i) + substitute(s << i, b, replacement)

function unchanged(hashes:seq.file) seq.filename
if n.hashes < 2 then empty:seq.filename
else
 let lines = toseq(asset.breaklines.data.1#hashes ∩ asset.breaklines.data.2#hashes),
 if isempty.lines then empty:seq.filename
 else
  let i = findindex(toseqbyte.1#lines, tobyte.toint.char.32)
  for unchanged = empty:seq.filename, line ∈ lines
  do
   for j = n.toseqbyte.line, b ∈ reverse.toseqbyte.line
   while b ∉ [tobyte.toint.char1."/", tobyte.32]
   do j - 1
   let t =
    towords.UTF8(
     subseq(toseqbyte.line, i + 1, j - 1)
      + tobyte.32
      + subseq(toseqbyte.line, j + 1, n.toseqbyte.line)
    ),
   if n.t = 4 then unchanged + filename."+^(t)"
   else if n.t = 1 then unchanged + filename.t
   else
    assert n.t = 3 ∧ 2#t ∈ "." report "SDF^(t)",
    unchanged + filename.t,
  unchanged

type cmddef is toseq:seq.word

function infiles(c:cmddef) seq.word
if n.toseq.c < 5 ∨ 3#toseq.c ∈ "shell" then "input" else toseq.c << 4

function cmdlib(a:cmddef) word 3#toseq.a

function >1(a:cmddef, b:cmddef) ordering 2#toseq.a >1 2#toseq.b

use set.cmddef

Function makeScriptCore(
input:seq.file
, builddir:seq.word
, format:word
, hashes:seq.file
) seq.word
for allfile = empty:set.lineinfo, defs = empty:set.cmddef, f ∈ breakparagraph.input
do
 if 1#f ∈ "#" then next(allfile, defs)
 else
  let aa = substitute(f, "+$build", builddir),
  if 1#aa ∈ "define" then next(allfile, defs + cmddef(if n.aa = 3 then aa + 2#aa else aa))
  else
   let find = lookup(defs, cmddef("define" + 1#aa))
   assert not.isempty.find report "command /em^(1#aa) is not defined. ",
   next(allfile + tolineinfo(aa, builddir, 1#find), defs)
{build graph}
for arcs1 = empty:seq.arc.filename, line ∈ toseq.allfile
do
 let tail = 1#output.line
 for more = arcs1, fn ∈ output.line << 1
 do more + arc(fn, tail),
 for arcs2 = more, fn ∈ input.line do arcs2 + arc(tail, fn),
 arcs2
let g = newgraph.arcs1
let unchanged = asset.unchanged.hashes
let changed = asset.sinks.g \ unchanged \ asset.[filename(builddir + "shell.lib")]
let outdated = reachable(complement.g, toseq.changed) \ changed
for changelist = "", n ∈ toseq.changed
do changelist + fullname.n
for unchangelist = "", n ∈ toseq.unchanged
do unchangelist + fullname.n
let acc2 =
 "set /sp-e
 /br changelist /tag =^(dq.changelist) /br unchangelist /tag =^(dq.unchangelist) /br for f in $changelist $unchangedlist ; do
 /br if ! [/sp-f $f /sp] ; then
 /br echo^(dq."File $f does not exist.") ; exit 1
 /br fi
 /br done
 /br if [[/sp-z $makehash /sp]] ; then"
for acc = acc2 + "/br#remove outdated files", dated ∈ toseq.outdated
do acc + "/br rm /sp-f" + fullname.dated
let subg = subgraph(g, outdated),
if format ∉ "script" then
 for debugtxt = "", a ∈ if format ∈ "full" then toseq.arcs.g else toseq.arcs.subg
 do debugtxt + "+^(tail.a)+^(head.a)",
 debugtxt
else
 for cmds = "", d ∈ toseq.defs
 do
  if cmdlib.d ∈ "shell" then cmds
  else
   let cmd = 2#toseq.d
   let exe = cmdlib.d,
   let rest = if n.toseq.d < 4 then [cmd] else [4#toseq.d],
   cmds
    + "/br function^(cmd) {
   /br /tag built/^(exe).lib^(rest) $@
   /br if [/sp-e error.html /sp] ; then
   /br $tauopen error.html ; exit 1
   /br fi
   /br}",
 createorder(subg, allfile, acc + cmds) + "/br fi"

Function fullnames(s:seq.filename) seq.word
for acc = "", fn ∈ s do acc + fullname.fn,
acc

function createorder(g:graph.filename, defs:set.lineinfo, out:seq.word) seq.word
let sinks = sinks.g,
if isempty.sinks then
 assert isempty.nodes.g report "cycle in graph",
 out
else
 for txt = out, p ∈ if isempty.sinks then toseq.nodes.g else sinks
 do
  let b = lookup(defs, lineinfo([p], empty:seq.filename, "", cmddef."")),
  if isempty.b then txt
  else
   let l = line.1#b,
   txt
    + if 1#l ∈ "define" then ""
   else if cmdlib.def.1#b ∈ "shell" then "/br^(shellparameters(toseq.def.1#b << 3, fullnames.input.1#b, fullnames.output.1#b, line.1#b))"
   else
    let l1 = if subseq(l, 2, 3) = "input: " then [1#l] + l << 3 else l,
    "/br echo making^(1#output.1#b) /br^(l1)",
 createorder(
  subgraph(g, nodes.g \ asset.sinks)
  , defs
  , txt + "/br#-------------------------------"
 )

function shellparameters(
cmd:seq.word
, input:seq.word
, output:seq.word
, other:seq.word
) seq.word
if n.cmd = 1 then cmd + "/sp /tag^(dq.input)"
else
 for out = subseq(cmd, 1, 1), last = 1#cmd, w ∈ cmd << 1
 do
  if w ∈ ":" then
   next(
    out >> 1
     + (if last ∈ "input" then input
    else if last ∈ "output" then output
    else extractValue(other, [last]))
    , w
   )
  else next(out + w, w),
 out

Function >1(a:UTF8, b:UTF8) ordering toseqbyte.a >1 toseqbyte.b

Function >1(a:filename, b:filename) ordering
alphaword.name.a >1 alphaword.name.b
∧ alphaword.ext.a >1 alphaword.ext.b
∧ alphaword.dirpath.a >1 alphaword.dirpath.b

Function >1(a:byte, b:byte) ordering toint.a >1 toint.b 