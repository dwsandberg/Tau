Module makescript

use UTF8

use seq.UTF8

use set.UTF8

use bits

use otherseq.byte

use seq.seq.byte

use file

use seq.file

use seq.arc.filename

use graph.filename

use otherseq.filename

use set.filename

use standard

use textio

use otherseq.word

use set.word

use words

use otherseq.lineinfo

use set.lineinfo

type lineinfo is output:seq.filename, input:seq.filename, line:seq.word

function >1(a:lineinfo, b:lineinfo) ordering 1#output.a >1 1#output.b

function %(a:lineinfo) seq.word %.output.a + %.input.a + line.a

function tolineinfo(line:seq.word, builddir:seq.word) lineinfo
let sin = 1
let sout = 2
for acc = "", in = "", out = "", state = 0, last = 1#line, w ∈ line
do
 let newstate =
  if w ∈ ":=" then
  if last ∈ "<" then sin else if last ∈ ">" then sout else 0
  else state,
  if state = newstate then
   if state = 0 then
   next(acc + w, in, out, newstate, w)
   else if state = sin then
   next(acc, in + w, out, newstate, w)
   else next(acc, in, out + w, newstate, w)
  else if state = 0 then
  next(acc >> 1, in, out, newstate, w)
  else if state = sout ∧ newstate = sin then
  next(acc, in, out >> 1, newstate, w)
  else if state = sout ∧ newstate = 0 then
  next(acc + last + w, in, out >> 1, newstate, w)
  else if state = sin ∧ newstate = 0 then
  next(acc + last + w, in >> 1, out, newstate, w)
  else
   assert state = sin ∧ newstate = sout report "fail toline^(state)^(newstate)",
   next(acc, in >> 1, out, newstate, w)
let outfn = tofilenames(builddir + out)
let infn = tofilenames(builddir + in)
assert not.isempty.outfn report "must specify stdout with > in:/sp" + line,
if ext.1#outfn ∈ "lib" ∧ 1#line ∉ "shell" then
 for dependlibs = "/br dependlibs /tag _^(name.1#outfn) /tag =^(dq)", fn ∈ infn
 do
  if ext.fn ∈ "libinfo" then
  dependlibs + "built /tag /^(name.fn).bc"
  else dependlibs,
 lineinfo(outfn, infn, acc + dependlibs + dq + "/br linklibrary^(name.1#outfn)")
else lineinfo(outfn, tofilenames(builddir + in), acc)

function substitute(s:seq.word, b:seq.word, replacement:seq.word) seq.word
let i = findindex(s, 1^b),
if i > n.s then
s
else if subseq(s, i - n.b + 1, i) = b then
subseq(s, 1, i - n.b) + replacement + substitute(s << i, b, replacement)
else subseq(s, 1, i) + substitute(s << i, b, replacement)

function unchanged(hashes:seq.file) seq.filename
if n.hashes < 2 then
empty:seq.filename
else
 let lines = toseq(asset.breaklines.data.1#hashes ∩ asset.breaklines.data.2#hashes),
  if isempty.lines then
  empty:seq.filename
  else
   let i = findindex(toseqbyte.1#lines, tobyte.toint.char.32)
   for unchanged = empty:seq.filename, line ∈ lines
   do
    for j = n.toseqbyte.line, b ∈ reverse.toseqbyte.line
    while b ∉ [tobyte.toint.char1."/", tobyte.32]
    do j - 1
    let t = towords.UTF8(
     subseq(toseqbyte.line, i + 1, j - 1)
      + tobyte.32
      + subseq(toseqbyte.line, j + 1, n.toseqbyte.line)
    ),
     if n.t = 4 then
     unchanged + filename("+" + t)
     else if n.t = 1 then
     unchanged + filename.t
     else assert n.t = 3 ∧ 2#t ∈ "." report "SDF" + t, unchanged + filename.t,
   unchanged

Function makeScriptCore(
 input:seq.file
 , builddir:seq.word
 , debug:boolean
 , hashes:seq.file
) seq.word
for allfile = empty:set.lineinfo, defs = asset."shell", f ∈ breakparagraph.input
do
 if 1#f ∈ "#" then
 next(allfile, defs)
 else
  let aa = substitute(f, "+$build", builddir),
   if 1#aa ∈ "define" then
   next(
    allfile
     + lineinfo([filename."^(2#aa).cmd"], [filename(builddir + "^(3#aa).lib")], f)
    , defs + 2#aa
   )
   else
    assert 1#aa ∈ defs report "command /em^(1#aa) is not defined. ",
    next(allfile + tolineinfo(aa, builddir), defs)
let r = buildgraph.allfile
let g = newgraph.r
let unchanged = asset.unchanged.hashes
let changed = toseq(
 asset.sinks.g
  \ unchanged
  \ asset.[{filename (builddir+" orgstdlib.lib"),} filename(builddir + "shell.lib")]
)
let outdated = reachable(complement.g, changed) \ asset.changed
{relink changed}
for changelist = "", n ∈ changed
do if name.n ∈ "define shell" then changelist else changelist + fullname.n
for unchangelist = "", n ∈ toseq.unchanged
do if name.n ∈ "define shell" then unchangelist else unchangelist + fullname.n
let acc2 = "set /sp-e
/br#relink changed files
/br changelist /tag =^(dq.changelist)
/br unchangelist /tag =^(dq.unchangelist)
/br if [[/sp-z $makehash /sp]] ; then
/br checksrc $changelist"
for acc = acc2 + "/br#remove outdated files", dated ∈ toseq.outdated
do acc + "/br rm /sp-f" + fullname.dated
let subg = subgraph(g, outdated),
if debug then
 for debugtxt = "", a ∈ {r} toseq.arcs.subg do debugtxt + "+^(tail.a)+^(head.a)",
 debugtxt
else
 for cmds = "", l ∈ toseq.allfile
 do
  if 1#line.l ∈ "define" then
   let cmd = 2#line.l
   let exe = 3#line.l
   let rest = if n.line.l < 4 then [cmd] else line.l << 3,
    cmds
     + "
    /br function^(cmd) {
    /br /tag built/^(exe).lib^(rest) $@
    /br if [/sp-e error.html /sp] ; then
    /br $tauopen error.html
    /br exit 1
    /br fi
    /br}"
  else cmds,
 createorder(subg, allfile, acc + cmds) + "/br fi"

Function makeScript2(
 input:seq.file
 , builddir:seq.word
 , hashes:seq.file
 , o:seq.word
) seq.file
{COMMAND /strong makeScript creates shell script for building code
/br The first file of hashes is a new file of shahash of the input files.The second file should
be the result of the last run of makeScript. The output of makeScript2 will include the hashes in
the first file of hashes.Thus identical lines in the hashes files will be the list of first the
have not changed between runs. }
let txtbytes = toseqbyte.textformat."if [[/sp-n true /sp]] ; then
/br^(makeScriptCore(input, builddir, false, hashes))
/br else
/br shahash of source files
/br"
let databytes = if isempty.hashes then empty:seq.byte else data.1#hashes
let fn = filename.o,
[file(fn, txtbytes + tobyte.10 + databytes + toseqbyte.textformat."/br fi")]

use set.arc.filename

function fullnames(s:seq.filename) seq.word for acc = "", fn ∈ s do acc + fullname.fn, acc

function buildgraph(input:set.lineinfo) seq.arc.filename
for acc = empty:seq.arc.filename, line ∈ toseq.input
do
 let cmd = 1#line.line
 let tail = 1#output.line,
  if cmd ∈ "shell define" then
  for arcs = acc, fn ∈ input.line do arcs + arc(tail, fn), arcs
  else if ext.tail ∈ "lib" then
   let tail1 = changeext(tail, "bc")
   for arcs = acc, fn ∈ input.line do arcs + arc(tail1, fn),
    arcs
     + arc(tail, filename."^(cmd).cmd")
     + arc(changeext(tail, "libsrc"), tail)
     + arc(changeext(tail, "libinfo"), tail)
     + arc(tail, tail1)
  else
   for arcs = acc, fn ∈ input.line do arcs + arc(tail, fn),
   arcs + arc(tail, filename."^(cmd).cmd"),
acc

function createorder(g:graph.filename, defs:set.lineinfo, out:seq.word) seq.word
assert true report for acc = "", l ∈ toseq.defs do acc + "/p" + line.l, acc
let sinks = sinks.g,
if isempty.sinks then
assert isempty.nodes.g report "cycle in graph", out
else
 for txt = out, p ∈ if isempty.sinks then toseq.nodes.g else sinks
 do
  let b = lookup(defs, lineinfo([p], empty:seq.filename, "")),
   if isempty.b then
   txt
   else
    txt
     + 
     if 1#line.1#b ∈ "define" then
     ""
     else if 1#line.1#b ∈ "shell" then
      "/br^(2#line.1#b)"
       + line.1#b << 2
       + fullnames.input.1#b
       + ">"
       + fullnames.output.1#b
     else
      "/br echo making^(1#output.1#b) /br^(1#line.1#b)"
       + fullnames.input.1#b
       + line.1#b << 1
       + "o ="
       + fullnames.output.1#b,
 createorder(
  subgraph(g, nodes.g \ asset.sinks)
  , defs
  , txt + "/br#-------------------------------"
 )

Function >1(a:UTF8, b:UTF8) ordering toseqbyte.a >1 toseqbyte.b

Function >1(a:filename, b:filename) ordering
alphaword.name.a >1 alphaword.name.b
 ∧ alphaword.ext.a >1 alphaword.ext.b
 ∧ alphaword.dirpath.a >1 alphaword.dirpath.b

Function >1(a:byte, b:byte) ordering toint.a >1 toint.b 