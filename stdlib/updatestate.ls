Module updatestate

use set.cmdpara

use file

use seq.file

use seq.arc.filename

use graph.filename

use seq.filename

use set.filename

use standard

use textio

use otherseq.word

use words

Function prettystate(input:seq.file)seq.file
for acc = "", a ∈ breakparagraph.data.first.input do
 for txt = "", have = "", p ∈ a do
  if p ∈ have then
   next(if p ∈ "+"then txt + " /br+"else txt >> 1 + " /br" + last.txt + p
   , have
   )
  else next(txt + p, if p ∈ "+="then have + p else have)
 /for(acc + " /p" + txt)
/for([file("try2.txt", acc)])

Function updatestate(input:seq.file, o:seq.word)seq.file
let allfile = for acc = empty:seq.seq.word, f ∈ input do acc + breakparagraph.data.f /for(acc)
for acc = empty:seq.arc.filename, defs2 = empty:set.cmdpara, cmds = "", aa ∈ allfile do
 if first.aa ∈ "-"then next(acc, defs2, cmds)
 else if first.aa ∈ ":"then next(acc, defs2, cmds + aa)
 else
  let cmd0 = first.aa
  let cidx = findindex(cmd0, cmds)
  assert subseq(cmds, cidx - 1, cidx) = ":" + cmd0 report"unknown cmd" + cmd0 + aa
  let cmd = 
   cmds
   _if subseq(cmds + ":", cidx + 3, cidx + 3) = ":"then cidx + 2 else cidx
  let cmdlib = subseq(cmds, cidx + 1, cidx + 1) + ".lib"
  let idx = findindex("="_1, aa + "?=")
  let rest = if idx > length.aa then""else aa << (idx - 2)
  let filenames = 
   getfilenames("built", subseq(aa, 2, 4) + cmdlib + subseq(aa, 5, length.aa - length.rest + 3))
  let tail = first.filenames
  next(for arcs = acc, fn ∈ filenames << 1 do arcs + arc(tail, fn)/for(if cmd ∈ "makelib"then
   arcs + arc(changeext(tail, "libsrc"), tail)
   + arc(changeext(tail, "libinfo"), tail)
  else arcs /if)
  , defs2 + cmdpara(tail, filenames << 1, rest, cmd)
  , cmds
  )
/for({let g=newgraph.acc HTMLformat.drawgraph(toseq.arcs(subgraph(g, nodes.g \ asset.sinks.g)), empty:set.word, empty 
:set.word)}
let g = newgraph.acc
let sinks = sinks.g
let scriptstart = 
 for acc2 = "set $([space])-e", n ∈ sinks do
  if dirpath.n = "built"then acc2 else acc2 + " /br checksrc" + fullname.n
 /for(acc2)
let out = createorder(subgraph(g, nodes.g \ asset.sinks), defs2, scriptstart)
[file(filename.o, out)])

function createorder(g:graph.filename, defs:set.cmdpara, out:seq.word)seq.word
let sinks = sinks.g
if isempty.sinks then
 assert isempty.nodes.g report"cycle in graph"
 out
else
 for txt = out, p ∈ if isempty.sinks then toseq.nodes.g else sinks do txt + tosetvars(defs, p)/for(createorder(subgraph(g, nodes.g \ asset.sinks), defs, txt + " /br #________________"))

function ?(a:filename, b:filename)ordering
alphaword.name.a ? alphaword.name.b ∧ alphaword.ext.a ? alphaword.ext.b
∧ toalphaseq.dirpath.a ? toalphaseq.dirpath.b

function print(filenames:seq.filename)seq.word
for f2 = "", n ∈ filenames do f2 + fullname.n /for(f2)

function tosetvars(defs2:set.cmdpara, fn:filename)seq.word
let node = fullname.fn
let cmdpara = lookup(defs2, cmdpara(fn, empty:seq.filename, empty:seq.word, first."noop"))
if isempty.cmdpara then""
else
 let parts = print.parts.cmdpara_1
 let lib = [name.first.parts.cmdpara_1]
 let cmd = cmd.cmdpara_1
 if cmd ∈ "makelib"then
  let B = extractValue(data.cmdpara_1, "uses")
  for depends = ""
  , libinfo = ""
  , ccode = "void init_libs(){"
  , u ∈ reverse.B
  do
   next(depends + fullname.filename([u] + ".$libtype")
   , libinfo + fullname.filename([u] + ".libinfo")
   , "void init_$([u])(); $(ccode)init_$([u])();"
   )
  /for(let out = [name.fn, "."_1, "libsrc"_1]
  " /p parts3=$(dq(parts << 1))
 /br dependsOn=$(dq("$parts3" + first.parts))
 /br libsrcargs=$(dq."$(lib)libsrc $parts3 $(data.cmdpara_1)o=$(out)")
 /br compileargs=$(dq(lib + "makebitcode" + fullname.filename.out + libinfo))
 /br dependlibs=$(dq.depends)
 /br ccode=$(dq.ccode)
 /br makelibrary $([name.fn])")
 else
  " /p node=$(dq.[node])
 /br parts3=$(dq(parts << 1))
 /br dependsOn=$(dq("$parts3" + first.parts))
 /br libexeAll $(lib + cmd)$parts3 $(data.cmdpara_1 + "o=$([name.fn, "."_1, ext.fn])")"

type cmdpara is fn:filename, parts:seq.filename, data:seq.word, cmd:word

function ?(a:cmdpara, b:cmdpara)ordering fn.a ? fn.b 