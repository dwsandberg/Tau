Module updatestate

use UTF8

use seq.UTF8

use set.UTF8

use bits

use otherseq.byte

use seq.seq.byte

use set.cmdpara

use set.defines

use file

use seq.file

use seq.arc.filename

use graph.filename

use otherseq.filename

use seq.filename

use set.filename

use standard

use textio

use otherseq.word

use words

function >1(a:UTF8, b:UTF8)ordering toseqbyte.a >1 toseqbyte.b

function >1(a:byte, b:byte)ordering toint.a >1 toint.b

Function prettystate(input:seq.file, o:seq.word)seq.file
for acc = "", a ∈ breakparagraph.data.first.input do
 if subseq(a, 1, 1) ∈ ["-", "comment"]then acc + " /p comment" + a << 1
 else if subseq(a, 1, 1) ∈ [":", "define"]then
  for txt = "", w ∈ a do
   if w ∈ "define:" ∧ not.isempty.txt then txt + " /br define"else txt + w
  /for(acc + " /p define" + txt << 1)
 else
  for txt = "", have = "", lastbreak = 0, p ∈ a do
   if p ∈ "+="then
    next(if p ∈ "+"then txt + " /br+"else txt >> 1 + " /br" + last.txt + p
    , have
    , 0
    )
   else
    let addbreak = lastbreak > 10 ∧ last.txt ∈ "."
    next(if addbreak then txt + " /br" + space + p else txt + p
    , if p ∈ "+="then have + p else have
    , if addbreak then 0 else lastbreak + 1
    )
  /for(acc + " /p" + txt)
/for([file(o, acc)])

type defines is name:word, lib:word, cmds:seq.word

function cmd(a:defines)word first.cmds.a

function >1(a:defines, b:defines)ordering name.a >1 name.b

type result is arcs:seq.arc.filename, defs2:set.cmdpara

function tofilename(u:UTF8)filename
let t = break(tobyte.toint.{first.decodeword.first}char1."/", toseqbyte.u)
{if isempty.t then filename("Z.ls")else}
filename(if length.t > 1 then"+" + towords.UTF8(toseqbyte.u >> (length.last.t + 1))
else"+.ls"/if
+ towords.UTF8.last.t)

function substitute(s:seq.word, b:seq.word, replacement:seq.word)seq.word
let i = findindex(s, last.b)
if i > length.s then s
else if subseq(s, i - length.b + 1, i) = b then
 subseq(s, 1, i - length.b) + replacement + substitute(s << i, b, replacement)
else subseq(s, 1, i) + substitute(s << i, b, replacement)

Function updatestate2(input:seq.file, o:seq.word, builddir:seq.word)seq.file
let lines = toseq(asset.breaklines.data.first.input ∩ asset.breaklines.data.input_2)
let unchanged = 
 if isempty.lines then empty:seq.filename
 else
  let i = findindex(toseqbyte.first.lines, tobyte.32)
  for txt = empty:seq.filename, line ∈ lines do
   txt + tofilename.UTF8(toseqbyte.line << (2 + i + length.decodeword.first."./"))
  /for(txt)
let r = buildgraph(input << 2, builddir)
let g = newgraph.arcs.r
let changed = 
 toseq(asset.sinks.g \ asset.unchanged
 \ asset.[filename(builddir + "orgstdlib.lib"), filename(builddir + "shell.lib")])
let outdated = reachable(complement.g, changed) \ asset.changed
{relink changed}
let out = 
 for acc2 = "set $([space])-e  /br # relink changed files", n ∈ changed do
  if name.n ∈ "shell"then acc2 else acc2 + " /br checksrc" + fullname.n
 /for(
  for acc = acc2 + " /br # remove outdated files", dated ∈ toseq.outdated do
   acc + " /br rm $([space])-f" + fullname.dated
  /for(createorder(subgraph(g, outdated), defs2.r, acc)))
[file(o, out)
, file("+tmp changed.html", %.changed)
, file("+tmp unchanged.html", %.unchanged)
, file("+tmp sinks.html", %.sinks.g)
]

function buildgraph(inputs:seq.file, builddir:seq.word)result
let allfile = 
 for acc = empty:seq.seq.word, f ∈ inputs do acc + breakparagraph.data.f /for(acc)
for acc = empty:seq.arc.filename, defs2 = empty:set.cmdpara, defines = empty:set.defines, aaa ∈ allfile do
 let aa = substitute(aaa, "+$build", builddir)
 if first.aa ∈ "comment"then next(acc, defs2, defines)
 else if first.aa ∈ "define"then
  next(acc
  , defs2
  , for newcmds = defines, cmd = "", w ∈ aa << 1 + "define"do
   if w ∈ "define"then
    {defines x lib}
    if length.cmd = 2 then next(newcmds + defines(cmd_1, cmd_2, [cmd_1]), "")
    else next(newcmds + defines(cmd_1, cmd_2, cmd << 2), "")
   else next(newcmds, cmd + w)
  /for(newcmds)
  )
 else
  let cmd0 = first.aa
  let bb = lookup(defines, defines(cmd0, cmd0, ""))
  assert not.isempty.bb report"command \em" + aa + "is not defined"
  let cmd = cmd.bb_1
  let cmdlib = [lib.bb_1] + ".lib"
  let idx = findindex(aa + "?=", "="_1)
  let rest = if idx > length.aa then""else aa << (idx - 2)
  let tmp2 = getfilenames(builddir + cmdlib + subseq(aa, 2, length.aa - length.rest + 3))
  let tail = tmp2_2
  let filenames = [tmp2_1] + tmp2 << 2
  next(for arcs = acc, fn ∈ filenames do
   arcs + arc(tail, fn)
  /for(
   if cmd ∈ "makelib"then
    arcs + arc(changeext(tail, "libsrc"), tail)
    + arc(changeext(tail, "libinfo"), tail)
   else arcs)
  , defs2 + cmdpara(tail, filenames, rest, bb_1)
  , defines
  )
/for(result(acc, defs2))

function createorder(g:graph.filename, defs:set.cmdpara, out:seq.word)seq.word
let sinks = sinks.g
if isempty.sinks then
 assert isempty.nodes.g report"cycle in graph"
 out
else
 for txt = out, p ∈ if isempty.sinks then toseq.nodes.g else sinks do
  let cmdpara = 
   lookup(defs
   , cmdpara(p
   , empty:seq.filename
   , empty:seq.word
   , defines("noop"_1, "noop"_1, "")
   )
   )
  if isempty.cmdpara then txt else txt + tosetvars(cmdpara_1, p)
 /for(createorder(subgraph(g, nodes.g \ asset.sinks), defs, txt + " /br #________________"))

Function >1(a:filename, b:filename)ordering
alphaword.name.a >1 alphaword.name.b ∧ alphaword.ext.a >1 alphaword.ext.b
∧ toalphaseq.dirpath.a >1 toalphaseq.dirpath.b

function print(filenames:seq.filename)seq.word
for f2 = "", n ∈ filenames do f2 + fullname.n /for(f2)

function tosetvars(cmdpara:cmdpara, fn:filename)seq.word
let node = fullname.fn
let parts = print.parts.cmdpara
let cmd = cmd.cmdpara
if lib.cmd ∈ "shell"then" /br" + cmds.cmd + parts << 1 + ">" + node
else if cmds.cmd = "makelib"then
 for depends = ""
 , libinfo = ""
 , ccode = "void init_libs(){"
 , u ∈ reverse.extractValue(data.cmdpara, "uses")
 do
  next(depends + fullname.filename."+$build $([u]).$libtype"
  , if isempty.libinfo then[u] + ".libinfo"else libinfo + u
  , "void init_$([u])(); $(ccode)init_$([u])();"
  )
 /for(
  let out = changeext(fn, "libsrc")
  {???? if para is placed inline an error is created when transformed
    /br libsrcargs=$(dq."$([lib.cmd])libsrc $parts3 $(data.cmdpara)o=$(para)"}
  let para = "+" + dirpath.out + name.out + ".libsrc"
  "
    /p #makelibrary $([name.fn])
    /br libexe $([lib.cmd])libsrc $(parts << 1)$(data.cmdpara)o=$(para)
    /br libexe $([lib.cmd])makebitcode+$build $([name.out] + "." + ext.out + libinfo
  )
    /br dependlibs=$(dq.depends)
    /br ccode=$(dq.ccode)
    /br linklibrary $([name.fn])")
else
 "
   /p # $(dq.[node])
   /br libexe $([lib.cmd] + cmds.cmd)$(parts << 1)$(data.cmdpara
 + "o=
  $("+" + dirpath.fn + [name.fn, "."_1, ext.fn])")"

type cmdpara is fn:filename, parts:seq.filename, data:seq.word, cmd:defines

function >1(a:cmdpara, b:cmdpara)ordering fn.a >1 fn.b 