Module simple

use UTF8

use bits

use file

use format

use standard

use textio

use words

use seq.byte

use seq.char

use set.cmdpara

use seq.file

use graph.filename

use otherseq.filename

use seq.filename

use set.filename

use otherseq.word

use set.word

use seq.arc.filename

use set.arc.filename

use seq.seq.filename

use otherseq.seq.word

use seq.seq.word

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

Function updatestate(input:seq.file, roots:seq.word, o:seq.word)seq.file
for acc = empty:seq.arc.filename
, defs2 = empty:set.cmdpara
, cmds = ""
, defined = empty:set.filename
, aa ∈ breakparagraph.data.first.input
do
 if first.aa ∈ "-"then next(acc, defs2, cmds, defined)
 else if first.aa ∈ ":"then next(acc, defs2, cmds + aa, defined)
 else
  let k = 1
  let cmd0 = aa_k
  let cidx = findindex(cmd0, cmds)
  assert subseq(cmds, cidx - 1, cidx) = ":" + cmd0 report"unknown cmd" + cmd0 + aa
  let cmd = 
   cmds_if subseq(cmds, cidx + 3, cidx + 3) = ":"then cidx + 2 else cidx
  let cmdlib = subseq(cmds, cidx + 1, cidx + 1) + ".lib"
  let idx = findindex("="_1, aa + "?=")
  let rest = 
   "cmd=" + cmd
   + if idx > length.aa then""else aa << (idx - 2)
  let filenames = 
   getfilenames("built", subseq(aa, 2, 4) + cmdlib + subseq(aa, 5, length.aa - length.rest + 3))
  let tail = first.filenames
  next(for arcs = acc, fn ∈ filenames << 1 do arcs + arc(tail, fn)/for(if cmd ∈ "makelib orgmakelib"then arcs + arc(tail, changeext(tail, "libsrc"))
  else arcs /if)
  , if cmd ∈ "makelib orgmakelib"then
   defs2 + cmdpara(changeext(tail, "libsrc"), [tail], "cmd=noop")
  else defs2 /if
  + cmdpara(tail, filenames << 1, rest)
  , cmds
  , if cmd ∈ "makelib orgmakelib"then defined + tail + changeext(tail, "libsrc")
  else defined + tail
  )
/for({let g=newgraph.acc HTMLformat.drawgraph(toseq.arcs(subgraph(g, nodes.g \ asset.sinks.g)), empty:set.word, empty 
:set.word))}
let g = 
 if isempty.roots then newgraph.acc
 else
  let g = newgraph.acc
  for rootfiles = empty:seq.filename, n ∈ toseq.nodes.g do
   if name.n ∈ roots then rootfiles + n else rootfiles
  /for(subgraph(g, reachable(g, rootfiles)))
let scriptstart = 
 for acc2 = "set $(sp)-e  /br if $(sp)[[$(sp)$1 $(sp)==$(sp + dq."-n" + sp)]]; $(sp)then  /br norun=true  /br fi  /br source bin/tauconfig.sh"
 , n ∈ toseq(nodes.g \ defined \ asset.[filename."orgstdlib.lib"])
 do
  acc2 + " /br checksrc" + fullname.n
 /for(acc2)
let g2 = for g2 = g, n ∈ sources.g do g2 + arc(filename."#.#", n)/for(g2)
{let out=outgraph.deletenode(g2, filename("orgstdlib.lib"))[file(filename(o), out)])}
let out = 
 createorder(deletenode(g2, filename."orgstdlib.lib"), defs2, scriptstart)
 + " /br mkbuild"
[file(filename.o, out)])

function outgraph(g2:graph.filename)seq.word
for out = "", n ∈ toseq.nodes.g2 do
 if ext.n ∈ "ls"then out
 else
  out + " /br" + toword.cardinality.predecessors(g2, n) + fullname.n
  + for suc = "", s ∈ toseq.successors(g2, n)do if ext.s ∈ "ls"then suc else suc + fullname.s /for(suc)
/for(out)

function createorder(g:graph.filename, defs:set.cmdpara, out:seq.word)seq.word
let sinks = sinks.g
let txt = 
 for txt = out, p ∈ if isempty.sinks then toseq.nodes.g else sinks do txt + tosetvars(defs, p)/for(txt)
if isempty.sinks then txt
else createorder(subgraph(g, nodes.g \ asset.sinks), defs, txt + " /br #________________")

function ?(a:filename, b:filename)ordering
alphaword.name.a ? alphaword.name.b ∧ alphaword.ext.a ? alphaword.ext.b
∧ toalphaseq.dirpath.a ? toalphaseq.dirpath.b

function print(filenames:seq.filename)seq.word
for f2 = "", n ∈ filenames do f2 + fullname.n /for(f2)

function tosetvars(defs2:set.cmdpara, fn:filename)seq.word
let node = fullname.fn
let cmdpara = lookup(defs2, cmdpara(fn, empty:seq.filename, empty:seq.word))
if isempty.cmdpara then""
else
 let parts = print.parts.cmdpara_1
 let cmd = extractValue(data.cmdpara_1, "cmd")
 if cmd = "noop"then""
 else
  let xxx = [name.first.parts.cmdpara_1]
  if cmd ∈ ["makelib", "orgmakelib"]then
   let A = finddependentlibs(defs2, name.fn)
   for depends = "", ccode = "void init_libs(){", u ∈ reverse.A >> 1 do
    next(depends + fullname.filename([u] + ".$libtype")
    , "void init_$([u])(); $(ccode)init_$([u])();"
    )
   /for(let baselib = subseq(A + "stdlib", 2, 2)
   let out = [name.fn, "."_1, "libsrc"_1]
   " /p parts=$(dq([node] + parts)) /br dependlibs=$(dq.depends) /br ccode=$(dq.ccode) /br outofdate ||(libexe $(xxx)libsrc $(parts << 1)$(data.cmdpara_1 << 3)o=$(out) /br libexe $(baselib)$(baselib)$([fullname.filename.out]);runlib $([name.fn]))")
  else
   " /p parts=$(dq([node] + parts)) /br outofdate ||(libexe $(xxx)$(cmd)$(parts << 1)$(data.cmdpara_1 + "o=$([name.fn, "."_1, ext.fn])"))"

function finddependentlibs(defs:set.cmdpara, lib:word)seq.word
if lib ∈ "stdlib orgstdlib"then[lib]
else
 {let cmdpara=for cmdpara=empty:set.cmdpara, ext /in"libsrc lib"while isempty.cmdpara do lookup(defs, cmdpara(filename 
("$([lib])."+ext), empty:seq.filename, empty:seq.word))/for(cmdpara)}
 let cmdpara = 
  lookup(defs
  , cmdpara(filename("$([lib])." + "lib"), empty:seq.filename, empty:seq.word)
  )
 assert not.isempty.cmdpara report"dep" + lib
 let libs = 
  for libs = empty:seq.filename, s ∈ parts.cmdpara_1 do if ext.s ∈ "lib"then libs + s else libs /for(libs)
 if isempty.libs then[lib]else[lib] + finddependentlibs(defs, name.last.libs)

function sp seq.word[space]

type cmdpara is fn:filename, parts:seq.filename, data:seq.word

function ?(a:cmdpara, b:cmdpara)ordering fn.a ? fn.b 