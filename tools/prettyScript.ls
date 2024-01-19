Module prettyScript

Implement /em prettyScript command.

use file

use otherseq.filename

use makescript

use newsvg

use standard

use set.arc.word

use graph.word

use otherseq.word

use otherseq.seq.word

use set.word

Function prettyScript(
input:seq.file
, builddir:seq.word
, hashes:seq.file
, roots:seq.word
, %:seq.word
) seq.word
{COMMAND /strong prettyScript pretty prints /sp.bld script.
/br /strong % format of output. <* block
/br /strong pretty ?
/br /strong full Graph of dependences between files.
/br /strong outdated like full but only include outdated files in graph
/br /strong script shell script for updating without the file hashes. *>
/p options used for formats other than pretty.
/br /strong roots only include the filenames list and their descendants in graph. 
/br /strong hashes ?
/br /strong builddir build target directory. Defaults to"+built"}
let format = 1#(if isempty.% then "pretty" else %),
if format ∈ "pretty" then pretty.input
else
 let txt = makeScriptCore(input, if isempty.builddir then "+built" else builddir, format, hashes),
 if format ∈ "script" then txt
 else
  let asfn = tofilenames.txt
  for acc = empty:seq.arc.word, tail = false, last = 1#asfn, fn ∈ asfn
  do next(if tail then acc + arc(fullname.last, fullname.fn) else acc, not.tail, fn)
  let g2 = newgraph.acc,
  let g3 = if isempty.roots then g2 else subgraph(g2, reachable(g2, fullnames.tofilenames.roots)),
  drawgraph(toseq.arcs.g3, empty:set.word, empty:set.word)

______________

function width(w:word) int if w ∈ ".+" then 1 else n.decodeword.w + 1

Function pretty(input:seq.file) seq.word
for acc = "", l ∈ breakparagraph.input
do
 if subseq(l, 1, 2) = "#File" then acc
 else if subseq(l, 1, 1) ∈ ["#", "define"] then acc + l + "/p"
 else
  for all = empty:seq.seq.word, part = "", width = 0, last = 1#l, w ∈ l << 1
  do
   if width > 90 ∧ last ∉ "." ∨ last ∈ "+" ∧ not.isempty.part ∧ 1^part ∉ ":: " ∨ w ∈ ":: " then next(all + part, [last], width.last, w)
   else next(all, part + last, width + width.last, w)
  let all1 = all + (part + last)
  let all2 = if n.1#all1 = 1 then 1#all1 + %("/br", all1 << 1) >> 1 else %("/br", all1) >> 1,
  let txt = if subseq(all2, 2, 2) = "+" then %.1#all2 + "/sp" + all2 << 1 else all2,
  acc + txt + "/p",
acc 