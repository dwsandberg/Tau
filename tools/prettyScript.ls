Module prettyScript

Implement /em prettyScript command.

use file

use seq1.filename

use makescript

use standard

use svg

use arc.word

use drawGraph.arc.word

use graph.arc.word

use set.arc.word

use seq1.seq.word

use seq1.word

use set.word

Function prettyScript(
input:seq.file
, builddir:seq.word
, hashes:seq.file
, roots:seq.word
, %:seq.word
) seq.word
{COMMAND prettyScript /strong pretty prints /sp.bld script./br
% /strong format of output. // /br
pretty /strong ? /br
full /strong Graph of dependences between files./br
outdated /strong like full but only include outdated files in graph /br
script /strong shell script for updating without the file hashes. /block /p
options used for formats other than pretty./br
roots /strong only include the filenames list and their descendants in graph. /br
hashes /strong ? /br
builddir /strong build target directory. Defaults to"+built"}
let format = (if isempty.% then "pretty" else %) sub 1,
if format ∈ "pretty" then pretty.input
else
 let txt =
  makeScriptCore(input, if isempty.builddir then "+built" else builddir, format, hashes),
 if format ∈ "script" then txt
 else
  let asfn = tofilenames.txt
  for acc = empty:seq.arc.word, tail = false, last = asfn sub 1, fn ∈ asfn
  do next(if tail then acc + arc(fullname.last, fullname.fn) else acc, not.tail, fn)
  let g2 = newgraph.acc,
  let g3 =
   if isempty.roots then g2 else subgraph(g2, reachable(g2, fullnames.tofilenames.roots)),
  drawgraph(toseq.arcs.g3, empty:set.word, empty:set.word)

______________

function width(w:word) int if w ∈ ".+" then 1 else n.decodeword.w + 1

Function pretty(input:seq.file) seq.word
for acc = "", l ∈ breakparagraph.input
do
 if subseq(l, 1, 2) = "# File" then acc
 else if subseq(l, 1, 1) ∈ ["#", "define"] then acc + l + "/p"
 else
  for all = empty:seq.seq.word, part = "", width = 0, last = l sub 1, w ∈ l << 1
  do
   if width > 90 ∧ last ∉ "."
   ∨ last ∈ "+" ∧ not.isempty.part ∧ part sub n.part ∉ ":: "
   ∨ w ∈ ":: " then next(all + part, [last], width.last, w)
   else next(all, part + last, width + width.last, w)
  let all1 = all + (part + last)
  let all2 =
   if n.all1 sub 1 = 1 then all1 sub 1 + %("/br", all1 << 1) >> 1
   else %("/br", all1) >> 1,
  let txt =
   if subseq(all2, 2, 2) = "+" then %.all2 sub 1 + "/sp" + all2 << 1 else all2,
  acc + txt + "/p",
acc 