#!/usr/local/bin/tau ; use tools; testprofile."solardataall"

/run profile dumpprofileinfo

run tools testprofile

Module profile

Problems:Junk at top of graph

Max space seems to be on node with head and tail blank!

use displaytextgraph

use libdesc

use mangle

use standard

use words

use otherseq.alphaword

use seq.alphaword

use seq.int

use seq.liblib

use labeledgraph.parc

use seq.parc

use set.parc

use otherseq.word

use seq.word

use seq.seq.word

use svggraph.seq.word

use seq.arcinfo.seq.word

use seq.seq.seq.word

* To profile a function add a use clause"use options.<return type of /function >"and change /function so body is wrap by a call to PROFILE(<body>). Multiple procedures can be profiled at the same time. After the part of code of interest add a call to profileresults("time")to optain the result.

* Profiling is accomplished by adding code to perform measurements before and after each procedure call and recording the difference.

function toarcinfo(measure:seq.word, max:int, map:nodemap, a:parc)arcinfo.seq.word
 let label = toword(
 (if measure = "time"then clocks.a
 else if measure = "count"then counts.a else space.a ) * 100
 / max
 )
  arcinfo(shorten(map, head.a), shorten(map, tail.a), [ label])

Function profileresults(measure:seq.word)seq.word
 \\ Returns label graph of profile results. Measure is time, count, or space. \\
 \\ let g = profileresults \\
 let g = for acc = empty:labeledgraph.parc, @e = for acc = empty:seq.parc, @e = loadedLibs do acc + profiledata.@e end(acc)do
  acc + @e
 end(acc)
 let m = if measure = "time"then
 for acc = 0, @e = toseq.arcs.g do max(acc, clocks.@e)end(acc)
 else if measure = "count"then
 for acc = 0, @e = toseq.arcs.g do max(acc, counts.@e)end(acc)
 else
  assert measure = "space"report"unknown profile measure"
   for acc = 0, @e = toseq.arcs.g do max(acc, space.@e)end(acc)
 let g3 = removesmall(g, measure, m)
  \\ shorten the names of the functions and then build and display labeled graph \\
  let nodemap = shorten.for acc ="", @e = toseq.nodes.g3 do acc + head.@e end(acc)
  let z2 = for acc = empty:seq.arcinfo.seq.word, @e = toseq.arcs.g3 do
   acc + toarcinfo(measure, m, nodemap, @e)
  end(acc)
   " &br" + measure + toword.m + " &br" + display.z2 + " &br"
   + measure
   + toword.m

function removesmall(g:labeledgraph.parc, measure:seq.word, m:int)labeledgraph.parc
let g2 = if measure = "time"then
for acc = g, @e = toseq.nodes.g do removesmallclocks(acc, m / 100, @e)end(acc)
else if measure = "space"then
for acc = g, @e = toseq.nodes.g do removesmallspace(acc, m / 100, @e)end(acc)
else
 for acc = g, @e = toseq.nodes.g do removesmallcount(acc, m / 100, @e)end(acc)
 if cardinality.arcs.g = cardinality.arcs.g2 then g2 else removesmall(g2, measure, m)

function removesmallclocks(g:labeledgraph.parc, limit:int, node:parc)labeledgraph.parc
 if cardinality.arcstosuccessors(g, node) = 0 then
 if for acc = 0, @e = toseq.backarcstopredecessors(g, node)do acc + clocks.@e end(acc) < limit then
  deletenode(g, node)
  else g
 else g

function removesmallspace(g:labeledgraph.parc, limit:int, node:parc)labeledgraph.parc
 if cardinality.arcstosuccessors(g, node) = 0 then
 if for acc = 0, @e = toseq.backarcstopredecessors(g, node)do acc + space.@e end(acc) < limit then
  deletenode(g, node)
  else g
 else g

function removesmallcount(g:labeledgraph.parc, limit:int, node:parc)labeledgraph.parc
 if cardinality.arcstosuccessors(g, node) = 0 then
 if for acc = 0, @e = toseq.backarcstopredecessors(g, node)do acc + counts.@e end(acc) < limit then
  assert false report [ head.node]
    deletenode(g, node)
  else g
 else g

Function shorten(pnodes:seq.word)nodemap
 \\ This procedure produces a map that takes fsigs and shortens them keeping them distinct. The following procedure uses this result to map the figs to the new ones. \\
 let nodes = sort.toalphaseq.pnodes
 let c = for acc = [ empty:seq.seq.word], @e = towordseq.nodes do acc + codedown.@e end(acc)
 + [ empty:seq.seq.word]
 let short = for acc = empty:seq.seq.word, @e = arithseq(length.c - 2, 1, 2)do acc + shorten(c, @e)end(acc)
  nodemap(nodes, short)

Function shorten(map:nodemap, w:word)seq.word(short.map)_binarysearch(org.map, alphaword.w)

type nodemap is  org:seq.alphaword, short:seq.seq.word

function shorten(a:seq.seq.seq.word, i:int)seq.word
 let j = max(differ(a_(i - 1), a_i, 1), differ(a_i, a_(i + 1), 1))
  if j = 1 then a_i_1
  else
   let z = for acc = empty:seq.seq.word, @e = subseq(a_i, 1, j)do acc + formattype.@e end(acc)
    z_1 + ":" + z_2 + "("
    + for acc ="", @e = subseq(z, 2, length.z)do list(acc,",", @e)end(acc)
    + ")"

function formattype(a:seq.word)seq.word
 reverse.for acc ="", @e = a do list(acc,".", [ @e])end(acc)

function differ(a:seq.seq.word, b:seq.seq.word, i:int)int
 if i > length.a ∨ i > length.b then i
 else if a_i = b_i then differ(a, b, i + 1)else i

Export head(parc)word

Export tail(parc)word

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

function ?(a:parc, b:parc)ordering head.a ? head.b ∧ tail.a ? tail.b

function ?2(a:parc, b:parc)ordering head.a ? head.b

function reverse(a:parc)parc parc(tail.a, head.a, counts.a, clocks.a, space.a)

function tonode(a:parc)parc parc(head.a, head.a, counts.a, clocks.a, space.a)

Function dumpprofileinfo seq.word
let e = profiledata.loadedLibs_1
 for acc ="", @e = profiledata.loadedLibs_1 do list(acc," &br", [ tail.@e, head.@e, toword.counts.@e])end(acc)