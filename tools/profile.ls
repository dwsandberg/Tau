#!/usr/local/bin/tau

/run profile dumpprofileinfo

run tools testprofile

Module profile

Problems:Junk at top of graph

Max space seems to be on node with head and tail blank!

use otherseq.alphaword

use seq.alphaword

use displaytextgraph

use seq.int

use libdesc

use seq.liblib

use mangle

use labeledgraph.parc

use seq.parc

use set.parc

use stdlib

use otherseq.word

use seq.arcinfo.seq.word

use seq.seq.seq.word

use seq.seq.word

use svggraph.seq.word

use seq.word

use words

* To profile a function add a use clause"use options.<return type of /function >"and change /function so body is wrap by a call to PROFILE(<body>). Multiple procedures can be profiled at the same time. After the part of code of interest add a call to profileresults("time")to optain the result.

* Profiling is accomplished by adding code to perform measurements before and after each procedure call and recording the difference.

function toarcinfo(measure:seq.word, max:int, map:nodemap, a:parc)arcinfo.seq.word
 let label = toword((if measure = "time"then clocks.a else if measure = "count"then counts.a else space.a)
 * 100
 / max)
  arcinfo(shorten(map, head.a), shorten(map, tail.a), [ label])

Function profileresults(measure:seq.word)seq.word
 // Returns label graph of profile results. Measure is time, count, or space. //
 // let g = profileresults //
 let g =(loadedlibs @@ +(empty:seq.parc, profiledata.@e))@@ +(empty:labeledgraph.parc, @e)
 let m = if measure = "time"then(toseq.arcs.g)@@ max(0, clocks.@e)
 else if measure = "count"then(toseq.arcs.g)@@ max(0, counts.@e)
 else
  assert measure = "space"report"unknown profile measure"
   toseq.arcs.g @@ max(0, space.@e)
 let g3 = removesmall(g, measure, m)
  // shorten the names of the functions and then build and display labeled graph //
  let nodemap = shorten((toseq.nodes.g3)@@ +("", head.@e))
  let z2 =(toseq.arcs.g3)@@ +(empty:seq.arcinfo.seq.word, toarcinfo(measure, m, nodemap, @e))
   " &br" + measure + toword.m + " &br" + display.z2 + " &br"
   + measure
   + toword.m

function removesmall(g:labeledgraph.parc, measure:seq.word, m:int)labeledgraph.parc
 let g2 = if measure = "time"then toseq.nodes.g @@  removesmallclocks(g,m / 100,@e) 
 else if measure = "space"then  toseq.nodes.g @@  removesmallspace(g,m / 100,@e) 
 else  toseq.nodes.g @@  removesmallcount(g,m / 100,@e)
  if cardinality.arcs.g = cardinality.arcs.g2 then g2 else removesmall(g2, measure, m)

function removesmallclocks( g:labeledgraph.parc,limit:int, node:parc)labeledgraph.parc
 if cardinality.arcstosuccessors(g, node) = 0 then
 if toseq.backarcstopredecessors(g, node)@@ +(0, clocks.@e) < limit then deletenode(g, node)else g
 else g

function removesmallspace(g:labeledgraph.parc,limit:int,  node:parc)labeledgraph.parc
 if cardinality.arcstosuccessors(g, node) = 0 then
 if toseq.backarcstopredecessors(g, node)@@ +(0, space.@e) < limit then deletenode(g, node)else g
 else g

function removesmallcount( g:labeledgraph.parc,limit:int, node:parc)labeledgraph.parc
 if cardinality.arcstosuccessors(g, node) = 0 then
 if toseq.backarcstopredecessors(g, node)@@ +(0, counts.@e) < limit then
  assert false report [ head.node]
    deletenode(g, node)
  else g
 else g

Function shorten(pnodes:seq.word)nodemap
 // This procedure produces a map that takes fsigs and shortens them keeping them distinct. The following procedure uses this result to map the figs to the new ones. //
 let nodes = sort.toalphaseq.pnodes
 let c = towordseq.nodes @@ +([ empty:seq.seq.word], codedown.@e) + [ empty:seq.seq.word]
 let short = arithseq(length.c - 2, 1, 2)@@ +(empty:seq.seq.word, shorten(c, @e))
  nodemap(nodes, short)

Function shorten(map:nodemap, w:word)seq.word(short.map)_binarysearch(org.map, alphaword.w)

type nodemap is record org:seq.alphaword, short:seq.seq.word

function shorten(a:seq.seq.seq.word, i:int)seq.word
 let j = max(differ(a_(i - 1), a_i, 1), differ(a_i, a_(i + 1), 1))
  if j = 1 then a_i_1
  else
   let z = subseq(a_i, 1, j)@@ +(empty:seq.seq.word, formattype.@e)
    z_1 + ":" + z_2 + "("
    + (subseq(z, 2, length.z))@@ list("",",",   @e)
    + ")"

function formattype(a:seq.word)seq.word reverse( a @@ list( "",  ".",[@e])  )

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

Function dumpprofileinfo seq.word profiledata.loadedlibs_1 @@ list( ""," &br", [ tail.@e, head.@e, toword.counts.@e])
