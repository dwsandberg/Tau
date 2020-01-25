Module profile

Problems:Junk at top of graph

Max space seems to be on node with head and tail blank!

profileresult could return a sequence of packed parcs instead of four sequence.

@(-, does not parse.

use displaytextgraph

use labeledgraph.parc

use libscope

use oseq.alphaword

use seq.alphaword

use seq.arcinfo.seq.word

use seq.int

use seq.parc

use seq.profileresult

use seq.seq.seq.word

use seq.seq.word

use seq.word

use set.parc

use stdlib

use svggraph.seq.word

* To profile a function add a use clause 
  "use options.<return type of /function >"and change /function so body is wrap 
 by a call to PROFILE(<body>). Multiple procedures can be profiled at the same time. After the part of code of interest add a 
 call to profileresults("time")to optain the result.

* Profiling is accomplished by adding code to perform measurements before and after each procedure call and recording the difference 
 .

function toarcinfo(measure:seq.word, max:int, map:nodemap, a:parc)arcinfo.seq.word 
   let label = toword((
    if measure ="time"
    then clocks.a 
    else if measure ="count"then counts.a else space.a)
   * 100 
   / max)
    arcinfo(shorten(map, head.a), shorten(map, tail.a), [ label])

Function profileresults(measure:seq.word)seq.word 
  // Returns label graph of profile results. Measure is time, count, or space. // 
  // let g = profileresults // 
  let g = @(+, identity, empty:labeledgraph.parc, profileinfo)
   let m = 
    if measure ="time"
    then @(max, clocks, 0, toseq(arcs.g))
    else if measure ="count"
    then @(max, counts, 0, toseq(arcs.g))
    else 
     assert measure ="space"report"unknown profile measure"
      @(max, space, 0, toseq(arcs.g))
   let g3 = removesmall(g, measure, m)
    // shorten the names of the functions and then build and display labeled graph // 
    let nodemap = shorten.@(+, head,"", toseq(nodes.g3))
     let z2 = @(+, toarcinfo(measure, m, nodemap), empty:seq.arcinfo.seq.word, toseq(arcs.g3))
      "&br"+ measure + toword.m +"&br"+ display.z2 +"&br"+ measure + toword.m

function removesmall(g:labeledgraph.parc, measure:seq.word, m:int)labeledgraph.parc 
   let g2 = 
    if measure ="time"
    then @(removesmallclocks(m / 100), identity, g, toseq(nodes.g))
    else if measure ="space"
    then @(removesmallspace(m / 100), identity, g, toseq(nodes.g))
    else @(removesmallcount(m / 100), identity, g, toseq(nodes.g))
    if cardinality(arcs.g)= cardinality(arcs.g2)then g2 else removesmall(g2, measure, m)

function removesmallclocks(limit:int, g:labeledgraph.parc, node:parc)labeledgraph.parc 
   if cardinality.arcstosuccessors(g, node)= 0 
   then if @(+, clocks, 0, toseq.backarcstopredecessors(g, node))< limit then deletenode(g, node)else g 
   else g

function removesmallspace(limit:int, g:labeledgraph.parc, node:parc)labeledgraph.parc 
   if cardinality.arcstosuccessors(g, node)= 0 
   then if @(+, space, 0, toseq.backarcstopredecessors(g, node))< limit then deletenode(g, node)else g 
   else g

function removesmallcount(limit:int, g:labeledgraph.parc, node:parc)labeledgraph.parc 
   if cardinality.arcstosuccessors(g, node)= 0 
   then 
    if @(+, counts, 0, toseq.backarcstopredecessors(g, node))< limit 
    then 
     assert false report [ head.node]
      deletenode(g, node)
    else g 
   else g

Function shorten(pnodes:seq.word)nodemap 
  // This procedure produces a map that takes fsigs and shortens them keeping them distinct. The following procedure uses this result to map the figs to the new ones. // 
  let nodes = sort(toalphaseq.pnodes)
   let c = @(+, codedown, [ empty:seq.seq.word], towordseq.nodes)+ [ empty:seq.seq.word]
   let short = @(+, shorten(c), empty:seq.seq.word, arithseq(length.c - 2, 1, 2))
    nodemap(nodes, short)

Function shorten(map:nodemap, w:word)seq.word(short.map)_binarysearch(org.map, alphaword.w)

type nodemap is record org:seq.alphaword, short:seq.seq.word

function shorten(a:seq.seq.seq.word, i:int)seq.word 
   let j = max(differ(a_(i - 1), a_i, 1), differ(a_i, a_(i + 1), 1))
    if j = 1 
     then a_i_1 
     else 
      let z = @(+, formattype, empty:seq.seq.word, subseq(a_i, 1, j))
       z_1 +":"+ z_2 +"("+ @(seperator(","), identity,"", subseq(z, 2, length.z))
       +")"

function formattype(a:seq.word)seq.word reverse.@(seperator("."), identity, empty:seq.word, a)

function reverse(s:seq.word)seq.word @(+,_(s), empty:seq.word, arithseq(length.s, 0 - 1, length.s))

function differ(a:seq.seq.word, b:seq.seq.word, i:int)int if i > length.a ∨ i > length.b then i else if a_i = b_i then differ(a, b, i + 1)else i

type parc is record head:word, tail:word, counts:int, clocks:int, space:int

Function head(parc)word export

Function tail(parc)word export

Function counts(parc)int export

Function clocks(parc)int export

Function space(parc)int export

function ?(a:parc, b:parc)ordering head.a ? head.b ∧ tail.a ? tail.b

function ?2(a:parc, b:parc)ordering head.a ? head.b

function reverse(a:parc)parc parc(tail.a, head.a, counts.a, clocks.a, space.a)

function tonode(a:parc)parc parc(head.a, head.a, counts.a, clocks.a, space.a)

function toarc(p:profileresult, i:int)parc parc((arcs.p)_(2 * i - 1),(arcs.p)_(2 * i),(counts.p)_i,(clocks.p)_i,(space.p)_i)

function +(g:labeledgraph.parc, p:profileresult)labeledgraph.parc @(+, toarc(p), g, arithseq(length(counts.p), 1, 1))

type profileresult is record arcs:seq.word, counts:seq.int, clocks:seq.int, space:seq.int

function profileinfo seq.profileresult builtin.usemangle

