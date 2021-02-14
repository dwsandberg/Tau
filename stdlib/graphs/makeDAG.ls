Module makeDAG.T

use standard

use graph.T

use seq.T

use set.T

use seq.arc.T

use set.arc.T

Function makeDAG(g:graph.T)graph.T
 \\ Turn directed graph into DAG by reversing arcs \\
 make(g, empty:seq.arc.T, ordernodes(g, empty:set.T, empty:seq.T, empty:seq.T), empty:set.T, 1)

function make(g:graph.T, reversed:seq.arc.T, l:seq.T, nodes:set.T, i:int)graph.T
 if i > length.l then
 let r = for @e ∈ reversed, acc = asset.empty:seq.arc.T ,,, acc + backarc.@e
   replacearcs(g, asset.reversed, r)
 else
  let n = l_i
  let succs = successors(g, n)
   make(g, for @e ∈ toseq.arcstosuccessors(g, n), acc = reversed ,,, acc + filter(nodes, @e), l, nodes + n, i + 1)

function filter(n:set.T, a:arc.T)seq.arc.T
 if head.a ∈ n then [ a]else empty:seq.arc.T

Function expandback(org:graph.T, modified:graph.T, n:T)T
 if n ∈ nodes.org then n else expandback(org, modified,(toseq.predecessors(modified, n))_1)

Function sinks2(g:graph.T, b:set.T, n:T)set.T
 if cardinality(successors(g, n) - b) = 0 then asset.[ n]else empty:set.T

Function sources2(g:graph.T, b:set.T, n:T)set.T
 if cardinality(predecessors(g, n) - b) = 0 then asset.[ n]else empty:set.T

function ordernodes(g:graph.T, b:set.T, first:seq.T, last:seq.T)seq.T
 let a = for @e ∈ toseq(nodes.g - b), acc = empty:set.T ,,, acc ∪ sources2(g, b, @e)
 let d = for @e ∈ toseq(nodes.g - b), acc = empty:set.T ,,, acc ∪ sinks2(g, b, @e)
  if cardinality.a + cardinality.d = 0 then
  let u = nodes.g - b
    if isempty.u then first + last else ordernodes(g, b + u_1, first + u_1, last)
  else ordernodes(g, b ∪ a ∪ d, first + toseq.a, toseq.d + last)