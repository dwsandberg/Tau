Module makeDAG.T

use graph.T

use seq.T

use seq.arc.T

use set.T

use set.arc.T

use stdlib

Function reverse(s:seq.T)seq.T @(+,_.s, empty:seq.T, arithseq(length.s, 0 - 1, length.s))

Function makeDAG(g:graph.T)graph.T 
 // Turn directed graph into DAG by reversing arcs // 
  make(g, empty:seq.arc.T, ordernodes(g, empty:set.T, empty:seq.T, empty:seq.T), empty:set.T, 1)

function make(g:graph.T, reversed:seq.arc.T, l:seq.T, nodes:set.T, i:int)graph.T 
 if i > length.l 
  then let r = @(+, backarc, asset.empty:seq.arc.T, reversed)
   replacearcs(g, asset.reversed, r)
  else let n = l_i 
  let succs = successors(g, n)
  make(g, @(+, filter.nodes, reversed, toseq.arcstosuccessors(g, n)), l, nodes + n, i + 1)

function filter(n:set.T, a:arc.T)seq.arc.T 
 if head.a in n then [ a]else empty:seq.arc.T

Function expandback(org:graph.T, modified:graph.T, n:T)T 
 if n in nodes.org then n else expandback(org, modified, toseq(predecessors(modified, n))_1)

Function sinks2(g:graph.T, b:set.T, n:T)set.T 
 if cardinality(successors(g, n) - b)= 0 then asset.[ n]else empty:set.T

Function sources2(g:graph.T, b:set.T, n:T)set.T 
 if cardinality(predecessors(g, n) - b)= 0 then asset.[ n]else empty:set.T

function ordernodes(g:graph.T, b:set.T, first:seq.T, last:seq.T)seq.T 
 let a = @(∪, sources2(g, b), empty:set.T, toseq(nodes.g - b))
  let d = @(∪, sinks2(g, b), empty:set.T, toseq(nodes.g - b))
  if cardinality.a + cardinality.d = 0 
  then let u = nodes.g - b 
   if isempty.u then first + last else ordernodes(g, b + u_1, first + u_1, last)
  else ordernodes(g, b ∪ a ∪ d, first + toseq.a, toseq.d + last)

________

     

