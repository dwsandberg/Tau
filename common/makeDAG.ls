Module makeDAG.T

use seq.arc.T

use set.arc.T

use graph.T

use seq.T

use set.T

use standard

Function makeDAG(g:graph.T) graph.T
{Turn directed graph into DAG by reversing arcs}
make(g
, empty:seq.arc.T
, ordernodes(g, empty:set.T, empty:seq.T, empty:seq.T)
, empty:set.T
, 1
)

function make(g:graph.T, reversed:seq.arc.T, l:seq.T, nodes:set.T, i:int) graph.T
if i > length.l then
 let r = for acc = asset.empty:seq.arc.T, @e ∈ reversed do acc + backarc.@e /for (acc)
 replacearcs(g, asset.reversed, r)
else
 let n = l_i
 let succs = successors(g, n)
 make(g
 , for acc = reversed, @e ∈ toseq.arcstosuccessors(g, n) do acc + filter(nodes, @e) /for (acc)
 , l
 , nodes + n
 , i + 1
 )

function filter(n:set.T, a:arc.T) seq.arc.T
if head.a ∈ n then [a] else empty:seq.arc.T

Function sinks2(g:graph.T, b:set.T, n:T) set.T
if cardinality(successors(g, n) \ b) = 0 then asset.[n] else empty:set.T

Function sources2(g:graph.T, b:set.T, n:T) set.T
if cardinality(predecessors(g, n) \ b) = 0 then asset.[n] else empty:set.T

function ordernodes(g:graph.T, b:set.T, first:seq.T, last:seq.T) seq.T
let a = for acc = empty:set.T, @e ∈ toseq(nodes.g \ b) do acc ∪ sources2(g, b, @e) /for (acc)
let d = for acc = empty:set.T, @e ∈ toseq(nodes.g \ b) do acc ∪ sinks2(g, b, @e) /for (acc)
if cardinality.a + cardinality.d = 0 then
 let u = nodes.g \ b
 if isempty.u then first + last
 else ordernodes(g, b + u_1, first + u_1, last)
else ordernodes(g, b ∪ a ∪ d, first + toseq.a, toseq.d + last) 