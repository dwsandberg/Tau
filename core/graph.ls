Module graph.T

use set.arc.T

use seq.T

use set.T

use standard

Export type:arc.T

Export head(arc.T) T

Export tail(arc.T) T

Export arc(a:T, b:T) arc.T

Export type:graph.T

Export arcs(graph.T) set.arc.T

Export nodes(graph.T) set.T

type arc is tail:T, head:T

type graph is arcs:set.arc.T, backarcs:set.arc.T, nodes:set.T

Function newgraph(a:seq.arc.T) graph.T
for acc = graph(empty:set.arc.T, empty:set.arc.T, empty:set.T), @e ∈ a do
 acc + @e
/for (acc)

Function =(c:arc.T, d:arc.T) boolean tail.c = tail.d ∧ head.c = head.d

Function >1(a:arc.T, b:arc.T) ordering tail.a >1 tail.b ∧ head.a >1 head.b

Function >2(a:arc.T, b:arc.T) ordering tail.a >1 tail.b

unbound =(a:T, b:T) boolean

unbound >1(T, T) ordering

Function subgraph(g:graph.T, nodes:set.T) graph.T
for acc = graph(empty:set.arc.T, empty:set.arc.T, nodes), @e ∈ toseq.arcs.g do
 if head.@e ∉ nodes then acc else if tail.@e ∉ nodes then acc else acc + @e
/for (acc)

Function successors(g:graph.T, n:T) set.T
for acc = empty:set.T, @e ∈ toseq.findelement2(arcs.g, arc(n, n)) do
 acc + head.@e
/for (acc)

Function arcstosuccessors(g:graph.T, n:T) set.arc.T findelement2(arcs.g, arc(n, n))

Function arcstopredecessors(g:graph.T, n:T) set.arc.T
asset.toarcs(toseq.predecessors(g, n), n)

Function predecessors(g:graph.T, n:T) set.T
for acc = empty:set.T, @e ∈ toseq.findelement2(backarcs.g, arc(n, n)) do
 acc + head.@e
/for (acc)

Function deletearc(g:graph.T, a:arc.T) graph.T
graph(arcs.g - a, backarcs.g - arc(head.a, tail.a), nodes.g)

Function deletearcs(g:graph.T, a:set.arc.T) graph.T
for acc = g, @e ∈ toseq.a do deletearc(acc, @e) /for (acc)

Function deletenode(g:graph.T, n:T) graph.T
deletearcs(graph(arcs.g, backarcs.g, nodes.g - n)
 , arcstosuccessors(g, n) ∪ arcstopredecessors(g, n))

Function toarcs(n:T, s:seq.T) seq.arc.T
for acc = empty:seq.arc.T, @e ∈ s do acc + arc(n, @e) /for (acc)

Function toarcs(s:seq.T, n:T) seq.arc.T
for acc = empty:seq.arc.T, @e ∈ s do acc + arc(@e, n) /for (acc)

Function backarc(a:arc.T) arc.T arc(head.a, tail.a)

Function replacearcs(g:graph.T, oldarcs:set.arc.T, newarcs:set.arc.T) graph.T
deletearcs(g, oldarcs \ newarcs) + toseq(newarcs \ oldarcs)

Function +(g:graph.T, a:arc.T) graph.T
graph(arcs.g + a, backarcs.g + arc(head.a, tail.a), nodes.g + tail.a + head.a)

Function +(g:graph.T, a:seq.arc.T) graph.T
for acc = g, @e ∈ a do acc + @e /for (acc)

Function +(g:graph.T, node:T) graph.T graph(arcs.g, backarcs.g, nodes.g + node)

Function reachable(g:graph.T, a:seq.T) set.T
let d = asset.a
reachable(g, d, d, 1)

function reachable(g:graph.T, old:set.T, new:set.T, count:int) set.T
assert count < 1000 report "fal" + toword.cardinality.old + toword.cardinality.new
if isempty.new then
 old
else
 let a = for acc = empty:set.T, @e ∈ toseq.new do acc ∪ successors(g, @e) /for (acc)
 let b = old ∪ new
 reachable(g, b, a \ b, count + 1)

Function complement(g:graph.T) graph.T graph(backarcs.g, arcs.g, nodes.g)

_________________

ordering of nodes in graph

Function sinks(g:graph.T, b:set.T) seq.T
{returns list of sinks in graph with arcs to nodes in set b removed}
for acc = empty:seq.T, n ∈ toseq(nodes.g \ b) do
 if cardinality(successors(g, n) \ b) = 0 then acc + n else acc
/for (acc)

Function sources(g:graph.T, b:set.T) seq.T
{returns list of sources in graph with arcs to nodes in set b removed}
for acc = empty:seq.T, n ∈ toseq(nodes.g \ b) do
 if cardinality(predecessors(g, n) \ b) = 0 then acc + n else acc
/for (acc)

Function sources(g:graph.T) seq.T sources(g, empty:set.T)

Function sinks(g:graph.T) seq.T sinks(g, empty:set.T)

Function sinksfirst(g:graph.T) seq.T
{will not return nodes involved in a cycle}
sinksfirst(g, empty:set.T, empty:seq.T)

function sinksfirst(g:graph.T, b:set.T, result:seq.T) seq.T
let new = sinks(g, b)
if isempty.new then result else sinksfirst(g, b ∪ asset.new, result + new)

function breathfirst(g:graph.T, b:set.T, result:seq.T) seq.T
let new = sources(g, b)
if isempty.new then result else breathfirst(g, b ∪ asset.new, result + new)

Function breathfirst(g:graph.T) seq.T
{will not return nodes involved in a cycle}
breathfirst(g, empty:set.T, empty:seq.T)

____________________

Function outdegree(g:graph.T, n:T) int cardinality.successors(g, n)

Function indegree(g:graph.T, n:T) int cardinality.predecessors(g, n)

Function =(a:graph.T, b:graph.T) boolean
cardinality.arcs.a = cardinality.arcs.b ∧ nodes.a = nodes.b ∧ arcs.a = arcs.b

Function transitiveClosure(gin:graph.T) graph.T
{add arcs to graph so if node is reachable, it can be reached with single arc}
for g = gin, n ∈ toseq.nodes.gin do
 {add arcs to graph so path does not need to go through n}
 for arcs = empty:seq.arc.T, p ∈ toseq.predecessors(g, n) do
  for acc2 = empty:seq.arc.T, s ∈ toseq.successors(g, n) do
   acc2 + arc(p, s)
  /for (arcs + acc2)
 /for (g + arcs)
/for (g) 