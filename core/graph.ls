Module graph.T

use standard

use set.<<.T

use set.T

use seq.barc.T

use set.barc.T

unbound tail(T) <<.T

unbound head(T) <<.T

unbound toarc(<<.T) T

unbound >1(<<.T, <<.T) ordering

Export head(T) <<.T

Function >1(a:T, b:T) ordering tail.a >1 tail.b ∧ head.a >1 head.b

Function >2(a:T, b:T) ordering tail.a >1 tail.b

type << is dummy:T

type barc is arc:T

Function head(b:barc.T) <<.T tail.arc.b

Function tail(b:barc.T) <<.T head.arc.b

Function >1(a:barc.T, b:barc.T) ordering tail.a >1 tail.b ∧ head.a >1 head.b

Function >2(a:barc.T, b:barc.T) ordering tail.a >1 tail.b

Function tobarc(s:seq.T) seq.barc.T
for acc = empty:seq.barc.T, e ∈ s do acc + barc.e,
acc

Function toarcs(s:seq.barc.T) seq.T
for acc = empty:seq.T, e ∈ s do acc + arc.e,
acc

type graph is arcs:set.T, backarcs:set.barc.T, nodes:set.<<.T

Export nodes(graph.T) set.<<.T

Export arcs(graph.T) set.T

Export type:graph.T

/Export type:barc.T

/Export type:<<.T

Function newgraph(arcs:seq.T) graph.T
for acc = empty:set.<<.T, e ∈ arcs do acc + tail.e + head.e,
graph(asset.arcs, asset.tobarc.arcs, acc)

Function arcstosuccessors(g:graph.T, n:<<.T) set.T findelement2(arcs.g, toarc.n)

Function successors(g:graph.T, n:<<.T) set.<<.T
for acc = empty:set.<<.T, @e ∈ toseq.findelement2(arcs.g, toarc.n) do acc + head.@e,
acc

Function arcstopredecessors(g:graph.T, n:<<.T) seq.T
toarcs.toseq.findelement2(backarcs.g, barc.toarc.n)

Function predecessors(g:graph.T, n:<<.T) set.<<.T
for acc = empty:set.<<.T, e ∈ toseq.findelement2(backarcs.g, barc.toarc.n) do acc + head.e,
acc

Function replacearcs(g:graph.T, oldarcs:set.T, newarcs:set.T) graph.T
deletearcs(g, oldarcs \ newarcs) + toseq(newarcs \ oldarcs)

Function deletearc(g:graph.T, a:T) graph.T
graph(arcs.g - a, backarcs.g - barc.a, nodes.g)

Function deletearcs(g:graph.T, a:set.T) graph.T
for acc = g, e ∈ toseq.a do deletearc(acc, e),
acc

Function +(g:graph.T, nodes:seq.<<.T) graph.T
graph(arcs.g, backarcs.g, asset.nodes ∪ nodes.g)

Function +(g:graph.T, a:T) graph.T
graph(arcs.g + a, backarcs.g + barc.a, nodes.g + tail.a + head.a)

Function +(g:graph.T, a:seq.T) graph.T
for acc = g, @e ∈ a do acc + @e,
acc

Function deletenode(g:graph.T, n:<<.T) graph.T
deletearcs(
 graph(arcs.g, backarcs.g, nodes.g - n)
 , arcstosuccessors(g, n) ∪ asset.arcstopredecessors(g, n)
)

Function sinks(g:graph.T, b:set.<<.T) seq.<<.T
{returns list of sinks in graph with arcs to nodes in set b removed}
for acc = empty:seq.<<.T, n ∈ toseq(nodes.g \ b)
do if n(successors(g, n) \ b) = 0 then acc + n else acc,
acc

Function sources(g:graph.T, b:set.<<.T) seq.<<.T
{returns list of sources in graph with arcs to nodes in set b removed}
for acc = empty:seq.<<.T, n ∈ toseq(nodes.g \ b)
do if n(predecessors(g, n) \ b) = 0 then acc + n else acc,
acc

Function sources(g:graph.T) seq.<<.T sources(g, empty:set.<<.T)

Function sinks(g:graph.T) seq.<<.T sinks(g, empty:set.<<.T)

Function subgraph(g:graph.T, nodes:set.<<.T) graph.T
for acc = graph(empty:set.T, empty:set.barc.T, nodes), e ∈ toseq.arcs.g
do if head.e ∉ nodes then acc else if tail.e ∉ nodes then acc else acc + e,
acc

Function reachable(g:graph.T, a:seq.<<.T) set.<<.T
let d = asset.a,
reachable(g, d, d, 1)

function reachable(g:graph.T, old:set.<<.T, new:set.<<.T, count:int) set.<<.T
assert count < 1000 report "fal" + toword.n.old + toword.n.new,
if isempty.new then old
else
 for acc = empty:set.<<.T, e ∈ toseq.new do acc ∪ successors(g, e)
 let b = old ∪ new,
 reachable(g, b, acc \ b, count + 1)

Function complement(g:graph.T) graph.T
for acc = empty:set.T, a ∈ toseq.arcs.g do acc + reverse.a,
graph(acc, asset.tobarc.toseq.acc, nodes.g)

unbound reverse(T) T

-------------------------------

Function outdegree(g:graph.T, n:<<.T) int n.successors(g, n)

Function indegree(g:graph.T, n:<<.T) int n.predecessors(g, n)

Function =(a:graph.T, b:graph.T) boolean
n.arcs.a = n.arcs.b ∧ nodes.a = nodes.b ∧ arcs.a = arcs.b

Function transitiveClosure(gin:graph.T) graph.T
{add arcs to graph so if node is reachable, it can be reached with single arc}
for g = gin, n ∈ toseq.nodes.gin
do
 {add arcs to graph so path does not need to go through n}
 for arcs = empty:seq.T, p ∈ arcstopredecessors(g, n)
 do
  for acc2 = empty:seq.T, s ∈ toseq.arcstosuccessors(g, n) do acc2 + merge(p, s),
  arcs + acc2,
 g + arcs,
g

unbound merge(T, T) T 