Module labeledgraph.T

use seq.T

use set.T

use stdlib

unbound ?(a:T, b:T)ordering

unbound ?2(a:T, b:T)ordering

unbound reverse(a:T)T

Export type:labeledgraph.T

type labeledgraph is record arcs:set.T, backarcs:set.T, nodes:set.T

Export arcs(labeledgraph.T)set.T

Export backarcs(labeledgraph.T)set.T

Export nodes(labeledgraph.T)set.T

Function empty:labeledgraph.T labeledgraph.T labeledgraph(empty:set.T, empty:set.T, empty:set.T)

Function +(g:labeledgraph.T, a:T)labeledgraph.T
 labeledgraph(arcs.g + a, backarcs.g + reverse.a, nodes.g + tonode.a + tonode.reverse.a)

unbound tonode(a:T)T

Function arcstosuccessors(g:labeledgraph.T, node:T)set.T findelement2(arcs.g, node)

Function backarcstopredecessors(g:labeledgraph.T, node:T)set.T findelement2(backarcs.g, node)

Function sinks(g:labeledgraph.T)seq.T(toseq.nodes.g)@@ +(empty:seq.T, sinks(g, @e))

Function sinks(g:labeledgraph.T, n:T)seq.T
 if cardinality.arcstosuccessors(g, n) = 0 then [ n]else empty:seq.T

Function subdelete(a:set.T, b:T)set.T a - b

Function deletenode(g:labeledgraph.T, n:T)labeledgraph.T
 let b = backarcstopredecessors(g, n)
 let a =(toseq.b)@@ subdelete(arcs.g, reverse.@e)
  labeledgraph(a, backarcs.g - b, nodes.g - n)