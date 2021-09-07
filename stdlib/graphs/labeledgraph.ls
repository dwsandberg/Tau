Module labeledgraph.T

use standard

use seq.T

use set.T

unbound ?(a:T, b:T)ordering

unbound ?2(a:T, b:T)ordering

unbound reverse(a:T)T

Export type:labeledgraph.T

type labeledgraph is arcs:set.T, backarcs:set.T, nodes:set.T

Export arcs(labeledgraph.T)set.T

Export backarcs(labeledgraph.T)set.T

Export nodes(labeledgraph.T)set.T

Function empty:labeledgraph.T labeledgraph.T labeledgraph(empty:set.T, empty:set.T, empty:set.T)

Function +(g:labeledgraph.T, a:T)labeledgraph.T
 labeledgraph(arcs.g + a, backarcs.g + reverse.a, nodes.g + tonode.a + tonode.reverse.a)

unbound tonode(a:T)T

Function arcstosuccessors(g:labeledgraph.T, node:T)set.T findelement2(arcs.g, node)

Function backarcstopredecessors(g:labeledgraph.T, node:T)set.T findelement2(backarcs.g, node)

Function sinks(g:labeledgraph.T)seq.T
 for acc = empty:seq.T, @e = toseq.nodes.g do acc + sinks(g, @e)/for(acc)

Function sinks(g:labeledgraph.T, n:T)seq.T
 if cardinality.arcstosuccessors(g, n) = 0 then [ n]else empty:seq.T

 
Function deletenode(g:labeledgraph.T, n:T)labeledgraph.T
let b = backarcstopredecessors(g, n)
let a = for acc = arcs.g, @e = toseq.b do  acc - reverse.@e /for(acc)
 labeledgraph(a, backarcs.g \ b, nodes.g - n)