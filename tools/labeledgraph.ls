Module labeledgraph.T

use seq.T

use set.T

use stdlib

function ?(a:T, b:T)ordering unbound

function ?2(a:T, b:T)ordering unbound

function reverse(a:T)T unbound

type labeledgraph is record arcs:set.T, backarcs:set.T, nodes:set.T

Function arcs(labeledgraph.T)set.T export

Function backarcs(labeledgraph.T)set.T export

Function nodes(labeledgraph.T)set.T export

Function empty:labeledgraph.T labeledgraph.T labeledgraph(empty:set.T, empty:set.T, empty:set.T)

Function +(g:labeledgraph.T, a:T)labeledgraph.T labeledgraph(arcs.g + a, backarcs.g + reverse.a, nodes.g + tonode.a + tonode(reverse.a))

function tonode(a:T)T unbound

Function arcstosuccessors(g:labeledgraph.T, node:T)set.T findelement2(arcs.g, node)

Function backarcstopredecessors(g:labeledgraph.T, node:T)set.T findelement2(backarcs.g, node)

Function sinks(g:labeledgraph.T)seq.T @(+, sinks(g), empty:seq.T, toseq(nodes.g))

Function sinks(g:labeledgraph.T, n:T)seq.T if cardinality.arcstosuccessors(g, n)= 0 then [ n]else empty:seq.T

Function subdelete(a:set.T, b:T)set.T a - b

Function deletenode(g:labeledgraph.T, n:T)labeledgraph.T 
   let b = backarcstopredecessors(g, n)
   let a = @(subdelete, reverse, arcs.g, toseq.b)
    // assert false report @(+, print,"", toseq.backarcstopredecessors(g, n))// labeledgraph(a, backarcs.g - b, nodes.g - n)

