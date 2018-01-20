module graph(T)

use graph.T

use ipair.T

use oseq.T

use oseq.arc.T

use oseq.ipair.T

use seq.T

use seq.arc.T

use seq.ipair.T

use set.T

use set.arc.T

use stdlib

type arc is record tail:T, head:T

type graph is record arcs:set.arc.T, backarcs:set.arc.T, nodes:set.T

Function newgraph(a:seq.arc.T)graph.T 
 @(+, identity, graph(empty:set.arc.T, empty:set.arc.T, empty:set.T), a)

Function =(c:arc.T, d:arc.T)boolean tail.c = tail.d ∧ head.c = head.d

Function ?(a:arc.T, b:arc.T)ordering tail.a ? tail.b ∧ head.a ? head.b

Function ?2(a:arc.T, b:arc.T)ordering tail.a ? tail.b

Function =(a:T, b:T)boolean unbound

Function ?(a:T, b:T)ordering unbound

Function head(arc.T)T export

Function tail(arc.T)T export

Function arcs(graph.T)set.arc.T export

Function nodes(graph.T)set.T export

Function subgraph(g:graph.T, nodes:set.T)graph.T 
 @(+, subgraph1(g, nodes), newgraph.empty:seq.arc.T, toseq.nodes)

graph(@(+, filterc(nodes), empty.arc.T, arcs.g), @(+, filterc(nodes), empty.arc.T, backarcs.g))

function subgraph1(g:graph.T, nodes:set.T, n:T)seq.arc.T 
 @(+, arc.n, empty:seq.arc.T, toseq(successors(g, n)∩ nodes))

@(setinsert, b, @(setinsert, a, empty.T, arcs.g), arcs.g)

Function arc(a:T, b:T)arc.T export

Function successors(g:graph.T, n:T)set.T @(+, head, empty:set.T, toseq.findelement2(arcs.g, arc(n, n)))

Function arcstosuccessors(g:graph.T, n:T)set.arc.T findelement2(arcs.g, arc(n, n))

Function arcstopredecessors(g:graph.T, n:T)set.arc.T asset.toarcs(toseq.predecessors(g, n), n)

Function predecessors(g:graph.T, n:T)set.T 
 @(+, head, empty:set.T, toseq.findelement2(backarcs.g, arc(n, n)))

Function deletearc(g:graph.T, a:arc.T)graph.T graph(arcs.g - a, backarcs.g - arc(head.a, tail.a), nodes.g)

Function deletearcs(g:graph.T, a:set.arc.T)graph.T @(deletearc, identity, g, toseq.a)

Function deletenode(g:graph.T, n:T)graph.T 
 deletearcs(graph(arcs.g, backarcs.g, nodes.g - n), arcstosuccessors(g, n)∪ arcstopredecessors(g, n))

Function toarcs(n:T, s:seq.T)seq.arc.T @(+, arc.n, empty:seq.arc.T, s)

function toarcs(s:seq.T, n:T)seq.arc.T @(+, arcr.n, empty:seq.arc.T, s)

/Function toarcs(s:seq.T, t:seq.T)seq.arc.T @(+, toarcs.s, empty:seq.arc.T, t)

function arcr(a:T, b:T)arc.T arc(b, a)

Function backarc(a:arc.T)arc.T arc(head.a, tail.a)

Function replacearcs(g:graph.T, oldarcs:set.arc.T, newarcs:set.arc.T)graph.T 
 deletearcs(g, oldarcs - newarcs)+ toseq(newarcs - oldarcs)

Function +(g:graph.T, a:arc.T)graph.T 
 graph(arcs.g + a, backarcs.g + arc(head.a, tail.a), nodes.g + tail.a + head.a)

Function +(g:graph.T, a:seq.arc.T)graph.T @(+, identity, g, a)

Function +(g:graph.T, node:T)graph.T graph(arcs.g, backarcs.g, nodes.g + node)

Function reachable(g:graph.T, a:seq.T)set.T 
 let d = asset.a 
  reachable(g, d, d, 1)

function reachable(g:graph.T, old:set.T, new:set.T, count:int)set.T 
 assert count < 1000 report"fal"+ toword.cardinality.old + toword.cardinality.new 
  if isempty.new 
  then old 
  else let a = @(∪, successors.g, empty:set.T, toseq.new)
  let b = old ∪ new 
  reachable(g, b, a - b, count + 1)

Function complement(g:graph.T)graph.T graph(backarcs.g, arcs.g, nodes.g)

_________________

ordering of nodes in graph

Function sinks(g:graph.T, b:set.T, n:T)seq.T 
 // returns list of sinks in graph with arcs to nodes in set b removed // 
  if cardinality(successors(g, n) - b)= 0 then [ n]else empty:seq.T

Function sinks(g:graph.T, b:set.T)seq.T @(+, sinks(g, b), empty:seq.T, toseq.nodes.g)

Function sinks(g:graph.T)seq.T sinks(g, empty:set.T)

Function sinksfirst(g:graph.T)seq.T 
 // will not return nodes involved in a cycle // sinksfirst(g, empty:set.T, empty:seq.T)

function addnodup(l:seq.T, n:seq.T)seq.T 
 if length.n = 0 then l else if n_1 in l then l else l + n

function sinksfirst(g:graph.T, b:set.T, result:seq.T)seq.T 
 let a = @(addnodup, sinks(g, b), result, toseq(nodes.g - b))
  if length.a = length.result then result else sinksfirst(g, asset.a, a)

Function sources(g:graph.T, b:set.T, n:T)seq.T 
 if cardinality(predecessors(g, n) - b)= 0 then [ n]else empty:seq.T

function breathfirst(g:graph.T, b:set.T, result:seq.T)seq.T 
 let a = @(addnodup, sources(g, b), result, toseq(nodes.g - b))
  if length.a = length.result 
  then let u = nodes.g - b 
   if isempty.u then result else breathfirst(g, b + u_1, a + u_1)
  else breathfirst(g, asset.a, a)

Function breathfirst(g:graph.T)seq.T 
 // will not return nodes involved in a cycle // breathfirst(g, empty:set.T, empty:seq.T)

____________________

Function nodesbyoutdegree(g:graph.T)seq.T 
 @(+, value, empty:seq.T, sort.@(+, subnodesbyoutdegree.g, empty:seq.ipair.T, toseq.nodes.g))

Function subnodesbyoutdegree(g:graph.T, n:T)ipair.T ipair(outdegree(g, n), n)

Function outdegree(g:graph.T, n:T)int cardinality.successors(g, n)

Function indegree(g:graph.T, n:T)int cardinality.predecessors(g, n)

Function =(a:graph.T, b:graph.T)boolean 
 cardinality.arcs.a = cardinality.arcs.b ∧ nodes.a = nodes.b ∧ arcs.a = arcs.b

Function transitiveClosure(g:graph.T)graph.T 
 // add arcs to graph so if node is reachable, it can be reached with single arc // 
  @(addclosure, identity, g, toseq.nodes.g)

function addclosure(g:graph.T, n:T)graph.T 
 // add arcs to graph so path does not need to go through n // g + toarcs(toseq.predecessors(g, n), toseq.successors(g, n))

Function toarcs(a:seq.T, b:seq.T)seq.arc.T @(+, toarcs2.b, empty:seq.arc.T, a)

Function toarcs2(b:seq.T, a:T)seq.arc.T @(+, arc.a, empty:seq.arc.T, b)

