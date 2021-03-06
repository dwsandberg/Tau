Module layergraph.T

use barycenter.T

use graph.T

use seq.T

use seq.arc.T

use seq.seq.T

use set.T

use set.arc.T

use stdlib

type layeredgraph is record g:graph.T, layers:seq.seq.T

Function g(layeredgraph.T)graph.T export

Function layers(layeredgraph.T)seq.seq.T export

Function layeredgraph(g:graph.T, layers:seq.seq.T)layeredgraph.T export

Function layer(g:graph.T)layeredgraph.T 
 // expect DAG as input // 
  let a = layeredgraph(g, sublayer.g)
  assert not.isempty.layers.a report"empty graph"
  let lg = adddummynodes.a 
  layeredgraph(g.lg, decreasecrosses(g.lg, layers.lg))

function sublayer(g:graph.T)seq.seq.T 
 if isempty.nodes.g 
  then empty:seq.seq.T 
  else let r = sources.g 
  assert not.isempty.r report"NOT A DAG"
  [ r]+ sublayer.@(deletenode, identity, g, r)

Function issource(g:graph.T, n:T)seq.T 
 if cardinality.predecessors(g, n)= 0 then [ n]else empty:seq.T

Function sources(g:graph.T)seq.T @(+, issource.g, empty:seq.T, toseq.nodes.g)

----adddummy nodes---

add nodes so that arcs never cross layers.

function adddummynodes(y2:layeredgraph.T)layeredgraph.T 
 d2(y2, g.y2, 2, asset(layers(y2)_1), [ layers(y2)_1])

function d2(org:layeredgraph.T, g:graph.T, i:int, ok:set.T, layerout:seq.seq.T)layeredgraph.T 
 let ok1 = ok ∪ asset(layers(org)_i)
  let gnew = @(splitarc, identity, g, @(+, splitarcs(g, ok1), empty:seq.arc.T, layerout_(i - 1)))
  let newnodes = nodes.gnew - nodes.g 
  let newout = layerout + [ layers(org)_i + toseq.newnodes]
  if i < length.layers.org 
  then let x = ok1 ∪ newnodes ∪ asset(layers(org)_(i + 1))
   d2(org, gnew, i + 1, x, newout)
  else layeredgraph(gnew, newout)

function splitarcs(g:graph.T, ok:set.T, n:T)seq.arc.T toarcs(n, toseq(successors(g, n) - ok))

function splitarc(g:graph.T, a:arc.T)graph.T 
 let new = generatenode.nodes.g 
  replacearcs(g, asset.[ a], asset.[ arc(tail.a, new), arc(new, head.a)])

function generatenode(s:set.T)T unbound

      

