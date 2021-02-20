Module layergraph.T

use standard

use barycenter.T

use graph.T

use seq.T

use set.T

use seq.arc.T

use set.arc.T

use seq.seq.T

type layeredgraph is g:graph.T, layers:seq.seq.T

Export g(layeredgraph.T)graph.T

Export layers(layeredgraph.T)seq.seq.T

Export layeredgraph(g:graph.T, layers:seq.seq.T)layeredgraph.T

Function layer(g:graph.T)layeredgraph.T
 \\ expect DAG as input \\
 let a = layeredgraph(g, sublayer.g)
  assert not.isempty.layers.a report"empty graph"
  let lg = adddummynodes.a
   layeredgraph(g.lg, decreasecrosses(g.lg, layers.lg))

function sublayer(g:graph.T)seq.seq.T
 if isempty.nodes.g then empty:seq.seq.T
 else
  let r = sources.g
   assert not.isempty.r report"NOT A DAG"
    [ r] + sublayer.for acc = g, @e = r do deletenode(acc, @e)end(acc)

Function issource(g:graph.T, n:T)seq.T
 if cardinality.predecessors(g, n) = 0 then [ n]else empty:seq.T

Function sources(g:graph.T)seq.T
 for acc = empty:seq.T, @e = toseq.nodes.g do acc + issource(g, @e)end(acc)

----adddummy nodes---

add nodes so that arcs never cross layers.

function adddummynodes(y2:layeredgraph.T)layeredgraph.T d2(y2, g.y2, 2, asset.(layers.y2)_1, [(layers.y2)_1])

function d2(org:layeredgraph.T, g:graph.T, i:int, ok:set.T, layerout:seq.seq.T)layeredgraph.T
let ok1 = ok ∪ asset.(layers.org)_i
let gnew = for acc = g, @e = for acc = empty:seq.arc.T, @e = layerout_(i - 1)do acc + splitarcs(g, ok1, @e)end(acc)do
 splitarc(acc, @e)end(acc)
let newnodes = nodes.gnew - nodes.g
let newout = layerout + [(layers.org)_i + toseq.newnodes]
 if i < length.layers.org then
 let x = ok1 ∪ newnodes ∪ asset.(layers.org)_(i + 1)
  d2(org, gnew, i + 1, x, newout)
 else layeredgraph(gnew, newout)

function splitarcs(g:graph.T, ok:set.T, n:T)seq.arc.T toarcs(n, toseq(successors(g, n) - ok))

function splitarc(g:graph.T, a:arc.T)graph.T
let new = generatenode.nodes.g
 replacearcs(g, asset.[ a], asset.[ arc(tail.a, new), arc(new, head.a)])

unbound generatenode(s:set.T)T