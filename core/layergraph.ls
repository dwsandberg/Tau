Module layergraph

use otherseq.baryinfo

use otherseq.arc.int

use set.arc.int

use graph.int

use otherseq.int

use seq.int

use otherseq.seq.int

use seq.seq.int

use set.int

use real

use standard

Export type:layeredgraph

Export g(layeredgraph) graph.int

Export layers(layeredgraph) seq.seq.int

Export orgNodeCount(layeredgraph) int

Export layeredgraph(g:graph.int, layers:seq.seq.int, int) layeredgraph

type layeredgraph is g:graph.int, layers:seq.seq.int, orgNodeCount:int

Function layer(g:graph.int) layeredgraph
{expect DAG as input}
let a = layeredgraph(g, sublayer.g, n.nodes.g)
assert not.isempty.layers.a report "empty graph"
let lg = adddummynodes.a,
layeredgraph(g.lg, decreasecrosses(g.lg, layers.lg), n.nodes.g)

function sublayer(g0:graph.int) seq.seq.int
for g = g0, layers = empty:seq.seq.int, lastlayer = empty:set.int
while not.isempty.nodes.g
do
 let sources = asset.sources.g
 assert not.isempty.sources report "NOT A DAG"
 for acc = g, @e ∈ toseq.sources do deletenode(acc, @e)
 for acc2 = empty:set.int, n ∈ toseq.lastlayer
 do
  let succ = successors(g0, n),
  if isempty.succ ∨ not.isempty(succ ∩ sources) then acc2 else acc2 + n
 let thislayer = sources ∪ acc2,
 {assert isempty.lastlayer /or toseq.acc2 /in [{[13], empty:seq.int,} [2]] report" last"+%.toseq.lastlayer+"
 /br sources"+%.toseq.sources+"
 /br"+%.toseq.acc2+"
 /br thislayer+%.toseq.thislayer"+%n (layers >> 1+toseq.(lastlayer \ acc2)+toseq.thislayer)+"
 /br"+%.toseq.arcs.g0}
 next(acc, if isempty.lastlayer then layers else layers + toseq(lastlayer \ acc2), thislayer),
layers + toseq.lastlayer

----adddummy nodes---

function levels(s:seq.seq.int) seq.int
{assignment of node to level}
for acc = empty:set.arc.int, level = 1, l ∈ s
do
 for acc1 = acc, i ∈ l do acc1 + arc(i, level),
 next(acc1, level + 1)
for list = empty:seq.int, a ∈ toseq.acc do list + head.a,
list

function adddummynodes(y2:layeredgraph) layeredgraph
{add nodes so that arcs never cross layers.}
let level = levels.layers.y2
for
 arcs = empty:seq.arc.int
 , layers = layers.y2
 , level' = level
 , nextnode = n.nodes.g.y2 + 1
 , a ∈ toseq.arcs.g.y2
do
 let leveltail = (tail.a)#level
 let levelhead = (head.a)#level,
 if leveltail + 1 = levelhead then next(arcs + a, layers, level', nextnode)
 else
  let t = levelhead - leveltail - 1
  for
   arcs1 = arcs + arc(tail.a, nextnode) + arc(t + nextnode - 1, head.a)
   , remaininglayers = layers << leveltail
   , layers' = subseq(layers, 1, leveltail)
   , n ∈ arithseq(t, 1, nextnode)
  do
   next(
    if t + nextnode - 1 = n then arcs1 else arcs1 + arc(n, n + 1)
    , remaininglayers << 1
    , layers' + (1#remaininglayers + n)
   ),
  next(arcs1, layers' + remaininglayers, level' + arithseq(t, 1, leveltail + 1), nextnode + t)
assert check(levels.layers, arcs) report "XX",
layeredgraph(newgraph.arcs, layers, orgNodeCount.y2)

function check(levels:seq.int, s:seq.arc.int) boolean
for ok = true, a ∈ s
while ok
do
 let leveltail = (tail.a)#levels
 let levelhead = (head.a)#levels,
 leveltail + 1 = levelhead,
ok

----------------

type baryinfo is avg:real, node:int

function =(a:baryinfo, b:baryinfo) boolean node.a = node.b

Function >1(a:baryinfo, b:baryinfo) ordering avg.a >1 avg.b

function barycenter(layer1:seq.int, pred:seq.int) real
for a = 0, @e ∈ pred do a + findindex(layer1, @e),
toreal.a / toreal.n.pred

Function decreasecrosses(g:graph.int, layers:seq.seq.int) seq.seq.int
for result = [1#layers], i = 1
while i < n.layers
do
 let layer1 = i#result
 let layer2 = (i + 1)#layers
 for a = empty:seq.baryinfo, node ∈ layer2
 do a + baryinfo(barycenter(layer1, toseq.predecessors(g, node)), node),
 for new = empty:seq.int, @e ∈ sort.a do new + node.@e,
 next(result + new, i + 1),
result 