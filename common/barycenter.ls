Module barycenter.T

use otherseq.baryinfo.T

use graph.T

use otherseq.T

use seq.seq.T

use set.T

use real

use standard

unbound =(T, T) boolean

type baryinfo is avg:real, node:T

function =(a:baryinfo.T, b:baryinfo.T) boolean node.a = node.b

Function >1(a:baryinfo.T, b:baryinfo.T) ordering avg.a >1 avg.b

function averagepred(g:graph.T, layer1:seq.T, node:T) baryinfo.T
let pred = toseq.predecessors(g, node)
let a = for acc = 0, @e ∈ pred do acc + findindex(layer1, @e), acc,
baryinfo(toreal.a / toreal.n.pred, node)

function baryinfo(g:graph.T, layer1:seq.T, layer2:seq.T) seq.T
let a = for acc = empty:seq.baryinfo.T, @e ∈ layer2 do acc + averagepred(g, layer1, @e), acc
for acc = empty:seq.T, @e ∈ sort.a do acc + node.@e,
acc

function baryinfo(g:graph.T, layers:seq.seq.T, i:int, result:seq.seq.T) seq.seq.T
if i < n.layers then
 let new = baryinfo(g, i_result, (i + 1)_layers),
 baryinfo(g, layers, i + 1, result + new)
else result

Function decreasecrosses(g:graph.T, layers:seq.seq.T) seq.seq.T
baryinfo(g, layers, 1, [1_layers]) 