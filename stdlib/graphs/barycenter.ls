Module barycenter.T

use real

use standard

use graph.T

use otherseq.T

use seq.T

use set.T

use otherseq.baryinfo.T

use seq.baryinfo.T

use seq.seq.T

unbound =(T, T)boolean

type baryinfo is avg:real, node:T

function =(a:baryinfo.T, b:baryinfo.T)boolean node.a = node.b

Function ?(a:baryinfo.T, b:baryinfo.T)ordering avg.a ? avg.b

function averagepred(g:graph.T, layer1:seq.T, node:T)baryinfo.T
let pred = toseq.predecessors(g, node)
let a = for acc = 0, @e = pred do acc + findindex(@e, layer1)/for(acc)
 baryinfo(toreal.a / toreal.length.pred, node)

function baryinfo(g:graph.T, layer1:seq.T, layer2:seq.T)seq.T
let a = for acc = empty:seq.baryinfo.T, @e = layer2 do acc + averagepred(g, layer1, @e)/for(acc)
 for acc = empty:seq.T, @e = sort.a do acc + node.@e /for(acc)

function baryinfo(g:graph.T, layers:seq.seq.T, i:int, result:seq.seq.T)seq.seq.T
 if i < length.layers then
 let new = baryinfo(g, result_i, layers_(i + 1))
  baryinfo(g, layers, i + 1, result + new)
 else result

Function decreasecrosses(g:graph.T, layers:seq.seq.T)seq.seq.T baryinfo(g, layers, 1, [ layers_1])