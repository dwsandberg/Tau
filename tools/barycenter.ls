Module barycenter.T

use otherseq.baryinfo.T

use seq.baryinfo.T

use graph.T

use seq.seq.T

use seq.T

use set.T

use real

use standard

unbound =(T, T)boolean

type baryinfo is record avg:real, node:T

function =(a:baryinfo.T, b:baryinfo.T)boolean node.a = node.b

Function ?(a:baryinfo.T, b:baryinfo.T)ordering avg.a ? avg.b

function findindex(s:seq.T, a:T)int findindex(a, s)

function averagepred(g:graph.T, layer1:seq.T, node:T)baryinfo.T
 let pred = toseq.predecessors(g, node)
 let a = pred @ +(0, findindex(layer1, @e))
  baryinfo(toreal.a / toreal.length.pred, node)

function baryinfo(g:graph.T, layer1:seq.T, layer2:seq.T)seq.T
 let a = layer2 @ +(empty:seq.baryinfo.T, averagepred(g, layer1, @e))
  sort.a @ +(empty:seq.T, node.@e)

function baryinfo(g:graph.T, layers:seq.seq.T, i:int, result:seq.seq.T)seq.seq.T
 if i < length.layers then
 let new = baryinfo(g, result_i, layers_(i + 1))
   baryinfo(g, layers, i + 1, result + new)
 else result

Function decreasecrosses(g:graph.T, layers:seq.seq.T)seq.seq.T baryinfo(g, layers, 1, [ layers_1])