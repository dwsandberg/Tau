Module barycenter.T

use graph.T

use otherseq.baryinfo.T

use real

use seq.T

use seq.baryinfo.T

use seq.seq.T

use set.T

use stdlib

function =(T, T)boolean unbound

type baryinfo is record avg:real, node:T

function =(a:baryinfo.T, b:baryinfo.T)boolean node.a = node.b

Function ?(a:baryinfo.T, b:baryinfo.T)ordering avg.a ? avg.b

function findindex(s:seq.T, a:T)int findindex(a, s)

function averagepred(g:graph.T, layer1:seq.T, node:T)baryinfo.T
 let pred = toseq.predecessors(g, node)
  baryinfo(toreal.@(+, findindex(layer1), 0, pred) / toreal.length.pred, node)

function baryinfo(g:graph.T, layer1:seq.T, layer2:seq.T)seq.T
 @(+, node, empty:seq.T, sort.@(+, averagepred(g, layer1), empty:seq.baryinfo.T, layer2))

function baryinfo(g:graph.T, layers:seq.seq.T, i:int, result:seq.seq.T)seq.seq.T
 if i < length.layers then
 let new = baryinfo(g, result_i, layers_(i + 1))
   baryinfo(g, layers, i + 1, result + new)
 else result

Function decreasecrosses(g:graph.T, layers:seq.seq.T)seq.seq.T baryinfo(g, layers, 1, [ layers_1])