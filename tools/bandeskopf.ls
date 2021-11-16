Module bandeskopf.T

use standard

use makeDAG.T

use layergraph.T


use graph.T

use otherseq.T

use seq.T

use set.T

use seq.int

use seq.arc.T

use set.arc.T

use seq.nodeinfo.T

use set.nodeinfo.T

use seq.seq.T

unbound =(T, T)boolean

Based on:Fast and Simple Horizontal Coordinate Assignment Ulrik Brandes and Boris Kopf, 2002

step one is to find type1 conflicts

function contains(a:set.T, w:T)set.T lookup(a, w)

function iis(g:graph.T, dummy:set.T, node:T)seq.T
{ returns upper nieghbor of inner segment ending at node }
if not(node ∈ dummy)then empty:seq.T
else
 let p =
  for acc = empty:set.T, @e ∈ toseq.predecessors(g, node)do acc ∪ contains(dummy, @e)/for(acc)
 if isempty.p then empty:seq.T else [ p_1]

Function type1conflicts(g:graph.T, dummy:set.T, layers:seq.seq.T)seq.arc.T
{ find type 1 conflicts, that is arcs that cross a inner arc }
for acc = empty:seq.arc.T, @e ∈ arithseq(length.layers - 2, 1, 2)do acc + marklayer(g, dummy, layers, @e)/for(acc)

function marklayer(g:graph.T, dummy:set.T, layers:seq.seq.T, l:int)seq.arc.T
marklayer(g, dummy, layers_l, layers_(l + 1), 0, 0, 1)

function marklayer(g:graph.T, dummy:set.T, upperlayer:seq.T, currentlayer:seq.T, k0:int, l:int, l1:int)seq.arc.T
if l1 > length.currentlayer then crossings(g, upperlayer, k0, length.upperlayer + 1, currentlayer, l, l1)
else
 let x = iis(g, dummy, currentlayer_l1)
 if isempty.x then marklayer(g, dummy, upperlayer, currentlayer, k0, l, l1 + 1)
 else
  let k1 = findindex(x_1, upperlayer)
  crossings(g, upperlayer, k0, k1, currentlayer, l, l1)
  + marklayer(g, dummy, upperlayer, currentlayer, k1, l1, l1 + 1)

function crossings(g:graph.T, upperlayer:seq.T, k0:int, k1:int, currentlayer:seq.T, l:int, l1:int)seq.arc.T
{(k0, l)and(k1, l1)both inner.crossings of(k0, l)have been found for(?, j)for j< k0.find arcs(?, n)where n > l and n < l1 
 that cross(k0, l)or(k1, l1)}
for acc = empty:seq.arc.T, @e ∈ arithseq(l1 - 1 - (l + 1) + 1, 1, l + 1)do acc + w1(g, upperlayer, k0, k1, currentlayer, @e)/for(acc)

function w1(g:graph.T, upperlayer:seq.T, k0:int, k1:int, currentlayer:seq.T, l0:int)seq.arc.T
{ crossings of cross(k0, l)or(k1, l1)for arcs incident to l0 where l0 is between l and l1 }
for acc = empty:seq.arc.T, @e ∈ toseq.predecessors(g, currentlayer_l0)do acc + w1(upperlayer, k0, k1, currentlayer_l0, @e)/for(acc)

function w1(upperlayer:seq.T, k0:int, k1:int, finish:T, start:T)seq.arc.T
let k = findindex(start, upperlayer)
if k < k0 ∨ k > k1 then [ arc(start, finish)]else empty:seq.arc.T

______________

Step 2 is to find vertical alignments.This will return arcs that will have the two nodes with the same x value.Inner arcs are 
 are prim canidates for this vertial alignment.

Function findvertarcsUL(g:graph.T, currentlayer:seq.T, lastlayer:seq.T, r:int, x:int, assigned:seq.T)seq.arc.T
if x > length.currentlayer then empty:seq.arc.T
else
 let node = currentlayer_x
 let preds = toseq.predecessors(g, node)
 if length.preds > 0 then
  let upperidx = for acc = empty:seq.int, @e ∈ preds do acc + findindex(@e, lastlayer)/for(acc)
  let medianleft = upperidx_((length.upperidx + 1) / 2)
  let medianright = upperidx_((length.upperidx + 1) / 2)
  if r < medianleft ∧ not(lastlayer_medianleft ∈ assigned)then
   findvertarcsUL(g, currentlayer, lastlayer, medianleft, x + 1, assigned + lastlayer_medianleft)
   + arc(lastlayer_medianleft, node)
  else if r < medianright ∧ not(lastlayer_medianright ∈ assigned)then
   findvertarcsUL(g, currentlayer, lastlayer, medianright, x + 1, assigned + lastlayer_medianright)
   + arc(lastlayer_medianright, node)
  else findvertarcsUL(g, currentlayer, lastlayer, r, x + 1, assigned)
 else findvertarcsUL(g, currentlayer, lastlayer, r, x + 1, assigned)

Function findvertarcsUL(g:graph.T, layers:seq.seq.T, l:int)seq.arc.T findvertarcsUL(g, layers_l, layers_(l - 1), 0, 1, empty:seq.T)

Function findvertarcsUL(g:graph.T, layers:seq.seq.T)seq.arc.T
for acc = empty:seq.arc.T, @e ∈ arithseq(length.layers - 1, 1, 2)do acc + findvertarcsUL(g, layers, @e)/for(acc)

Function findvertarcsUR(g:graph.T, layers:seq.seq.T)seq.arc.T
for acc = empty:seq.arc.T, @e ∈ arithseq(length.layers - 1, 1, 2)do acc + findvertarcsUR(g, layers, @e)/for(acc)

Function findvertarcsUR(g:graph.T, layers:seq.seq.T, l:int)seq.arc.T
findvertarcsUR(g, layers_l, layers_(l - 1), length.layers_l + 1, length.layers_l, empty:seq.T)

Function findvertarcsUR(g:graph.T, currentlayer:seq.T, lastlayer:seq.T, r:int, x:int, assigned:seq.T)seq.arc.T
if x = 0 then empty:seq.arc.T
else
 let node = currentlayer_x
 let preds = toseq.predecessors(g, node)
 if length.preds > 0 then
  let upperidx = for acc = empty:seq.int, @e ∈ preds do acc + findindex(@e, lastlayer)/for(acc)
  let medianleft = upperidx_((length.upperidx + 1) / 2)
  let medianright = upperidx_((length.upperidx + 1) / 2)
  if r > medianright ∧ not(lastlayer_medianright ∈ assigned)then
   findvertarcsUR(g, currentlayer, lastlayer, medianright, x - 1, assigned + lastlayer_medianright)
   + arc(lastlayer_medianright, node)
  else if r > medianleft ∧ not(lastlayer_medianleft ∈ assigned)then
   findvertarcsUR(g, currentlayer, lastlayer, medianleft, x - 1, assigned + lastlayer_medianleft)
   + arc(lastlayer_medianleft, node)
  else findvertarcsUR(g, currentlayer, lastlayer, r, x - 1, assigned)
 else findvertarcsUR(g, currentlayer, lastlayer, r, x - 1, assigned)

_________________

Function assignvert(RtoL:boolean
, layers:set.nodeinfo.T
, vertarcs:seq.arc.T
, assigned:set.nodeinfo.T
, q:nodeinfo.T
, x:int
, result:seq.nodeinfo.T
)set.nodeinfo.T
{ look for other nodes in vertical assignment.Do this recursively to assign all nodes in vertical assignmentnodes collecting 
 the max value of x in each layer Vertarcs always increate level by 1.The final value of x is assigned to all nodes in the vertical 
 assignment }
let lastassignedx =
 if RtoL then for acc = x, @e ∈ toseq.assigned do min(acc, findx(RtoL, q, @e))/for(acc)
 else for acc = x, @e ∈ toseq.assigned do max(acc, findx(RtoL, q, @e))/for(acc)
let newq = for acc = empty:seq.nodeinfo.T, @e ∈ vertarcs do acc + findy(q, @e)/for(acc)
if isempty.newq then
 for acc = assigned, @e ∈ result + q do acc + setx(lastassignedx, @e)/for(acc)
else
 assignvert(RtoL, layers, vertarcs, assigned, lookup(layers, newq_1)_1, lastassignedx, result + q)

function setx(x:int, q:nodeinfo.T)nodeinfo.T nodeinfo(n.q, x, y.q)

function findy(q:nodeinfo.T, a:arc.T)seq.nodeinfo.T
if n.q = tail.a then [ nodeinfo(head.a, x.q, y.q + 1)]else empty:seq.nodeinfo.T

function findx(RtoL:boolean, q:nodeinfo.T, a:nodeinfo.T)int
if y.a = y.q then if RtoL then x.a - seperation.q else x.a + seperation.q
else 0

------------Helper functions for adding arcs for block graph in hrizontal alignment

Function isroot(g:graph.T, n:T)seq.arc.T
if isempty.predecessors(g, n)then arcsfromsuccesors(n, g, n)else empty:seq.arc.T

function arcsfromsuccesors(root:T, g:graph.T, n:T)seq.arc.T
let s = successors(g, n)
if isempty.s then empty:seq.arc.T else [ arc(s_1, root)] + arcsfromsuccesors(root, g, s_1)

Function layerarcsR(arcstoroots:set.arc.T, layer:seq.T)seq.arc.T
for acc = empty:seq.arc.T, @e ∈ arithseq(length.layer - 1,-1, length.layer)do acc + layerarcsR(arcstoroots, layer, @e)/for(acc)

Function layerarcsR(arcstoroot:set.arc.T, layer:seq.T, i:int)seq.arc.T
let arc1 = arc(layer_i, layer_(i - 1))
let e = findelement2(arcstoroot, arc1)
if isempty.e then [ arc1]else [ arc(head.e_1, head.arc1), arc1]

Function layerarcs(arcstoroots:set.arc.T, layer:seq.T)seq.arc.T
for acc = empty:seq.arc.T, @e ∈ arithseq(length.layer - 1, 1, 2)do acc + layerarcs(arcstoroots, layer, @e)/for(acc)

Function layerarcs(arcstoroot:set.arc.T, layer:seq.T, i:int)seq.arc.T
let arc1 = arc(layer_(i - 1), layer_i)
let e = findelement2(arcstoroot, arc1)
if isempty.e then [ arc1]else [ arc(head.e_1, head.arc1), arc1]

-----------

For providing horizontal alignment.There is one for left and right directions.

Function alignUL(g:graph.T, layers:seq.seq.T, marked:set.arc.T, layerX:set.nodeinfo.T)set.nodeinfo.T
let vertarcs = findvertarcsUL(deletearcs(g, marked), layers)
let g3 = newgraph.vertarcs
let arcstoroots =
 asset.for acc = empty:seq.arc.T, @e ∈ toseq.nodes.g3 do acc + isroot(g3, @e)/for(acc)
let layerarcs =
 asset.for acc = toseq.arcstoroots, @e ∈ layers do acc + layerarcsR(arcstoroots, @e)/for(acc)
let a = newgraph.toseq.layerarcs
let b = sinksfirst.a + singlenodelayers.layers
assignx(false, layerX, b, empty:set.nodeinfo.T, vertarcs, 1)

Function alignUR(g:graph.T, layers:seq.seq.T, marked:set.arc.T, layerX:set.nodeinfo.T)set.nodeinfo.T
let vertarcs = findvertarcsUR(deletearcs(g, marked), layers)
let g3 = newgraph.vertarcs
let arcstoroots =
 asset.for acc = empty:seq.arc.T, @e ∈ toseq.nodes.g3 do acc + isroot(g3, @e)/for(acc)
let layerarcs =
 asset.for acc = toseq.arcstoroots, e2 ∈ layers do acc + layerarcs(arcstoroots, e2)/for(acc)
let a = newgraph.toseq.layerarcs
let b = sinksfirst.a + singlenodelayers.layers
assignx(true, layerX, b, empty:set.nodeinfo.T, vertarcs, 1)

function singlenodelayers(a:seq.T)seq.T if length.a = 1 then a else empty:seq.T

function singlenodelayers(a:seq.seq.T)seq.T for acc = empty:seq.T, @e ∈ a do acc + singlenodelayers.@e /for(acc)

function assignx(RtoL:boolean
, layers:set.nodeinfo.T
, list:seq.T
, assigned:set.nodeinfo.T
, vertarcs:seq.arc.T
, i:int
)set.nodeinfo.T
{ assign x values.Direction can either be Right to left or left to Right.Negative x's are assign when RtoL ' }
if i > length.list then assigned
else
 let node = list_i
 if nodeinfo(node, 0, 0) ∈ assigned then assignx(RtoL, layers, list, assigned, vertarcs, i + 1)
 else
  let q = lookup(layers, nodeinfo(node, 0, 0))_1
  assignx(RtoL
  , layers
  , list
  , assignvert(RtoL
  , layers
  , vertarcs
  , assigned
  , q
  , if RtoL then-1 else 1
  , empty:seq.nodeinfo.T
  )
  , vertarcs
  , i + 1
  )

----------------------

Final step is to merge multiple layouts into one.

Function assignx(g:graph.T, dummy:set.T, layers:seq.seq.T)set.nodeinfo.T
let marked = asset.type1conflicts(g, dummy, layers)
let layerX = posindegree(g, layers)
let UL = alignUL(g, layers, marked, layerX)
let UR = alignUR(g, layers, marked, layerX)
let m = for acc = 0, @e ∈ toseq.UR do min(acc, x.@e)/for(acc)
asset.for acc = empty:seq.nodeinfo.T, @e ∈ arithseq(cardinality.UL, 1, 1)do acc + merge(UL, UR, m, @e)/for(acc)

function merge(UL:set.nodeinfo.T, UR:set.nodeinfo.T, m:int, i:int)nodeinfo.T
let ul = UL_i
nodeinfo(n.ul,(x.ul + x.UR_i - m + 1) * 2 / 2, y.ul) 



________________

use graph.nodeinfo.T

use seq.arc.nodeinfo.T

type graphlayout is  g:graph.T, nodeinfo:set.nodeinfo.T, paths:seq.seq.T

Export  nodeinfo(graphlayout.T) set.nodeinfo.T

Export  paths(graphlayout.T) seq.seq.T

use otherseq.seq.seq.T

Function layout(  g:graph.T,allpaths:boolean) graphlayout.T
let lg = layer.makeDAG.g
 let paths= for  acc=empty:seq.seq.T,      a /in   toseq.arcs.g.lg do
     if tail.a /nin nodes.g /or   not.allpaths /and head.a /in nodes.g     then acc
     else  
      let path=[tail.a]+followpath(head.a,g.lg,nodes.g)
   let acc1=   if arc(first.path,last.path) /in arcs.g  then
        acc+path
      else acc
     if arc(last.path,first.path) /in arcs.g  then
        acc1+reverse.path
      else acc1 
/for(acc)
graphlayout(g,assignx(g.lg, nodes.g.lg \ nodes.g, layers.lg),paths)

 for  acc=empty:seq.arc.nodeinfo.T,      a /in   toseq.arcs.g.lg do
    acc+  arc(lookup(t, nodeinfo(tail.a,0,0))_1,lookup(t, nodeinfo(head.a,0,0))_1)
/for(newgraph.acc)

function followpath( a:T,lg:graph.T,nodes:set.T ) seq.T
     if a /in nodes   then  [a]
      else  [a]+followpath(successors(lg,a)_1,lg,nodes)  

  
________________

Export type:nodeinfo.T

type nodeinfo is n:T, x:int, y:int,  seperation:int

seperation is"width"of node in layer.y is the layer value, x is the posistion within the layer.

Export n(nodeinfo.T)T

Export x(nodeinfo.T)int

Export y(nodeinfo.T)int


Export seperation(nodeinfo.T)int

Function nodeinfo(n:T, x:int, y:int)nodeinfo.T nodeinfo(n, x, y,  1)


unbound =(T, T)boolean

function =(a:nodeinfo.T, b:nodeinfo.T)boolean n.a = n.b

/Function maxx(a:seq.nodeinfo.T)int for acc = 0, @e ∈ a do max(acc, rightedge.@e)/for(acc)


/Function maxy(a:seq.nodeinfo.T)int for acc = 0, @e ∈ a do max(acc, y.@e)/for(acc)

function posindegree(g:graph.T, layers:seq.seq.T, layer:int, node:T)nodeinfo.T
let x = findindex(node, layers_layer)
if x > length.layers_layer then posindegree(g, layers, layer + 1, node)
else
 let d = length.toseq.predecessors(g, node)
 nodeinfo(node, x, layer,  if d > 2 then d else 1)

function pos(layers:seq.seq.T, layer:int, node:T)nodeinfo.T
let x = findindex(node, layers_layer)
if x > length.layers_layer then pos(layers, layer + 1, node)else nodeinfo(node, x, layer)

function defaultpos(g:graph.T, layers:seq.seq.T)set.nodeinfo.T
let a = for acc = empty:seq.T, @e ∈ layers do acc + @e /for(acc)
for acc = empty:set.nodeinfo.T, @e ∈ a do acc + pos(layers, 1, @e)/for(acc)

function posindegree(g:graph.T, layers:seq.seq.T)set.nodeinfo.T
let a = for acc = empty:seq.T, @e ∈ layers do acc + @e /for(acc)
for acc = empty:set.nodeinfo.T, @e ∈ a do acc + posindegree(g, layers, 1, @e)/for(acc)


