Module brandeskopf

Graph layout based on:Fast and Simple Horizontal Coordinate Assignment Ulrik Brandes and Boris Kopf, 2002

use seq1.block

use seq1.seq.block

use set.block

use seq1.int

use seq.int

use seq1.seq.int

use seq.seq.int

use set.int

use layernode

use seq1.layernode

use seq.layernode

use sort.layernode

use real

use standard

use seq1.seq.layernode

function =(a:layernode, b:layernode) boolean no.a = no.b

function type1conflicts(g:graph.arc.layernode, orgNodeCount:int) seq.arc.layernode
for layers = empty:seq.seq.layernode, b = 1, idx = 1, e ∈ toseq.nodes.g + layernode(0, 0, 0)
do
 if n.layers + 1 = layer.e then next(layers, b, idx + 1)
 else next(layers + toseq.subseq(nodes.g, b, idx - 1), idx, idx + 1)
for acc0 = empty:seq.arc.layernode, upperlayer = layers sub 1, currentlayer ∈ layers << 1
do
 {In paper, upperlayer = L_i and currentlayer = L_ (i+1)}
 for acc = empty:seq.arc.layernode, k0 = 0, l = 0, node ∈ currentlayer
 do
  let l1 = pos.node,
  if node ≠ currentlayer sub n.currentlayer then next(acc, k0, l)
  else if no.node ≤ orgNodeCount then {not inner segment} next(acc, k0, l)
  else
   let p = predecessors(g, node),
   if isempty.p then next(acc, k0, l)
   else
    {iis is upper neighbor of inner segment ending at node}
    let iis = p sub 1
    let k1 = findindex(upperlayer, iis),
    for acc3 = empty:seq.arc.layernode, start ∈ subseq(currentlayer, l + 1, l1 + 1)
    do
     let k = findindex(upperlayer, start),
     acc3 + if k < k0 ∨ k > k1 then [arc(start, {k1} iis)] else empty:seq.arc.layernode,
    next(acc + acc3, k1, l1),
 next(acc0 + acc, currentlayer),
acc0

-------------------------------

function findvertarcsUL(
RtoL:boolean
, g:graph.arc.layernode
, layers2:seq.seq.layernode
, marked:set.arc.layernode
) seq.arc.layernode
{Step 2 is to find vertical alignments. This will return arcs that will have the two nodes with the same x value. Inner arcs are prime canidates for this vertial alignment.}
for result1 = empty:seq.arc.layernode, lastlayer = layers2 sub 1, currentlayer ∈ layers2 << 1
do
 for result2 = empty:seq.arc.layernode, r = 0, assigned = empty:seq.int, node ∈ currentlayer
 do
  let preds = toseq.predecessors(g, node),
  if n.preds > 0 then
   for upperidx = empty:seq.int, @e ∈ preds
   do
    let t2 = if RtoL then n.lastlayer + 1 - pos.@e else pos.@e,
    upperidx + t2
   let tmp = (n.upperidx + 1) / 2,
   for
    result3 = result2
    , r1 = r
    , assigned1 = assigned
    , m ∈ if tmp * 2 = n.upperidx then [tmp, tmp + 1] else [tmp]
   do
    let m2 = upperidx sub m,
    if r1 < m2 ∧ between(m2, 1, n.lastlayer) ∧ no.node ∉ assigned1 then
     let newarc = arc(lastlayer sub m2, node),
     if newarc ∈ marked then next(result3, m2, assigned1)
     else next(result3 + newarc, m2, assigned1 + no.node)
    else next(result3, r1, assigned1),
   next(result3, r1, assigned1)
  else next(result2, r, assigned),
 next(result1 + result2, currentlayer),
result1

-----------

type block is levels:seq.layernode, start:layernode, blk:seq.int, class:int

function block(levels:seq.layernode, blk:seq.int) block
block(levels, levels sub (blk sub 1), blk, 1)

function setclass(b:block, class:int) block block(levels.b, start.b, blk.b, class)

function >1(a:block, b:block) ordering
let level = levels.a
let l1 = start.a
let l2 = start.b
let diff = layer.l2 - layer.l1,
if diff = 0 then pos.l1 >1 pos.l2
else if diff > 0 then if diff + 1 > n.blk.a then LT else pos.level sub ((blk.a) sub (diff + 1)) >1 pos.l2
else if-diff + 1 > n.blk.b then GT
else pos.l1 >1 pos.level sub ((blk.b) sub (-diff + 1))

function %(b:block) seq.word "{:(class.b)} {:(start.b)}:(blk.b)"

function align(
RtoL:boolean
, gin:graph.arc.layernode
, marked:set.arc.layernode
) seq.layernode
{For providing horizontal alignment. if RtoL then alignUR else alignUL}
for
 layers4 = empty:seq.seq.layernode
 , thislayer = empty:seq.layernode
 , layerorder = empty:seq.layernode
 , n2 ∈ toseq.nodes.gin + layernode(0, 0, 0)
do
 let layerno = n.layers4 + 1,
 if layer.n2 = layerno then
  let layer = if RtoL then [n2] + thislayer else thislayer + n2,
  next(layers4, layer, layerorder)
 else
  let tmp =
   if RtoL then
    for acc1 = empty:seq.layernode, i = 1, e ∈ thislayer
    do next(acc1 + layernode(no.e, layerno, i), i + 1),
    acc1
   else thislayer,
  next(layers4 + thislayer, [n2], layerorder + tmp)
let level = sort>3.layerorder
let vertarcs = findvertarcsUL(RtoL, gin, layers4, marked)
for blocks = empty:seq.seq.int, all = empty:seq.int, o5 = layerorder, aa ∈ vertarcs
do
 for newo = o5, newblks = blocks, allx = empty:seq.int
 while no.tail.aa ≠ no.newo sub 1
 do
  if no.newo sub 1 ∈ all then next(newo << 1, newblks, allx)
  else next(newo << 1, newblks + [no.newo sub 1], allx + no.newo sub 1)
 for i = 1, x ∈ newblks while no.tail.aa ∉ x do i + 1,
 if i > n.newblks then next(newblks + [no.tail.aa, no.head.aa], all + allx + [no.tail.aa, no.head.aa], newo)
 else
  next(
   subseq(newblks, 1, i - 1) + (newblks sub i + no.head.aa) + newblks << i
   , all + allx + no.head.aa
   , newo
  )
let tmp = asset.all
for more = blocks, e ∈ toseq.nodes.gin
do if no.e ∈ tmp then more else more + [no.e]
{assert false report %n.blocks+"
/br"+%.vertarcs+"
/br"+%.toseq (nodes.g \ asset.all)}
for classlist = empty:seq.seq.block, maxlayer = 1, classno = 0, b ∈ more
do
 let val = block(level, b)
 for class = 1, place = 0, blks ∈ classlist
 while place = 0
 do
  let i = binarysearch(blks, val),
  if-i ≤ n.blks ∧ maxlayer < layer.start.val ∧ pos.start.val < pos.start.blks sub-i then next(class + 1, 0)
  else next(class,-i),
 let val2 = setclass(val, class),
 next(
  if n.classlist < class.val2 then classlist + [val2]
  else
   let blks = classlist sub class.val2,
   replace(classlist, class.val2, subseq(blks, 1, place - 1) + [val2] + subseq(blks, place, n.blks))
  , max(layer.start.val, maxlayer)
  , max(classno, class.val)
 )
{assert false report" HH"+%n.classlist}
for assigned0 = empty:seq.layernode, blks ∈ classlist
do
 for assigned = assigned0, x = {if not.RtoL then 1 else 18} 1, b ∈ blks
 do
  for assigned1 = assigned, node ∈ blk.b
  do
   let l2 = layer.level sub node,
   assigned1 + layernode(node, l2, x),
  next(assigned1, {if not.RtoL then x+1 else x-1)} x + 1),
 assigned,
assigned0

----------------------

use graph.arc.layernode

use set.layernode

use set.arc.layernode

use seq.arc.layernode

use arc.layernode

Function assignx(gin:graph.arc.layernode, orgNodeCount:int, scaley:int) seq.layernode
{Final step is to merge multiple layouts into one.}
let marked = asset.type1conflicts(gin, orgNodeCount)
let UL = sort>3.align(false, gin, marked)
let UR = sort>3.align(true, gin, marked)
{assert n.UL = n.nodes.g report" assignx:(n.UL):(n.nodes.g)"+%.UL+%n.layers}
for
 maxlayer = empty:seq.int
 , maxpos = 1
 , lastlayer1 = 1
 , e ∈ sort.align(true, gin, marked) + layernode(0, 0, 0)
do
 if lastlayer1 = layer.e then next(maxlayer, max(maxpos, pos.e), lastlayer1)
 else next(maxlayer + maxpos, pos.e, layer.e)
for acc = empty:seq.layernode, i ∈ arithseq(n.UL, 1, 1)
do
 let ul = UL sub i
 let x = 2 * (pos.ul + maxlayer sub layer.ul + 1 - pos.UR sub i) / 2,
 next(acc + layernode(no.ul, scaley * layer.ul, x))
let t = sort.align(true, gin, marked)
for change = empty:seq.layernode, last = layernode(1, 0, 0), e ∈ sort.acc
do
 if layer.e ≠ layer.last ∨ pos.e ≠ pos.last then next(change + e, e)
 else next(change + layernode(no.e, layer.e, pos.e + 1), e),
sort>3.change

-------------------------------

, xxseperation:int {seperation is" width" of node in layer.y is the layer value, x is the posistion within the layer.} 
