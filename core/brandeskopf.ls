Module brandeskopf

Graph layout based on:Fast and Simple Horizontal Coordinate Assignment Ulrik Brandes and Boris Kopf, 2002

use set.arc.int

use graph.int

use layergraph

use makeDAG.int

use otherseq.int

use seq.seq.int

use set.int

use seq.nodeinfo

use set.nodeinfo

use standard

Export type:nodeinfo

Export n(nodeinfo) int

Export seperation(nodeinfo) int

Export x(nodeinfo) int

Export y(nodeinfo) int

Function >1(a:nodeinfo, b:nodeinfo) ordering n.a >1 n.b

function iis(lg:layeredgraph, node:int) seq.int
{returns upper neighbor of inner segment ending at node}
if node ≤ orgNodeCount.lg then {not inner segment} empty:seq.int
else
 let p = predecessors(g.lg, node),
 if isempty.p then empty:seq.int else [1#p]

function type1conflicts(lg:layeredgraph) seq.arc.int
{step one is to find type1 conflicts, that is arcs that cross a inner arc}
for
 acc0 = empty:seq.arc.int
 , upperlayer = 1#layers.lg
 , currentlayer ∈ subseq(layers.lg, 2, n.layers.lg - 1)
do
 {In paper, upperlayer = L_i and currentlayer = L_ (i+1)}
 for acc = empty:seq.arc.int, k0 = 0, l = 0, l1 ∈ arithseq(n.currentlayer, 1, 1)
 do
  let node = l1#currentlayer
  let x = iis(lg, node),
  if isempty.x ∨ node ≠ 1^currentlayer then next(acc, k0, l)
  else
   let k1 = findindex(upperlayer, 1#x)
   for acc3 = empty:seq.arc.int, start ∈ subseq(currentlayer, l + 1, l1 + 1)
   do
    let k = findindex(upperlayer, start),
    acc3 + if k < k0 ∨ k > k1 then [arc(start, k1)] else empty:seq.arc.int,
   next(acc + acc3, k1, l1),
 next(acc0 + acc, currentlayer),
acc0

-------------------------------

function findvertarcsUL(g:graph.int, layers:seq.seq.int, marked:set.arc.int) seq.arc.int
{Step 2 is to find vertical alignments. This will return arcs that will have the two nodes with the same x value. Inner arcs are prime canidates for this vertial alignment.}
for acc = empty:seq.arc.int, lastlayer = 1#layers, currentlayer ∈ layers << 1
do
 for result = empty:seq.arc.int, r = 0, assigned = empty:seq.int, node ∈ currentlayer
 do
  let preds = toseq.predecessors(g, node),
  if n.preds > 0 then
   for upperidx = empty:seq.int, @e ∈ preds
   do upperidx + findindex(lastlayer, @e)
   let tmp = (n.upperidx + 1) / 2,
   for
    result1 = result
    , r1 = r
    , assigned1 = assigned
    , m ∈ if tmp * 2 = n.upperidx then [tmp, tmp + 1] else [tmp]
   do
    let m2 = m#upperidx
    let v = m2#lastlayer,
    if r1 < m2 ∧ between(m2, 1, n.lastlayer) ∧ node ∉ assigned1 then
     let newarc = arc(v, node),
     if newarc ∈ marked then next(result1, m2, assigned1)
     else next(result1 + newarc, m2, assigned1 + node)
    else next(result1, r1, assigned1),
   next(result1, r1, assigned1)
  else next(result, r, assigned),
 next(acc + result, currentlayer),
acc

-----------

use otherseq.arc.int

use otherseq.seq.int

type block is levels:seq.lev, start:lev, blk:seq.int, class:int

function block(levels:seq.lev, blk:seq.int) block block(levels, (1#blk)#levels, blk, 1)

function setclass(b:block, class:int) block block(levels.b, start.b, blk.b, class)

type lev is n:int, layer:int, x:int

function >1(a:lev, b:lev) ordering n.a >1 n.b

function %(a:lev) seq.word "^(n.a)^(layer.a)^(x.a)"

function %(a:ordering) seq.word [toword.a]

use otherseq.lev

function levels(s:seq.seq.int) seq.lev
{assignment of node to level}
for acc = empty:seq.lev, level = 1, l ∈ s
do
 for acc1 = acc, i = 1, n ∈ l do next(acc1 + lev(n, level, i), i + 1),
 next(acc1, level + 1),
sort.acc

function >1(a:block, b:block) ordering
let level = levels.a
let l1 = start.a
let l2 = start.b
let diff = layer.l2 - layer.l1,
if diff = 0 then x.l1 >1 x.l2
else if diff > 0 then if diff + 1 > n.blk.a then LT else x.((diff + 1)#blk.a)#level >1 x.l2
else if-diff + 1 > n.blk.b then GT
else x.l1 >1 x.((-diff + 1)#blk.b)#level

use otherseq.block

use set.block

function %(b:block) seq.word "{^(class.b)} {^(start.b)}^(blk.b)"

function align(
RtoL:boolean
, g:graph.int
, layers0:seq.seq.int
, marked:set.arc.int
) set.nodeinfo
{For providing horizontal alignment. if RtoL then alignUR else alignUL}
let layers =
 if not.RtoL then layers0
 else
  for layers3 = empty:seq.seq.int, l ∈ layers0
  do layers3 + reverse.l,
  layers3
let vertarcs = findvertarcsUL(g, layers, marked)
for layerorder = empty:seq.int, l ∈ layers
do layerorder + l
for blocks = empty:seq.seq.int, all = empty:seq.int, o = layerorder, a ∈ vertarcs
do
 for newo = o, newblks = blocks, allx = empty:seq.int
 while tail.a ≠ 1#newo
 do
  if 1#newo ∈ all then next(newo << 1, newblks, allx)
  else next(newo << 1, newblks + [1#newo], allx + 1#newo)
 for i = 1, x ∈ newblks while tail.a ∉ x do i + 1,
 if i > n.newblks then next(newblks + [tail.a, head.a], all + allx + [tail.a, head.a], newo)
 else
  next(
   subseq(newblks, 1, i - 1) + (i#newblks + head.a) + newblks << i
   , all + allx + head.a
   , newo
  )
for more = blocks, n ∈ toseq(nodes.g \ asset.all)
do more + [n]
{assert false report %n.blocks+"
/br"+%.vertarcs+"
/br"+%.toseq (nodes.g \ asset.all)}
let level = levels.layers
for classlist = empty:seq.seq.block, maxlayer = 1, classno = 0, b ∈ more
do
 let val = block(level, b)
 for class = 1, place = 0, blks ∈ classlist
 while place = 0
 do
  let i = binarysearch(blks, val),
  if-i ≤ n.blks ∧ maxlayer < layer.start.val ∧ x.start.val < x.start.(-i)#blks then next(class + 1, 0)
  else next(class,-i),
 let val2 = setclass(val, class),
 next(
  if n.classlist < class.val2 then classlist + [val2]
  else
   let blks = (class.val2)#classlist,
   replace(classlist, class.val2, subseq(blks, 1, place - 1) + [val2] + subseq(blks, place, n.blks))
  , max(layer.start.val, maxlayer)
  , max(classno, class.val)
 )
{assert false report" HH"+%n.classlist}
for assigned0 = empty:set.nodeinfo, blks ∈ classlist
do
 for assigned = assigned0, x = {if not.RtoL then 1 else 18} 1, b ∈ blks
 do
  for assigned1 = assigned, node ∈ blk.b
  do
   let l2 = layer.node#level,
   assigned1 + nodeinfo(node, x, l2),
  next(assigned1, {if not.RtoL then x+1 else x-1)} x + 1),
 assigned,
assigned0

use otherseq.seq.block

----------------------

Function assignx(lg:layeredgraph) set.nodeinfo
{Final step is to merge multiple layouts into one.}
let marked = asset.type1conflicts.lg
let UL = align(false, g.lg, layers.lg, marked)
let UR = align(true, g.lg, layers.lg, marked)
assert n.UL = n.nodes.g.lg report %.toseq.UL + %n.layers.lg
for max = 1, e ∈ toseq.UR do max(max, x.e)
for acc = empty:seq.nodeinfo, i ∈ arithseq(n.UL, 1, 1)
do
 let ul = i#UL,
 acc + nodeinfo(n.ul, (x.ul + max + 1 - x.i#UR) / 2, y.ul),
asset.acc

-------------------------------

Function paths(g:graph.int, lg:layeredgraph) seq.seq.int
for px = empty:seq.seq.int, node ∈ arithseq(orgNodeCount.lg, 1, 1)
do
 for acc1 = px, s ∈ toseq.successors(g.lg, node)
 do
  for path = [node, s], last = s
  while last > orgNodeCount.lg
  do
   let tmp = 1#successors(g.lg, last),
   next(path + tmp, tmp)
  let acc2 = if arc(1#path, 1^path) ∈ arcs.g then acc1 + path else acc1,
  if arc(1^path, 1#path) ∈ arcs.g then acc2 + reverse.path else acc2,
 acc1,
px

-------------------------------

type nodeinfo is
n:int
, x:int
, y:int
, seperation:int {seperation is" width" of node in layer.y is the layer value
, x is the posistion within the layer.}

Function %(a:nodeinfo) seq.word "{^(n.a)^(x.a)^(y.a)}"

use otherseq.nodeinfo

Function nodeinfo(n:int, x:int, y:int) nodeinfo nodeinfo(n, x, y, 1) 