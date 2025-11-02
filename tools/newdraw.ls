Module newdraw.>>.T

use arc.>>.T

use graph.T

use set.T

use orderNodes.T

use seq1.>>.T

use set.>>.T

use brandeskopf

use arc.int

use set.arc.int

use seq1.int

use layernode

use arc.layernode

use graph.arc.layernode

use seq.arc.layernode

use seq1.layernode

use set.layernode

use sort.layernode

use svg

use seq.path

use standard

unbound %(>>.T) seq.word

unbound =(>>.T, >>.T) boolean

unbound nodeLabel(>>.T) seq.seq.word

unbound arcLabel(T) seq.seq.word

unbound head(T) >>.T

unbound tail(T) >>.T

unbound reverse(T) T

Function drawgraph(arcs:seq.T, include:set.>>.T, exclude:set.>>.T) seq.word
for arclist2 = empty:seq.T, a ∈ arcs
do
 if head.a ∈ exclude ∨ not.isempty.include ∧ tail.a ∉ include then arclist2
 else arclist2 + a,
drawgraph.newgraph.arclist2

Function sublayer2(org:graph.T) rr5
let arcstoreverse2 = arcsToReverse.org
for reversed2 = empty:set.arc.int, reversedarcs = empty:seq.T, arc ∈ arcstoreverse2
do
 next(
  reversed2 + arc(findindex(nodes.org, head.arc), findindex(nodes.org, tail.arc))
  , reversedarcs + reverse.arc
 )
let gin = replacearcs(org, asset.arcstoreverse2, asset.reversedarcs)
for
 g = gin
 , xx = empty:seq.arc.layernode
 , lowlayersnodes = empty:seq.layernode
 , remaining = nodes.gin
 , nextpos = [1]
 , lastNodeNo = n.nodes.gin
 , paths1 = empty:seq.path
while not.isempty.remaining
do
 for
  xx2 = xx
  , acc2 = lowlayersnodes
  , handled = empty:set.>>.T
  , lastNodeNo2 = lastNodeNo
  , nextpos2a = nextpos
  , paths2 = paths1
  , n ∈ toseq.remaining
 do
  let preds = toseq.predecessors(g, n)
  for nopred = true, e ∈ preds while nopred do e ∉ remaining,
  if not.nopred then next(xx2, acc2, handled, lastNodeNo2, nextpos2a, paths2)
  else
   let newnode = layernode(findindex(nodes.g, n), n.nextpos, (n.nextpos)#nextpos2a)
   let nextpos2 = nextpos2a >> 1 + (pos.newnode + 1)
   for xx3 = xx2, lastNodeNo3 = lastNodeNo2, nextpos3 = nextpos2, paths3 = paths2, e ∈ preds
   do
    let find = findindex(nodes.g, e)
    let t = binarysearch>3(lowlayersnodes, layernode(find, 0, 0))#lowlayersnodes
    {adding new arc (t, newnode)}
    let nodummynodes = layer.newnode - layer.t - 1
    let a = lookup(reversed2, arc(no.t, no.newnode))
    let class =
     if isempty.a then 1#"arc"
     else if e ∈ predecessors(org, n) then 1#"both"
     else 1#"reversed",
    let path =
     path(
      no.t
      , no.newnode
      , if nodummynodes = 0 then 0 else lastNodeNo3 + 1
      , lastNodeNo3 + nodummynodes
      , class
     ),
    if nodummynodes = 0 then next(xx3 + arc(t, newnode), lastNodeNo3, nextpos3, paths3 + path)
    else
     for
      newarcs = empty:seq.arc.layernode
      , last = t
      , nextpos4 = subseq(nextpos3, 1, layer.t)
      , nn ∈ arithseq(nodummynodes, 1, lastNodeNo3 + 1)
     do
      let tmp = layernode(nn, layer.last + 1, (layer.last + 1)#nextpos3),
      next(newarcs + arc(last, tmp), tmp, nextpos4 + (pos.tmp + 1))
     let newarcs1 = newarcs + arc(last, newnode)
     let z = nextpos4 + nextpos3 << n.nextpos4,
     assert n.z = n.nextpos3 report "DIFF",
     next(xx3 + newarcs1, lastNodeNo3 + nodummynodes, z, paths3 + path),
   {end adding new arc (t, newnode)}
   next(xx3, acc2 + newnode, handled + n, lastNodeNo3, nextpos3, paths3)
 assert n.handled > 0 report
  let on = orderNodes(nodes.g, arcs.g)
  for txt = "", k = empty:seq.>>.T, e ∈ on
  do
   if isempty.k then next(txt, k + e)
   else if 1#k = e then
    if n.k = 1 then next(txt, empty:seq.>>.T)
    else next(txt + "/br^(k)", empty:seq.>>.T)
   else next(txt, k + e),
  "XXX^(toseq.remaining) /br^(txt)",
 next(g, xx2, sort>3.acc2, remaining \ handled, nextpos2a + [1], lastNodeNo2, paths2)
for txt = "", e ∈ xx
do
 assert layer.tail.e - layer.head.e =-1 report "SDFDS",
 txt + "/br^(tail.e)----^(head.e)^(layer.tail.e - layer.head.e)"
let gg1 = newgraph.xx + lowlayersnodes,
rr5(reduceCrossings.gg1, paths1, n.nodes.org)

function %(a:arc.>>.T) seq.word "{^(tail.a)^(head.a)}"

function =(a:arc.>>.T, b:arc.>>.T) boolean tail.a = tail.b ∧ head.a = head.b

Function arcsToReverse(g3:graph.T) seq.T
let on = orderNodes(nodes.g3, arcs.g3)
for arcstoreverse2 = empty:seq.T, k = empty:seq.>>.T, e ∈ on
do
 if isempty.k then next(arcstoreverse2, k + e)
 else if 1#k = e then
  if n.k = 1 then next(arcstoreverse2, empty:seq.>>.T)
  else
   for arcstoreverse3 = arcstoreverse2, e2 ∈ k
   do
    for arcstoreverse4 = arcstoreverse3, arc ∈ toseq.arcstosuccessors(g3, e2)
    do
     let e3 = head.arc,
     if findindex(k, e2) > findindex(k, e3) then arcstoreverse4 + arc else arcstoreverse4,
    arcstoreverse4,
   next(arcstoreverse3, empty:seq.>>.T)
 else next(arcstoreverse2, k + e),
arcstoreverse2

Function addscc(s:seq.>>.T, scc:seq.>>.T) seq.>>.T
{if n.scc = 1 then s else}
s + scc + 1#scc

use seq.seq.int

use sort.seq.int

use uniqueids

use seq.seq.word

unbound arcLabel(set.T, >>.T, >>.T) seq.seq.word

Function drawgraph(g33:graph.T) seq.word
let r = sublayer2.g33
let nodepos = assignx(g.r, orgNodeCount.r, 12)
let nodes = toseq.nodes.g33
let paths2 = paths2.r
let orgNodeCount = n.nodes
let startid = requestids(orgNodeCount + n.paths2) + requestids.1
for out = "", maxx0 = 0, maxy0 = 0, id = startid, lastno = 0, draw4 = "", a ∈ sort>3.paths2
do
 let startnode = (1#a)#nodepos
 for id2 = id, nodetxt2 = "", ii = lastno
 while ii < no.startnode
 do next(id2 + 1, nodetxt2 + nodetext((ii + 1)#nodepos, id2, nodes), ii + 1)
 let nodetxt = nodetxt2
 let id1 = id2
 let newdraw =
  if no.startnode = lastno then draw4 + ",^(id1)"
  else draw4 + "], [^(id1 - 1),^(id1)"
 let from = if n.a = 2 then pos.startnode else 0
 for d = "M 0 0", from0 = 0, from1 = from, maxx1 = maxx0, maxy1 = maxy0, p ∈ a << 1
 do
  let xy = p#nodepos
  let nodex = layer.xy,
  let nodey = pos.xy,
  next(d + "L" + %.nodex + %.nodey, from1, pos.xy, max(nodex, maxx1), max(nodey, maxy1))
 let pth = svgpath("arcs", [toword.id1], d)
 let label = arcLabel(arcs.g33, (1#a)#nodes.g33, (1^a)#nodes.g33),
 let arclabel =
  if isempty.label then ""
  else
   "/tag <text /sp class = /tag^(dq."nodes") > /tag <textPath /sp href = /tag^(dq.[merge("#" + toword.id1)]) startOffset = /tag^(dq."100%") text-anchor = /tag^(dq."end") > /tag <tspan /sp = /tag^(dq."-0.1") >^(2#label) /tag </tspan></textPath></text>"
    + encodeword.[char.10],
 next(
  out + nodetxt + pth + encodeword.[char.10] + arclabel
  , maxx1
  , maxy1
  , id1 + 1
  , no.startnode
  , newdraw
 )
for txt = out, id2 = id, i = lastno + 1
while i ≤ orgNodeCount
do next(txt + nodetext(i#nodepos, id2, nodes), id2 + 1, i + 1),
svg(
 [
  ".arcs {fill:none ; stroke:black ; stroke-width:.07 ;}"
  , ".nodes {dominant-baseline:hanging; font: 1px sans-serif ; stroke-width:.1 ;}"
  , "svg g:hover text {opacity:1;}"
  , "svg g:hover rect {opacity:1;}"
 ]
 , [
  "id = svg10"
  , "viewBox 5 /sp-1^(%(maxx0 + 5))^(%(maxy0 + 5))"
  , "onload [^(draw4 << 2)]].forEach (shiftstart)"
 ]
 , txt
)
 + drawscript

function nodetext(startnode:layernode, htmlid:int, nodes:seq.>>.T) seq.word
let nodex = layer.startnode
let nodey = pos.startnode
let tmp0 = nodeLabel.(no.startnode)#nodes
let name = 2#tmp0
let hover = 3#tmp0,
text("nodes", [toword.htmlid], nodex, nodey, name)
 + hovertext(no.startnode, nodex, nodey, hover)
 + encodeword.[char.10] 