Module svggraph.T

use seq.arc.T

use set.arc.T

use seq.arcinfo.T

use set.arcinfo.T

use graph.T

use seq.nodeinfo.T

use set.nodeinfo.T

use seq.seq.T

use seq.T

use set.T

use otherseq.int

use seq.int

use sparseseq.int

use standard

use svg

use seq.seq.word

type svgdraw is record width:int, height:int, a:seq.word

Export type:nodeinfo.T

type nodeinfo is record n:T, x:int, y:int, width:int, seperation:int

seperation is"width"of node in layer.y is the layer value, x is the posistion within the layer.

Export n(nodeinfo.T)T

Export x(nodeinfo.T)int

Export y(nodeinfo.T)int

Export width(a:nodeinfo.T)int

Export seperation(nodeinfo.T)int

Function nodeinfo(n:T, x:int, y:int)nodeinfo.T nodeinfo(n, x, y, 0, 1)

Export nodeinfo(n:T, x:int, y:int, width:int, seperation:int)nodeinfo.T

unbound =(T, T)boolean

function =(a:nodeinfo.T, b:nodeinfo.T)boolean n.a = n.b

Function maxx(a:seq.nodeinfo.T)int a @ max(0, rightedge.@e)

function rightedge(a:nodeinfo.T)int x.a + width.a

Function maxy(a:seq.nodeinfo.T)int a @ max(0, y.@e)

Function zerowidth(a:seq.T, b:nodeinfo.T)nodeinfo.T
 if n.b ∈ a then b else nodeinfo(n.b, x.b, y.b, 0, seperation.b)

Function zerowidth(a:seq.T, b:set.nodeinfo.T)set.nodeinfo.T
 toseq.b @ +(empty:set.nodeinfo.T, zerowidth(a, @e))

Function posindegree(g:graph.T, layers:seq.seq.T, layer:int, node:T)nodeinfo.T
 let x = findindex(node, layers_layer)
  if x > length.layers_layer then posindegree(g, layers, layer + 1, node)
  else
   let d = length.toseq.predecessors(g, node)
    nodeinfo(node, x, layer, 0, if d > 2 then d else 1)

Function pos(layers:seq.seq.T, layer:int, node:T)nodeinfo.T
 let x = findindex(node, layers_layer)
  if x > length.layers_layer then pos(layers, layer + 1, node)else nodeinfo(node, x, layer)

Function defaultpos(g:graph.T, layers:seq.seq.T)set.nodeinfo.T
 let a = layers @ +(empty:seq.T, @e)
  a @ +(empty:set.nodeinfo.T, pos(layers, 1, @e))

Function posindegree(g:graph.T, layers:seq.seq.T)set.nodeinfo.T
 let a = layers @ +(empty:seq.T, @e)
  a @ +(empty:set.nodeinfo.T, posindegree(g, layers, 1, @e))

Function tosvg(arcs:seq.arc.T, nodes:seq.T, positions:set.nodeinfo.T)seq.word
 let arci = arcs @ +(empty:seq.arcinfo.T, arcinfo.@e)
  tosvg(arci, nodes, positions)

Function tosvg(arci:seq.arcinfo.T, nodes:seq.T, positions:set.nodeinfo.T)seq.word
 let r = zerowidth(nodes, positions)
 let minx = toseq.r @ min(x.r_1, x.@e)
 let vertnodesize = 16
 let a = toseq.r @ layerwidths(sparseseq.1, @e)
 let p2 = toseq.r @ +(empty:set.nodeinfo.T, adjust(vertnodesize, minx, a, @e))
 let g = arci @ +(empty:set.arcinfo.T, toarcinfo(p2, @e))
  svg(["text { fill:black }"], toseq.p2 @ +("", svgnode(vertnodesize, g, p2, @e)), maxx.toseq.p2, maxy.toseq.p2)

Function svgnode(vertnodesize:int, info:set.arcinfo.T, s:set.nodeinfo.T, p:nodeinfo.T)seq.word
 let arcstonode = findelement2(info, arcinfo(arc(n.p, n.p),"", 0))
  {(if width.p > 0 then text("text", x.p, y.p, nodetotext.n.p)else"")
  + arithseq(length.toseq.arcstonode, 1, 1) @ +("", drawarc(vertnodesize, p, toseq.arcstonode, @e))}

function drawarc(vertnodesize:int, stop:nodeinfo.T, s:seq.arcinfo.T, i:int)seq.word
 let a = s_i
 let xstop = if width.a = 0 then x.stop else x.stop - width.a / 8 - 5
  line(x.a, y.a, xstop, y.stop + (i - 1) * if width.a = 0 then 0 else vertnodesize, backarc.a, false)
  + " &br"
  + text("text", xstop, y.stop + (i - 1) * vertnodesize, label.a)

function toarcinfo(s:set.nodeinfo.T, a:arcinfo.T)arcinfo.T
 let y = findelement(nodeinfo(tail.a.a, 0, 0), s)
  assert not.isempty.y report"node not found" + nodetotext.tail.a.a
  let start = y_1
   arcinfo(a.a, x.start + if width.start = 0 then 0 else width.start + 10, y.start, label.a, width.a, backarc.a)

Export type:arcinfo.T

type arcinfo is record a:arc.T, x:int, y:int, label:seq.word, width:int, backarc:boolean

Function arcinfo(a:arc.T, label:seq.word, width:int)arcinfo.T arcinfo(a, 0, 0, label, width, false)

Function arcinfo(a:arc.T)arcinfo.T arcinfo(a,"", 0)

Function setarc(a:arcinfo.T, b:arc.T, backarc:boolean)arcinfo.T arcinfo(b, x.a, y.a, label.a, width.a, backarc)

Export a(arcinfo.T)arc.T

Export label(arcinfo.T)seq.word

/Function b(a:arc.T)T head.a

/Function a(a:arc.T)T tail.a

function =(a:arcinfo.T, b:arcinfo.T)boolean
 a.a = a.b ∧ backarc.a = backarc.b

Function ?(a:arcinfo.T, b:arcinfo.T)ordering
 head.a.a ? head.a.b ∧ y.a ? y.b
 ∧ tail.a.a ? tail.a.b
 ∧ backarc.a ? backarc.b

Function ?2(a:arcinfo.T, b:arcinfo.T)ordering head.a.a ? head.a.b

unbound ?(a:T, b:T)ordering

unbound nodetotext(T)seq.word

function layerwidths(ws:seq.int, p:nodeinfo.T)seq.int
 let w = width.p
  if w > ws_(y.p)then replaceS(ws, y.p, [w])else ws

function adjust(vertnodesize:int, minx:int, layerwidths:seq.int, p:nodeinfo.T)nodeinfo.T
 assert true report"layer width" + layerwidths @ +("", toword.@e)
 let interlayerspace = 500
 let y = if y.p = 1 then 0
 else
  subseq(layerwidths, 1, y.p - 1) @ +(interlayerspace * (y.p - 1), @e)
  nodeinfo(n.p, 10 + y / 8, 10 + (x.p - minx) * vertnodesize, width.p / 8, seperation.p)

____________________________________