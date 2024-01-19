Module newsvg

use seq.arcpath

use set.arcpath

use brandeskopf

use seq.arc.int

use set.arc.int

use graph.int

use otherseq.int

use seq.int

use set.int

use seq.labeledNode

use set.labeledarc

use set.nodeinfo

use real

use standard

use uniqueids

use graph.word

use set.word

Export type:labeledarc

Export type:labeledNode

Export name(labeledNode) seq.word

Export labeledNode(class:seq.word, name:seq.word, hover:seq.word) labeledNode

Export labeledarc(tail:int, head:int, class:seq.word, label:seq.word) labeledarc

type labeledNode is class:seq.word, name:seq.word, hover:seq.word

type labeledarc is tail:int, head:int, class:seq.word, label:seq.word

type arcpath is arc:arc.int, d:seq.word, from:int

Function >1(a:labeledarc, b:labeledarc) ordering tail.a >1 tail.b ∧ head.a >1 head.b

Function >1(a:arcpath, b:arcpath) ordering
head.arc.a >1 head.arc.b ∧ tail.arc.a >1 tail.arc.b

Function drawgraph(arcs:seq.arc.word, include:set.word, exclude:set.word) seq.word
for arclist2 = empty:seq.arc.int, nodes = empty:seq.labeledNode, a ∈ arcs
do
 if head.a ∈ exclude ∨ not.isempty.include ∧ tail.a ∉ include then next(arclist2, nodes)
 else
  let findhead = find(nodes, [head.a])
  let nodes1 = if findhead > n.nodes then nodes + labeledNode("", [head.a], "") else nodes
  let findtail = find(nodes1, [tail.a]),
  let nodes2 = if findtail > n.nodes1 then nodes1 + labeledNode("", [tail.a], "") else nodes1,
  next(arclist2 + arc(findtail, findhead), nodes2),
drawgraph(newgraph.arclist2, nodes, empty:set.labeledarc)

function find(a:seq.labeledNode, name:seq.word) int
for idx = 1, e ∈ a while name ≠ name.e do idx + 1,
idx

function scalex(x:int) int x * 12

function scaley(y:int) int y

use layergraph

use makeDAG.int

Function drawgraph(g:graph.int, nodelabels:seq.labeledNode, labels:set.labeledarc) seq.word
drawgraph(g, layer.makeDAG.g, nodelabels, labels)

Function drawgraph(
xxx:graph.int
, lg:layeredgraph
, nodelabels:seq.labeledNode
, labels:set.labeledarc
) seq.word
let nodepos = assignx.lg
for arcpaths0 = empty:set.arcpath, a ∈ paths(xxx, lg)
do
 let from = if n.a = 2 then x.1#lookup(nodepos, nodeinfo(1#a, 0, 0)) else 0
 for d = "", from0 = 0, from1 = from, p ∈ a << 1
 do
  let xy = 1#lookup(nodepos, nodeinfo(p, 0, 0)),
  next(d + "L" + %.scalex.y.xy + %.scaley.x.xy, from1, x.xy),
 asset.[arcpath(arc(1#a, 1^a), d, from0)] ∪ arcpaths0
let arcpaths =
 if isempty.labels then arcpaths0
 else
  for acc = empty:seq.arcpath, grp = empty:seq.arcpath, p ∈ toseq.arcpaths0
  do
   if isempty.grp ∨ head.arc.1^grp = head.arc.p then next(acc, grp + p)
   else next(acc + addgroup.grp, [p]),
  asset(acc + addgroup.grp)
for
 txt = ""
 , i = 1
 , id = requestids(n.nodes.xxx + n.arcs.xxx) + requestids.1
 , draw = ""
 , maxx = 0
 , maxy = 0
 , n ∈ toseq.nodepos
do
 {assumes nodes in g uses same sortorder as nodeinfo}
 let nodex = scalex.y.n
 let nodey = scaley.x.n,
 if not(i ≤ n.nodes.xxx ∧ i#nodes.xxx = n.n) then next(txt, i, id, draw, max(maxx, nodex), max(maxy, nodey))
 else
  let succ = toseq.successors(xxx, n.n)
  for arctxt = "", j = id + 1, s ∈ succ
  do
   let xy = 1#lookup(nodepos, nodeinfo(s, 0, 0))
   let paths = lookup(arcpaths, arcpath(arc(n.n, s), "", 0)),
   let path = if isempty.paths then "L^(scalex.y.xy)^(scaley.x.xy)" else d.1#paths,
   next(
    arctxt
     + svgpath("arcs", [toword.j], "M 0 0^(path)")
     + encodeword.[char.10]
     + (if isempty.labels then ""
    else
     let lab = lookup(labels, labeledarc(n.n, s, "", "")),
     if isempty.lab then ""
     else
      "/tag <text /sp class = /tag^(dq."nodes") > /tag <textPath /sp href = /tag^(dq.[merge("#" + toword.j)]) startOffset = /tag^(dq."100%") text-anchor = /tag^(dq."end") > /tag <tspan /sp = /tag^(dq."-0.1") >^(label.1#lab) /tag </tspan></textPath></text>"
       + encodeword.[char.10]
    )
    , j + 1
   )
  let hovertext = hover.(n.n)#nodelabels
  let svg =
   text("nodes", [toword.id], nodex, nodey, name.(n.n)#nodelabels)
    + {" /tag <text /sp id = /tag^(dq.[toword.id]) class = /tag^(dq." nodes") x = /tag^(dq.%.nodex)) y = /tag^(dq.%.nodey)) >^(name.(n.n)#nodelabels) /tag </text>"+}
   encodeword.[char.10]
    + arctxt
    + if isempty.hovertext then "" else hovertext(n.n, nodex, nodey, hovertext),
  let newdraw =
   if n.succ > 0 then
    for drawtxt = "", k = id
    while k ≤ id + n.succ
    do next(drawtxt + toword.k + ",", k + 1),
    "[^(drawtxt >> 1)],"
   else "",
  next(
   txt + svg
   , i + 1
   , id + n.succ + 1
   , draw + newdraw
   , max(maxx, nodex)
   , max(maxy, nodey)
  ),
svg(
 [
  ".arcs {fill:none ; stroke:black ; stroke-width:.07 ;}"
  , ".nodes {dominant-baseline:hanging; font: 1px sans-serif ; stroke-width:.1 ;}"
  , "svg g:hover text {opacity:1;}"
  , "svg g:hover rect {opacity:1;}"
 ]
 , [
  "id = svg10"
  , "viewBox 5 /sp-1^(%(maxx + 5))^(%(maxy + 5))"
  , "onload [^(draw >> 1)].forEach (shiftstart)"
 ]
 , txt
)
 + drawscript

Function text(class:seq.word, id:seq.word, x:int, y:int, w:seq.word) seq.word
"/tag <text /sp class = /tag^(dq.class)^(if id = "" then id else "id = /tag^(dq.id)") x = /tag^(dq.%.x) y = /tag^(dq.%.y) >^(w) /tag </text>"

Function svgpath(class:seq.word, id:seq.word, path:seq.word) seq.word
"/tag <path /sp class = /tag^(dq.class)^(if id = "" then id else "id = /tag^(dq.id)") d = /tag^(dq.path) />"

Function svg(classes2:seq.seq.word, otherAttributes:seq.seq.word, body:seq.word) seq.word
for att = "", e ∈ otherAttributes
do if isempty.e then "" else att + "^(1#e) = /tag^(dq(e << 1))"
for
 acc = ""
 , e ∈ for acc2 = empty:seq.seq.word, e ∈ classes2
 do acc2 + "" + e,
 acc2
do acc + e
let classdefs =
 "/tag <style /sp type = /tag^(dq."text/css") > /tag <"
  + merge."! [CDATA ["
  + acc
  + "] /tag] > /tag </style>",
"/tag <svg /sp^(att) >^(classdefs)^(body) Your browser does not support inline SVG. /tag </svg>"

function addgroup(grp:seq.arcpath) seq.arcpath
{For labeled arcs}
if n.grp = 1 then grp
else
 let inc = 1.0
 let dd = d.1#grp
 let base = makereal.subseq(dd, n.dd - 1, n.dd) - toreal(n.grp - 1) / 2.0 * inc,
 for acc = empty:seq.arcpath, new = base, q ∈ grp
 do next(acc + arcpath(arc.q, d.q >> 3 + print(3, new), 0), new + inc),
 acc

Function drawscript seq.word
{Adjust beginning of paths so the start at the end of the word}
"/tag <script> function shiftstart (arcs) {let bb = document.getElementById (arcs [0]).getBBox () ; arcs.forEach (function (idval, index) {if (index > 0) {let element = document.getElementById (idval) ; let d = /tag^(dq."M")+(bb.x+bb.width)+/tag^(dq.",")+(bb.y+bb.height / 2)+element.getAttribute (/tag^(dq."d")).substring (5) ; element.setAttribute (/tag^(dq."d"), d) ;}}) ;} /tag </script>"
 + encodeword.[char.10]

function hovertext(n:int, nodex0:int, nodey0:int, hovertext:seq.word) seq.word
let nodex = dq.%.nodex0
let nodey = dq.%.nodey0,
"/tag <g><rect /sp opacity = /tag^(dq."0.0") x = /tag^(nodex) y = /tag^(nodey)) height = /tag^(dq."0.5") width = /tag^(dq."1") > /tag </rect><rect /sp pointer-events = /tag^(dq."none") fill = /tag^(dq."white") opacity = /tag^(dq."0.0") x = /tag^(nodex) y = /tag^(nodey)) height = /tag^(dq."1") width = /tag^(dq."100") > /tag </rect><text /sp pointer-events = /tag^(dq."none") class = /tag^(dq."nodes") x = /tag^(nodex) y = /tag^(nodey) opacity = /tag^(dq."0.0") >^(hovertext) /tag </text></g>"
 + encodeword.[char.10] 