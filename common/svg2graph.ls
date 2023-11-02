Module svg2graph.T

use set.arc.T

use seq.arcpath.T

use set.arcpath.T

use bandeskopf.T

use graph.T

use otherseq.hovertext.T

use set.labeledarc.T

use set.nodeinfo.T

use seq.T

use set.T

use real

use standard

use uniqueids

Export type:arcpath.T

Export arc(arcpath.T) arc.T

Export d(arcpath.T) seq.word

Export from(arcpath.T) int

Export arcpath(arc:arc.T, d:seq.word, from:int) arcpath.T

Export type:labeledarc.T

Export label(a:labeledarc.T) seq.word

unbound >1(T, T) ordering

unbound =(T, T) boolean

unbound nodeTitle(T) seq.word

type arcpath is arc:arc.T, d:seq.word, from:int

type labeledarc is tail:T, head:T, label:seq.word

Function arc(a:labeledarc.T) arc.T arc(tail.a, head.a)

Function arc(a:T, b:T, label:seq.word) labeledarc.T labeledarc(a, b, label)

Function >1(a:labeledarc.T, b:labeledarc.T) ordering
tail.a >1 tail.b ∧ head.a >1 head.b

Function >1(a:arcpath.T, b:arcpath.T) ordering
head.arc.a >1 head.arc.b ∧ {from.a >1 from.b /and} tail.arc.a >1 tail.arc.b

Function addgroup(grp:seq.arcpath.T) seq.arcpath.T
if n.grp = 1 then
grp
else
 let inc = 0.6
 let dd = d.1#grp
 let base = makereal.subseq(dd, n.dd - 3, n.dd) - toreal(n.grp - 1) / 2.0 * inc
 for acc = empty:seq.arcpath.T, new = base, q ∈ grp
 do next(acc + arcpath(arc.q, d.q >> 3 + print(3, new), 0), new + inc),
 acc

Function drawscript:T seq.word
"/tag <script> function shiftstart (arcs) {let bb = document.getElementById (arcs [0]).
getBBox () ; arcs.forEach (function (idval, index) {if (index > 0) {let element =
document.getElementById (idval) ; let d = /tag^(dq."M")+(bb.x+bb.width)+/tag
^(dq.",")+(bb.y+bb.height)+element.getAttribute (/tag^(dq."d")).substring (5) ; element.setAttribute (/tag
^(dq."d"), d) ;}}) ;} /tag </script><style>.arcs {fill:none ; stroke:black ; stroke-width:.
07 ;}.nodes {font-size:.03em; stroke-width:.1 ;} svg g:hover text {opacity:1;}
svg g:hover rect {opacity:1;} /tag </style>"
 + encodeword.[char.10]

use UTF8

unbound node2text(T) seq.word

Function drawgraph(xxx:graph.T) seq.word drawgraph(xxx, empty:set.labeledarc.T)

Function drawgraph(arcs:seq.arc.T, include:set.T, exclude:set.T) seq.word
for arclist = empty:seq.arc.T, a ∈ arcs
do
 if head.a ∈ exclude ∨ not.isempty.include ∧ tail.a ∉ include then
 arclist
 else arclist + a,
drawgraph.newgraph.arclist

Function drawgraph(xxx:graph.T, labels:set.labeledarc.T) seq.word
let haslabels = not.isempty.labels
let scalex = 6.0
let scaley = 0.4
let layout = layout(xxx, haslabels)
let arcpaths0 =
 for ap = empty:set.arcpath.T, a ∈ paths.layout
 do
  let from = if n.a = 2 then x.1#lookup(nodeinfo.layout, nodeinfo(1#a, 0, 0)) else 0
  for d = "", from0 = 0, from1 = from, p ∈ a << 1
  do
   let xy = 1#lookup(nodeinfo.layout, nodeinfo(p, 0, 0)),
   next(
    d + "L" + print(3, toreal.y.xy * scalex) + print(3, toreal.x.xy * scaley)
    , from1
    , x.xy
   ),
  asset.[arcpath(arc(1#a, 1^a), d, from0)] ∪ ap,
 ap
let arcpaths =
 if not.haslabels then
 arcpaths0
 else
  for acc = empty:seq.arcpath.T, grp = empty:seq.arcpath.T, p ∈ toseq.arcpaths0
  do
   if isempty.grp ∨ head.arc.1^grp = head.arc.p then
   next(acc, grp + p)
   else next(acc + addgroup.grp, [p]),
  asset(acc + addgroup.grp)
for
 txt = ""
 , i = 1
 , id = requestids(n.nodes.xxx + n.arcs.xxx) + requestids.1
 , draw = ""
 , maxx = 0.0
 , maxy = 0.0
 , hover = empty:seq.hovertext.T
 , n ∈ toseq.nodeinfo.layout
do
 {assumes nodes in g uses same sortorder as nodinfo}
 let nodex = toreal.y.n * scalex
 let nodey = toreal.x.n * scaley,
  if i ≤ n.nodes.xxx ∧ i#nodes.xxx = n.n then
   let succ = toseq.successors(xxx, n.n)
   let hovertext = nodeTitle.n.n
   let svg =
    "/tag <text /sp id = /tag^(dq.[toword.id]) class = /tag^(dq."nodes") x = /tag
    ^(dq.print(3, nodex)) y = /tag^(dq.print(3, nodey)) >^(node2text.n.n) /tag </text>"
     + encodeword.[char.10]
     + 
     for arctxt = "", j = id + 1, s ∈ succ
     do
      let xy = 1#lookup(nodeinfo.layout, nodeinfo(s, 0, 0))
      let paths = lookup(arcpaths, arcpath(arc(n.n, s), "", 0))
      let path =
       if isempty.paths then
       "L^(print(3, toreal.y.xy * scalex))^(print(3, toreal.x.xy * scaley))"
       else d.1#paths,
      next(
       arctxt
        + "/tag <path /sp id = /tag^(dq.[toword.j]) class = /tag^(dq."arcs") d = /tag
       ^(dq."M 0 0^(path)") />"
        + encodeword.[char.10]
        + 
        if haslabels then
         let lab = lookup(labels, arc(n.n, s, "")),
          if isempty.lab then
          ""
          else
           "/tag <text /sp class = /tag^(dq."nodes") > /tag <textPath /sp href = /tag
           ^(dq.[merge("#" + toword.j)]) startOffset = /tag^(dq."100%") text-anchor = /tag
           ^(dq."end") > /tag <tspan /sp = /tag^(dq."-0.1") >^(label.1#lab) /tag </tspan></textPath></text>"
            + encodeword.[char.10]
        else ""
       , j + 1
      ),
     arctxt
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
    , if isempty.hovertext then hover else hover + hovertext(n.n, nodex, nodey, hovertext)
   )
  else next(txt, i, id, draw, max(maxx, nodex), max(maxy, nodey), hover)
let hovertxt = for svg2 = "", e ∈ sort.hover do svg2 + assvg.e, svg2,
drawscript:T
 + "/tag <svg /sp id = /tag"
 + dq."svg10"
 + "ldqns = /tag"
 + dq."http://www.w3.org/2000/svg"
 + "width = /tag"
 + dq."100%"
 + "viewBox = /tag"
 + dq."5.0 /sp-1^(print(2, maxx + 5.0))^(print(2, maxy + 1.3))"
 + "onload = /tag"
 + dq."[^(draw >> 1)].forEach (shiftstart)"
 + ">"
 + (txt + hovertxt)
 + "+tag </svg>"

type hovertext is n:T, nodex:real, nodey:real, text:seq.word

function >1(a:hovertext.T, b:hovertext.T) ordering
if nodex.b < nodex.a ∨ nodey.b < nodey.b then
LT
else if nodex.b = nodex.a ∨ nodey.b = nodey.b then
EQ
else GT

function assvg(h:hovertext.T) seq.word
"/tag <g><rect /sp opacity = /tag^(dq."0.0") x = /tag^(dq.print(2, nodex.h)) y = /tag
^(dq.print(2, nodey.h - 0.5)) height = /tag^(dq."0.5") width = /tag^(dq."1") > /tag </rect><rect /sp pointer-events = /tag
^(dq."none") fill = /tag^(dq."white") opacity = /tag^(dq."0.0") x = /tag
^(dq.print(2, nodex.h)) y = /tag^(dq.print(2, nodey.h - 0.5)) height = /tag^(dq."1") width = /tag
^(dq."100") > /tag </rect><text /sp pointer-events = /tag^(dq."none") class = /tag
^(dq."nodes") x = /tag^(dq.print(2, nodex.h)) y = /tag^(dq.print(2, nodey.h)) opacity = /tag
^(dq."0.0") >^(text.h) /tag </text></g>"
 + encodeword.[char.10] 