Module svg2graph.T

use seq.arc.T

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

Export type:labeledarc.T

Export arc(arcpath.T)arc.T

Export d(arcpath.T)seq.word

Export from(arcpath.T)int

Export arcpath(arc:arc.T, d:seq.word, from:int)arcpath.T

unbound ?(T, T)ordering

unbound=(T, T)boolean

unbound nodeTitle(T)seq.word

type arcpath is arc:arc.T, d:seq.word, from:int

type labeledarc is tail:T, head:T, label:seq.word

Export label(a:labeledarc.T)seq.word

Function arc(a:labeledarc.T)arc.T arc(tail.a, head.a)

Function arc(a:T, b:T, label:seq.word)labeledarc.T labeledarc(a, b, label)

Function ?(a:labeledarc.T, b:labeledarc.T)ordering tail.a ? tail.b ∧ head.a ? head.b

Function ?(a:arcpath.T, b:arcpath.T)ordering
head.arc.a ? head.arc.b ∧ {from.a ? from.b /and}tail.arc.a ? tail.arc.b

Function addgroup(grp:seq.arcpath.T)seq.arcpath.T
if length.grp = 1 then grp
else
 let inc = 0.6
 let dd = d.first.grp
 let base = makereal.subseq(dd, length.dd - 3, length.dd) - toreal(length.grp - 1) / 2.0 * inc
 for acc = empty:seq.arcpath.T, new = base, q ∈ grp do next(acc + arcpath(arc.q, d.q >> 3 + print(3, new), 0), new + inc)/for(acc)

Function drawscript:T seq.word
"<script> function shiftstart(arcs){let bb=document.getElementById(arcs[0]).getBBox(); arcs.forEach(
  function(idval, index){if(index > 0){let element=document.getElementById(idval); let d="
+ dq."M"
+ space
+ "+(bb.x+bb.width)+$(dq.", ")+(bb.y+bb.height)+element.getAttribute($(dq."d")).substring(5); element.setAttribute($(dq."d"), d);}});}</script> <style>.arcs{fill:none ; stroke:black ; stroke-width:.07 ;}.nodes{font-size:.03em;
  stroke-width:.1 ;}svg g:hover text{opacity:1;}svg g:hover rect{opacity:1;}</style>"
+ encodeword.[char.10]

unbound node2text(T)seq.word

Function drawgraph(xxx:graph.T)seq.word drawgraph(xxx, empty:set.labeledarc.T)

Function drawgraph(arcs:seq.arc.T, include:set.T, exclude:set.T)seq.word
for arclist = empty:seq.arc.T, a ∈ arcs do
 if head.a ∈ exclude ∨ not.isempty.include ∧ tail.a ∉ include then arclist else arclist + a
/for(drawgraph.newgraph.arclist)

Function drawgraph(xxx:graph.T, labels:set.labeledarc.T)seq.word
let haslabels = not.isempty.labels
let scalex = 6.0
let scaley = 0.4
let layout = layout(xxx, haslabels)
let arcpaths0 = 
 for ap = empty:set.arcpath.T, a ∈ paths.layout do
  let from = if length.a = 2 then x.lookup(nodeinfo.layout, nodeinfo(a_1, 0, 0))_1 else 0
  for d = "", from0 = 0, from1 = from, p ∈ a << 1 do
   let xy = lookup(nodeinfo.layout, nodeinfo(p, 0, 0))_1
   next(d + "L" + print(3, toreal.y.xy * scalex) + print(3, toreal.x.xy * scaley)
   , from1
   , x.xy
   )
  /for(asset.[arcpath(arc(first.a, last.a), d, from0)] ∪ ap)
 /for(ap)
let arcpaths = 
 if not.haslabels then arcpaths0
 else
  for acc = empty:seq.arcpath.T, grp = empty:seq.arcpath.T, p ∈ toseq.arcpaths0 do
   if isempty.grp ∨ head.arc.last.grp = head.arc.p then next(acc, grp + p)
   else next(acc + addgroup.grp, [p])
  /for(asset(acc + addgroup.grp))
for txt = ""
, i = 1
, id = requestids(cardinality.nodes.xxx + cardinality.arcs.xxx) + requestids.1
, draw = ""
, maxx = 0.0
, maxy = 0.0
, hover = empty:seq.hovertext.T
, n ∈ toseq.nodeinfo.layout
do
 {assumes nodes in g uses same sortorder as nodinfo}
 let nodex = toreal.y.n * scalex
 let nodey = toreal.x.n * scaley
 if i ≤ cardinality.nodes.xxx ∧ (nodes.xxx)_i = n.n then
  let succ = toseq.successors(xxx, n.n)
  let hovertext = nodeTitle.n.n
  let svg = 
   "<text id=$(xml.[toword.id])class=$(xml."nodes")x=$(xml.print(3, nodex))y=$(xml.print(3, nodey))> $(node2text.n.n)</text>"
   + encodeword.[char.10]
   + for arctxt = "", j = id + 1, s ∈ succ do
    let xy = lookup(nodeinfo.layout, nodeinfo(s, 0, 0))_1
    let paths = lookup(arcpaths, arcpath(arc(n.n, s), "", 0))
    let path = 
     if isempty.paths then"L" + print(3, toreal.y.xy * scalex) + print(3, toreal.x.xy * scaley)
     else d.paths_1
    next(arctxt
    + "<path id=$(xml.[toword.j])class=$(xml."arcs")d=$(xml("M 0 0" + path))></path>"
    + encodeword.[char.10]
    + if haslabels then
     let lab = lookup(labels, arc(n.n, s, ""))
     if isempty.lab then""
     else
      "<text class=$(xml."nodes")> <textPath href=$(xml.[merge("#" + toword.j)])startOffset=$(xml."100%")text-anchor=$(xml."end")> <tspan dy=$(xml."-0.1")> $(label.lab_1)</tspan> </textPath> </text>"
      + encodeword.[char.10]
    else""
    , j + 1
    )
   /for(arctxt)
  {"<tspan dy=$(xml."-0.1")> $(label.lab_1)</tspan>"}
  let newdraw = 
   if length.succ > 0 then
    for drawtxt = "", k ∈ arithseq(1 + length.succ, 1, id)do drawtxt + toword.k + ", "/for("[" + drawtxt >> 1 + "], ")
   else""
  next(txt + svg
  , i + 1
  , id + length.succ + 1
  , draw + newdraw
  , max(maxx, nodex)
  , max(maxy, nodey)
  , if isempty.hovertext then hover else hover + hovertext(n.n, nodex, nodey, hovertext)
  )
 else next(txt, i, id, draw, max(maxx, nodex), max(maxy, nodey), hover)
/for(let hovertxt = for svg2 = "", e ∈ sort.hover do svg2 + assvg.e /for(svg2)
" /br  /< noformat" + drawscript:T
+ "<svg id=$(xml."svg10")xmlns=$(xml."http://www.w3.org/2000/svg")width=$(xml."100%")viewBox=$(xml("5.0" + space + "-1" + print(2, maxx + 5.0) + print(2, maxy + 1.3)))onload=$(xml("[" + draw >> 1 + "].forEach(shiftstart)"))> $(txt + hovertxt)+</svg>"
+ " />")

type hovertext is n:T, nodex:real, nodey:real, text:seq.word

function ?(a:hovertext.T, b:hovertext.T)ordering
if nodex.b < nodex.a ∨ nodey.b < nodey.b then LT
else if nodex.b = nodex.a ∨ nodey.b = nodey.b then EQ else GT

function assvg(h:hovertext.T)seq.word
"<g> <rect opacity=$(xml."0.0")x=$(xml.print(2, nodex.h))y=$(xml.print(2, nodey.h - 0.5))height=$(xml."0.5")width=$(xml."1")></rect>"
+ "<rect pointer-events=$(xml."none")fill=$(xml."white")opacity=$(xml."0.0")x=$(xml.print(2, nodex.h))y=$(xml.print(2, nodey.h - 0.5))height=$(xml."1")width=$(xml."100")></rect>"
+ "<text pointer-events=$(xml."none")class=$(xml."nodes")x=$(xml.print(2, nodex.h))y=$(xml.print(2, nodey.h))opacity=$(xml."0.0")> $(text.h)</text>"
+ "</g>"
+ encodeword.[char.10] 