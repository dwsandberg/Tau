Module svg

use seq1.int

use seq1.seq.int

use sort.seq.int

use layernode

use seq.layernode

use standard

use uniqueids

function >3(a:seq.int, b:seq.int) ordering
if isempty.a then 0 >1 n.b else if isempty.b then n.b >1 0 else 1#a >1 1#b

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

Function drawscript seq.word
{Adjust beginning of paths so the start at the end of the word}
"/tag <script> function shiftstart (arcs) {let bb = document.getElementById (arcs [0]).getBBox () ; arcs.forEach (function (idval, index) {if (index > 0) {let element = document.getElementById (idval) ; let d = /tag^(dq."M")+(bb.x+bb.width)+/tag^(dq.",")+(bb.y+bb.height / 2)+element.getAttribute (/tag^(dq."d")).substring (5) ; element.setAttribute (/tag^(dq."d"), d) ;}}) ;} /tag </script>"
 + encodeword.[char.10]

Function hovertext(n:int, nodex0:int, nodey0:int, hovertext:seq.word) seq.word
if isempty.hovertext then ""
else
 let nodex = dq.%.nodex0
 let nodey = dq.%.nodey0,
 "/tag <g><rect /sp opacity = /tag^(dq."0.0") x = /tag^(nodex) y = /tag^(nodey)) height = /tag^(dq."0.5") width = /tag^(dq."1") > /tag </rect><rect /sp pointer-events = /tag^(dq."none") fill = /tag^(dq."white") opacity = /tag^(dq."0.0") x = /tag^(nodex) y = /tag^(nodey)) height = /tag^(dq."1") width = /tag^(dq."100") > /tag </rect><text /sp pointer-events = /tag^(dq."none") class = /tag^(dq."nodes") x = /tag^(nodex) y = /tag^(nodey) opacity = /tag^(dq."0.0") >^(hovertext) /tag </text></g>"
  + encodeword.[char.10]

Function nodeLabel(i:int) seq.seq.word ["", %.i, ""]

Function nodeLabel(n:word) seq.seq.word ["", %.n, ""]

Function nodeLabel(n:seq.word) seq.seq.word ["", n, ""] 