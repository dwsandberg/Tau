Module svg

use standard

use uniqueids

Function htmlMark(element:seq.word, attributes:seq.seq.word) seq.word
{For multi word attribute enclose in equals like htmlMark("rect",["class node","= pointer-events = none"])}
for acc = "/!<" + element, e ∈ attributes
do
 if n.e < 2 then if e = "/" then acc + "/ /nsp" else acc
 else
  acc
  + if e sub 1 ∈ "=" then
   let eqidx = findindex(e << 1, "=" sub 1)
   let attname = subseq(e, 2, eqidx),
   "/sp:(attname)/nsp =:(dq)/nsp" + e << (eqidx + 1) + dq
  else "/sp:(e sub 1)/nsp =:(dq)/nsp" + e << 1 + dq,
acc + "/!>"

Function htmlMark(element:seq.word) seq.word
for acc = "", e ∈ element do acc + "/!<:(e)/!>",
acc

Function text(class:seq.word, id:seq.word, x:int, y:int, w:seq.word) seq.word
htmlMark("text", ["class:(class)", "id:(id)", "x:(x)", "y:(y)"])
 + w
 + htmlMark."/text"

Function svgpath(class:seq.word, id:seq.word, path:seq.word) seq.word
htmlMark("path", ["class:(class)", "id:(id)", "d:(path)", "/"])

Function svg(classes2:seq.seq.word, otherAttributes:seq.seq.word, body:seq.word) seq.word
for acc2 = empty:seq.word, e ∈ classes2 do acc2 + e,
htmlMark("svg", otherAttributes)
 + htmlMark."style"
 + acc2
 + htmlMark."/style>"
 + body
 + "Your browser does not support inline SVG. "
 + htmlMark."/svg"

Function drawscript seq.word
{Adjust the beginning of paths so they start at the end of the word}
htmlMark."script"
 + "function shiftstart(arcs){let bb = document.getElementById(arcs[0]).getBBox(); arcs.forEach(function(idval, index){if(index > 0){let element = document.getElementById(idval); let d =:(dq."/nsp M")+(bb.x+bb.width)+:(dq.",")+(bb.y+bb.height / 2)+element.getAttribute(:(dq."/nsp d")).substring(5); element.setAttribute(:(dq."/nsp d"), d);}});}"
 + htmlMark."/script"
 + encodeword.[char.10]

Function hovertext(n:int, nodex:int, nodey:int, hovertext:seq.word) seq.word
let tmp = ["= pointer-events = none", "opacity 0.0", "x:(nodex)", "y:(nodey)"],
htmlMark."g"
 + htmlMark("rect", ["opacity 0.0", "x:(nodex)", "y:(nodey)", "height 0.5", "width 1", "/"])
 + htmlMark("rect", ["fill white", "height 1", "width 100"] + tmp + "/")
 + htmlMark("text", ["class nodes"] + tmp)
 + hovertext
 + htmlMark."/text /g"
 + encodeword.[char.10]

Function nodeLabel(i:int) seq.seq.word ["", %.i, ""]

Function nodeLabel(n:word) seq.seq.word ["", %.n, ""]

Function nodeLabel(n:seq.word) seq.seq.word ["", n, ""] 