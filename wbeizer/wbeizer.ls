Module wbeizer

use real

use standard

use webIO

/em grp1 is a group that contains circles that represent the control points.
/br /em grp1 also has a attribute data-segments that contains the number of biezer curves in path.
/br /em lines is a path that conects the control points.
/br /em curve is a path that draw the biezer curves.

Function draw4 real
{This keeps then paths in sync with the location of the control points}
let c1 = getattributes("c1", "cx cy")
let no = toint.first.getattributes("grp1", "data-segments")
for lines = "M" + c1, curve = "M" + c1, i ∈ arithseq(no, 2, 2) do
 let c2 = getattributes([merge.[first."c", toword.i]], "cx cy")
 let c3 = getattributes([merge.[first."c", toword(i + 1)]], "cx cy")
 next(lines + "L" + c2 + "L" + c3, curve + "Q" + c2 + c3)
/for (setAttribute("lines", "d", lines) + setAttribute("curve", "d", curve))

function split(c:seq.word) seq.seq.word
if c_2 = first."." then [subseq(c, 1, 3), c << 3] else [[c_1], c << 1]

function addsegment(thisid:word) real
let no = toint.first.getattributes("grp1", "data-segments")
let new = 
 for txt = empty:seq.seq.word, i ∈ arithseq(no * 2 + 1, 1, 1) do
  let id = merge("c" + toword.i)
  let c = getattributes([id], "cx cy")
  txt
  + if thisid = id then
   let t = toint.first.c
   [c, [toword(t + 1)] + c << 1, [toword(t + 2)] + c << 1]
  else
   [c]
 /for (txt)
let svg = 
 for svg = "", i = 1, c ∈ new do
  let d = split.c
  next(
   svg
   + "<circle id = $(dq.[merge("c" + toword.i)]) $(sp) class = $(dq."draggable") $(sp)
    fill = $(dq."blue") $(sp) cx = $(dq.d_1) $(sp) cy = $(dq.d_2) $(sp) r = $(dq.".3")
    />"
   , i + 1)
 /for (svg)
let k = replaceSVG("grp1", svg)
let t = setAttribute("grp1", "data-segments", [toword(no + 1)])
0.0

function sp seq.word [space]

use otherseq.seq.word

/function % (a:seq.word) seq.word a

Function myselect(id:jsbytes) real addsegment.first.towords.id

Function showsvg int setElementValue("selected", getElementValue:jsbytes("svg10"))

Function Bquadratic int 0

Function drawcubic real
{OPTION PROFILE}
let c1 = getattributes("c1", "cx cy")
let c2 = getattributes("c2", "cx cy")
let c3 = getattributes("c3", "cx cy")
let c4 = getattributes("c4", "cx cy")
let lines2 = "M" + c1 + "L" + c2 + "M" + c3 + "L" + c4
let d2 = "M" + c1 + "C" + c2 + c3 + c4
setAttribute("lines", "d", lines2) + setAttribute("curve", "d", d2)

Function Bcubic int intpart.drawcubic  

use profile

Function test345 int
setElementValue("xx", profileresults("time") )
+ callevent("svg10","load")

 

