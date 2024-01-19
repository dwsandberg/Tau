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
let no = toint.1#getattributes("grp1", "data-segments")
for lines = "M^(c1)", curve = "M^(c1)", i ∈ arithseq(no, 2, 2)
do
 let c2 = getattributes([merge.[1#"c", toword.i]], "cx cy")
 let c3 = getattributes([merge.[1#"c", toword(i + 1)]], "cx cy"),
 next(lines + "L" + c2 + "L" + c3, curve + "Q" + c2 + c3),
setAttribute("lines", "d", lines) + setAttribute("curve", "d", curve)

function split(c:seq.word) seq.seq.word
if 2#c = 1#"." then [subseq(c, 1, 3), c << 3] else [[1#c], c << 1]

function addsegment(thisid:word) real
let no = toint.1#getattributes("grp1", "data-segments")
let new =
 for txt = empty:seq.seq.word, i ∈ arithseq(no * 2 + 1, 1, 1)
 do
  let id = merge("c" + toword.i)
  let c = getattributes([id], "cx cy"),
   txt
    + 
    if thisid = id then
    let t = toint.1#c, [c, [toword(t + 1)] + c << 1, [toword(t + 2)] + c << 1]
    else [c],
 txt
let svg =
 for svg = "", i = 1, c ∈ new
 do
  let d = split.c,
  next(
   svg
    + "<circle id =^(dq.[merge("c" + toword.i)])^(sp) class =^(dq."draggable")^(sp)"
    + "fill =^(dq."blue")^(sp)"
    + "cx =^(dq.1#d)^(sp)"
    + "cy =^(dq.2#d)^(sp)"
    + "r =^(dq.".3")"
    + "/>"
   , i + 1
  ),
 svg
let k = replaceSVG("grp1", svg)
let t = setAttribute("grp1", "data-segments", [toword(no + 1)]),
0.0

function sp seq.word [encodeword.[char.32]]

use otherseq.seq.word

Function myselect(id:jsbytes) real addsegment.1#towords.id

Function showsvg real setElementValue("selected", getElementValue:jsbytes("svg10"))

Function Bquadratic int 0

Function tr(n:int) int
{OPTION PROFILE}
let a = %.n,
if n < 3 then n else tr(n - 1) + tr(n - 2)

Function drawcubic real
{OPTION PROFILE}
let zzz = tr.4
let c1 = getattributes("c1", "cx cy")
let c2 = getattributes("c2", "cx cy")
let c3 = getattributes("c3", "cx cy")
let c4 = getattributes("c4", "cx cy")
let lines2 = "M^(c1) L^(c2) M^(c3) L^(c4)"
let d2 = "M^(c1) C^(c2)^(c3)^(c4)",
setAttribute("lines", "d", lines2) + setAttribute("curve", "d", d2)

Function Bcubic int intpart.drawcubic

use profile

use bits

use seq.byte

builtin vector2 seq.byte

use objectio.addrsym

use object01

use symbol2

use seq.addrsym

use bitcast.seq.addrsym

Export type:addrsym

Function test345 real 
setElementValue("xx", profileresults."time") + callevent("svg10", "load")

{let a = dump.decode2.vector2} let a = bitcast:seq.addrsym (inrec.vector2) {let a = inbytes:addrsym
(vector2)} let r = for txt ="", e /in a do txt+%.addr.e+%.sym.e, txt, setElementValue (" xx"
, r)

setElementValue (" xx", profileresults." time")+callevent (" svg10"," load") 