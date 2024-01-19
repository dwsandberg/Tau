Module genPointModule

use standard

Function genPointModule(typenames:seq.word, elements:seq.word) seq.word
{COMMAND}
{For generating module for working with 2d and 3d points.}
let basetype = "real"
let typename = {" point2"} [1#typenames]
let matrixname = {" matrix2"} [2#typenames]
let code = types(basetype, typename, elements) + pointFunctions(basetype, typename, elements),
"Module^(typename) /p This package was generated with: genPointModule typesnames: ^(typenames) elements: ^(elements) /p use real
/p use standard
/p^(code + matrixFunctions(elements, basetype, typename, matrixname)) function square (a:^(basetype)) real a * a"

function types(basetype:seq.word, typename:seq.word, elements:seq.word) seq.word
for para0 = "", exports0 = "", x ∈ elements
do
 next(
  para0 + "^(x):^(basetype),"
  , exports0 + "Export^(x) (^(typename))^(basetype) /p"
 ),
"Export^(typename) (^(para0 >> 1))^(typename) /p^(exports0) type^(typename) is^(para0 >> 1) /p Export type:^(typename) /p"

function pointFunctions(basetype:seq.word, typename:seq.word, elements:seq.word) seq.word
let opdefs =
 [
  "+(a:^(typename), b:^(typename))^(typename) term: e.a+e.b, final:^(typename)"
  , "-(a:^(typename), b:^(typename))^(typename) term: e.a-e.b, final:^(typename)"
  , "= (a:^(typename), b:^(typename)) boolean term: e.a = e.b /and"
  , ">1 (a:^(typename), b:^(typename)) ordering term: e.a >1 e.b /and"
  , "length (b:^(typename))^(basetype) term:square.e.b+final:sqrt"
  , "* (a:^(basetype), b:^(typename))^(typename) term: a * e.b, final: ^(typename)"
  , "max (a:^(typename), b:^(typename))^(typename) term:max (e.a, e.b), final:^(typename)"
  , "min (a:^(typename), b:^(typename))^(typename) term:min (e.a, e.b), final:^(typename)"
  , "-(a:^(typename))^(typename) term: -e.a, final:^(typename)"
  , "* (a:^(typename), b:^(typename))^(basetype) term: e.a * e.b+final: "
  , "print (a:^(typename)) seq.word term: print (3, e.a)+final: "
  , "unit (a:^(typename))^(typename) let l = length.a term: e.a / l, final:^(typename)"
 ]
for code = "", ops ∈ opdefs
do
 let final = extractValue(ops, "final")
 let term = extractValue(ops, "term")
 let head = "Function" + subseq(ops, 1, findindex(ops, 1#"term") - 1),
 for body0 = "", e ∈ elements
 do
  for acc = body0, w ∈ term do if w ∈ "e" then acc + e else acc + w,
  "^(acc)",
 "^(code)^(head)^(final) (^(body0 >> 1))
 /p",
code
 + if elements = "x y z" then
 "Function cross (a:^(typename), b:^(typename))^(typename)^(typename) (y.a * z.b-z.a * y.b, z.a * x.b-x.a * z.b, x.a * y.b-y.a * x.b)
 /p"
else ""

use otherseq.word

use seq.seq.seq.word

use otherseq.seq.word

function matrixFunctions(
elements0:seq.word
, basename:seq.word
, typename:seq.word
, matrixname:seq.word
) seq.word
let elements = elements0 + "w"
let rotations = if n.elements0 = 3 then elements0 else if n.elements0 = 2 then "z" else ""
for extra = empty:seq.seq.word, e ∈ rotations
do
 extra
  + [
  [e, merge("rotate" + e)]
   + "(degrees:real)^(matrixname) let a = pi * degrees / 180.0 let sina = sin.a let cosa = cos.a,"
 ]
for
 all = ""
 , head ∈ [
  "*s * (a:^(basename), b:^(matrixname))^(matrixname)"
  , "*p * (a:^(matrixname), b:^(typename))^(typename)"
  , "*m * (a:^(matrixname), b:^(matrixname))^(matrixname)"
  , "++(a:^(matrixname), b:^(matrixname))^(matrixname)"
  , "--(a:^(matrixname), b:^(matrixname))^(matrixname)"
  , "= = (a:^(matrixname), b:^(matrixname)) boolean"
  , "transpose transpose (a:^(matrixname))^(matrixname)"
  , "identity identity^(matrixname)"
  , "scale scale (a:^(typename))^(matrixname)"
  , "translate translate (a:^(typename))^(matrixname)"
 ]
  + extra
do
 let kind = 1#head
 for acc1 = "", row ∈ elements
 do
  for acc2 = "", col ∈ elements
  do
   let calc =
    if kind ∈ "*s" then "a *^(col).^(row).b"
    else if kind ∈ "*p" then dot(elements, row, col, true) >> 4
    else if kind ∈ "transpose" then "^(row).^(col).a"
    else if kind ∈ "identity" then if row = col then "1.0" else "0.0"
    else if kind ∈ "scale" then
     if row = col then if row = 1^elements then "1.0" else "^(row).a"
     else "0.0"
    else if kind ∈ "translate" then if row = col then "1.0" else if col = 1^elements then "^(row).a" else "0.0"
    else if kind ∈ rotations then
     if row ∈ [1^elements, kind] ∨ col ∈ [1^elements, kind] then if row = col then "1.0" else "0.0"
     else if row = col then "cosa"
     else if findindex(elements, row) > findindex(elements, col) then "-sina"
     else "sina"
    else if kind ∈ "*m" then dot(elements, row, col, false)
    else "^(col).^(row).a^(kind)^(col).^(row).b",
   if kind ∈ "*p" ∧ col ≠ 1#elements then acc2
   else acc2 + calc + if kind ∈ "=" then "/and" else ",",
  if kind ∈ "=" then acc1 + acc2 >> 1 + "/and"
  else if kind ∈ "*p" then if row = 1^elements then acc1 else acc1 + "^(acc2 >> 1) /br,"
  else
   acc1
    + "row (^(acc2 >> 1))
   /br,",
 all
  + "Function"
  + head << 1
  + "/br"
  + if kind ∈ "*p" then
  "^(typename) (^(acc1 >> 2))
  /p"
 else if kind ∈ "=" then "^(acc1 >> 1) /p"
 else
  "^(matrixname) (^(acc1 >> 2))
  /p",
types(basename, "row", elements) + types("row", matrixname, elements) + all

function rowelements(row:word, elements:seq.word) seq.seq.word
for acc = empty:seq.seq.word, col ∈ elements
do acc + "^(col).^(row)",
acc

function colelements(col:word, elements:seq.word) seq.seq.word
for acc = empty:seq.seq.word, row ∈ elements
do acc + "^(col).^(row)",
acc

function dot(elements:seq.word, row:word, col:word, bypoint:boolean) seq.word
let c =
 if bypoint then
  for acc = empty:seq.seq.word, e ∈ elements
  do acc + [e],
  acc
 else colelements(col, elements)
for acc = "", index = 1, e ∈ rowelements(row, elements)
do next(acc + "^(e).a *^(index#c).b+", index + 1),
acc >> 1 