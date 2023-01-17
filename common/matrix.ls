Module matrix

use point

use real

use standard

Export type:matrix

type matrix is row1:point, row2:point, row3:point, row4:point

Function transpose(a:matrix) matrix
matrix(point(x.row1.a, x.row2.a, x.row3.a, x.row4.a)
 , point(y.row1.a, y.row2.a, y.row3.a, y.row4.a)
 , point(z.row1.a, z.row2.a, z.row3.a, z.row4.a)
 , point(w.row1.a, w.row2.a, w.row3.a, w.row4.a))

Function rotatex(a:real) matrix
matrix(point(1.0, 0.0, 0.0, 0.0)
 , point(0.0, cos.a, sin.a, 0.0)
 , point(0.0, sin.a, cos.a, 0.0)
 , point(0.0, 0.0, 0.0, 1.0))

Function rotatey(a:real) matrix
matrix(point(cos.a, 0.0, sin.a, 0.0)
 , point(0.0, 1.0, 0.0, 0.0)
 , point(-sin.a, 0.0, cos.a, 0.0)
 , point(0.0, 0.0, 0.0, 1.0))

Function rotatez(a:real) matrix
matrix(point(cos.a,-sin.a, 0.0, 0.0)
 , point(sin.a, cos.a, 0.0, 0.0)
 , point(0.0, 0.0, 1.0, 0.0)
 , point(0.0, 0.0, 0.0, 1.0))

Function scale(p:point) matrix
matrix(point(x.p, 0.0, 0.0, 0.0)
 , point(0.0, y.p, 0.0, 0.0)
 , point(0.0, 0.0, z.p, 0.0)
 , point(0.0, 0.0, 0.0, 1.0))

Function deg(d:real) real 3.14159 / 180.0 * d

Function print(m:matrix) seq.word
"[$(print.row1.m) /br, $(print.row2.m) /br, $(print.row3.m) /br, $(print.row4.m)]"

Function *(m:matrix, p:point) point
point(row1.m * p, row2.m * p, row3.m * p, row4.m * p)

Function translate(a:point) matrix
matrix(point(1.0, 0.0, 0.0, x.a)
 , point(0.0, 1.0, 0.0, y.a)
 , point(0.0, 0.0, 1.0, z.a)
 , point(0.0, 0.0, 0.0, 1.0))

Function *(a:matrix, b:matrix) matrix
matrix(
 point(
  x.row1.a * x.row1.b + y.row1.a * x.row2.b + z.row1.a * x.row3.b
  + w.row1.a * x.row4.b
  , x.row1.a * y.row1.b + y.row1.a * y.row2.b + z.row1.a * y.row3.b
  + w.row1.a * y.row4.b
  , x.row1.a * z.row1.b + y.row1.a * z.row2.b + z.row1.a * z.row3.b
  + w.row1.a * z.row4.b
  , x.row1.a * w.row1.b + y.row1.a * w.row2.b + z.row1.a * w.row3.b
  + w.row1.a * w.row4.b)
 , point(
  x.row2.a * x.row1.b + y.row2.a * x.row2.b + z.row2.a * x.row3.b
  + w.row2.a * x.row4.b
  , x.row2.a * y.row1.b + y.row2.a * y.row2.b + z.row2.a * y.row3.b
  + w.row2.a * y.row4.b
  , x.row2.a * z.row1.b + y.row2.a * z.row2.b + z.row2.a * z.row3.b
  + w.row2.a * z.row4.b
  , x.row2.a * w.row1.b + y.row2.a * w.row2.b + z.row2.a * w.row3.b
  + w.row2.a * w.row4.b)
 , point(
  x.row3.a * x.row1.b + y.row3.a * x.row2.b + z.row3.a * x.row3.b
  + w.row3.a * x.row4.b
  , x.row3.a * y.row1.b + y.row3.a * y.row2.b + z.row3.a * y.row3.b
  + w.row3.a * y.row4.b
  , x.row3.a * z.row1.b + y.row3.a * z.row2.b + z.row3.a * z.row3.b
  + w.row3.a * z.row4.b
  , x.row3.a * w.row1.b + y.row3.a * w.row2.b + z.row3.a * w.row3.b
  + w.row3.a * w.row4.b)
 , point(
  x.row4.a * x.row1.b + y.row4.a * x.row2.b + z.row4.a * x.row3.b
  + w.row4.a * x.row4.b
  , x.row4.a * y.row1.b + y.row4.a * y.row2.b + z.row4.a * y.row3.b
  + w.row4.a * y.row4.b
  , x.row4.a * z.row1.b + y.row4.a * z.row2.b + z.row4.a * z.row3.b
  + w.row4.a * z.row4.b
  , x.row4.a * w.row1.b + y.row4.a * w.row2.b + z.row4.a * w.row3.b
  + w.row4.a * w.row4.b)
 )

Function test seq.word
let a = point(7.000, 9.000, 11.000) = translate.point(6.0, 7.0, 8.0) * point(1.0, 2.0, 3.0)
let b = point(6.000, 14.000, 24.000) = scale.point(6.0, 7.0, 8.0) * point(1.0, 2.0, 3.0)
let c = 
 point(42.000, 63.000, 88.000)
 = scale.point(6.0, 7.0, 8.0) * translate.point(6.0, 7.0, 8.0) * point(1.0, 2.0, 3.0)
let d = 
 "[(0.708,-0.540,-0.455,-3.171)
  /br, (0.540, 0.000, 0.841, 9.974)
  /br, (-0.455, 0.841, 0.292, 5.498) (0.000, 0.000, 0.000)]"
 = print(transpose.transpose.identity * rotatez.deg.90.0 * rotatex.1.0 * rotatey.1.0
 * translate.point(6.0, 7.0, 8.0))
let p1 = cross(point(6.0, 7.0, 8.0), point(1.0, 0.0, 0.0) + point(0.0, 0.0, 0.0))
assert a ∧ b ∧ c ∧ d ∧ print(3, length.unit.-(p1 - 3.0 * p1 + p1)) = "1.000"
∧ (p1 >1 p1) = EQ
report "problem with matrix",
"test matrix ok"

Function identity matrix
matrix(point(1.0, 0.0, 0.0, 0.0)
 , point(0.0, 1.0, 0.0, 0.0)
 , point(0.0, 0.0, 1.0, 0.0)
 , point(0.0, 0.0, 0.0, 1.0)) 