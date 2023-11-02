Module point

use real

use standard

Export type:point

Export w(a:point) real

Export x(a:point) real

Export y(a:point) real

Export z(a:point) real

Export point(real, real, real, real) point

type point is x:real, y:real, z:real, w:real

Function point(a:real, b:real, c:real) point point(a, b, c, 1.0)

Function +(a:point, b:point) point point(x.a + x.b, y.a + y.b, z.a + z.b, 1.0)

Function -(a:point, b:point) point point(x.a - x.b, y.a - y.b, z.a - z.b, 1.0)

Function -(b:point) point point(-x.b,-y.b,-z.b, 1.0)

Function *(a:point, b:point) real x.a * x.b + y.a * y.b + z.a * z.b + w.a * w.b

Function *(a:real, b:point) point point(a * x.b, a * y.b, a * z.b, 1.0)

Function cross(a:point, b:point) point
point(y.a * z.b - z.a * y.b, z.a * x.b - x.a * z.b, x.a * y.b - y.a * x.b)

Function =(a:point, b:point) boolean x.a = x.b ∧ y.a = y.b ∧ z.a = z.b

Function >1(a:point, b:point) ordering
if x.a >1 x.b = LT then
LT
else if x.a >1 x.b = GT then
GT
else if y.a >1 y.b = LT then
LT
else if y.a >1 y.b = GT then
GT
else z.a >1 z.b

Function print(p:point) seq.word
"(^(print(3, x.p)),^(print(3, y.p)),^(print(3, z.p))
^(if w.p = 1.0 then "" else ",^(print(3, w.p))"))"

Function length(a:point) real sqrt((z.a)^2 + (x.a)^2 + (y.a)^2)

Function unit(a:point) point let l = length.a, point(x.a / l, y.a / l, z.a / l) 