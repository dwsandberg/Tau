Module point

use real

use standard

Export type:point

type point is x:real, y:real, z:real, w:real

Export point(real, real, real, real)point

Function point(a:real, b:real, c:real)point point(a, b, c, 1.0)

Function +(a:point, b:point)point point(x.a + x.b, y.a + y.b, z.a + z.b, 1.0)

Function -(a:point, b:point)point point(x.a - x.b, y.a - y.b, z.a - z.b, 1.0)

Function -(b:point)point point(-x.b, -y.b, -z.b, 1.0)

Function *(a:point, b:point)real x.a * x.b + y.a * y.b + z.a * z.b + w.a * w.b

Function *(a:real, b:point)point point(a * x.b, a * y.b, a * z.b, 1.0)

Function cross(a:real, b:point)point point(a * x.b, a * y.b, a * z.b)

Function cross(a:point, b:point)point point(y.a * z.b - z.a * y.b, z.a * x.b - x.a * z.b, x.a * y.b - y.a * x.b)

Function =(a:point, b:point)boolean x.a = x.b ∧ y.a = y.b ∧ z.a = z.b

Function ?(a:point, b:point)ordering
if(x.a ? x.b) = LT then LT
else if(x.a ? x.b) = GT then GT
else if(y.a ? y.b) = LT then LT else if(y.a ? y.b) = GT then GT else z.a ? z.b

Export y(a:point)real

Export x(a:point)real

Export z(a:point)real

Export w(a:point)real

Function print(p:point)seq.word
"(" + print(3, x.p) + ", " + print(3, y.p) + ", " + print(3, z.p)
+ if w.p = 1.0 then""else", " + print(3, w.p)/if
+ ")"

function max(p:point, q:point)point point(max(x.p, x.q), max(y.p, y.q), max(z.p, z.q), 1.0)

function min(p:point, q:point)point point(min(x.p, x.q), min(y.p, y.q), min(z.p, z.q), 1.0)

Function length(a:point)real sqrt((z.a)^2 + (x.a)^2 + (y.a)^2)

Function unit(a:point)point
let l = length.a
point(x.a / l, y.a / l, z.a / l) 