Module point.T

use standard

type point is x:T, y:T, z:T

unbound +(T, T)T

unbound-(T, T)T

unbound =(T, T)boolean

Export point(a:T, b:T, c:T)point.T

Function +(a:point.T, b:point.T)point.T
 point(x.a + x.b, y.a + y.b, z.a + z.b)

Function-(a:point.T, b:point.T)point.T
 point(x.a - x.b, y.a - y.b, z.a - z.b)

Function =(a:point.T, b:point.T)boolean
 x.a = x.b ∧ y.a = y.b ∧ z.a = z.b

Export y(a:point.T)T export

Export x(a:point.T)T

Export z(a:point.T)T