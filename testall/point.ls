Module point.T

use stdlib

type point is record x:T, y:T, z:T

Function +(T, T)T unbound

Function-(T, T)T unbound

Function =(T, T)boolean unbound

Function point(a:T, b:T, c:T)point.T export

Function +(a:point.T, b:point.T)point.T
 point(x.a + x.b, y.a + y.b, z.a + z.b)

Function-(a:point.T, b:point.T)point.T
 point(x.a - x.b, y.a - y.b, z.a - z.b)

Function =(a:point.T, b:point.T)boolean
 x.a = x.b ∧ y.a = y.b ∧ z.a = z.b

Function y(a:point.T)T export

Function x(a:point.T)T export

Function z(a:point.T)T export