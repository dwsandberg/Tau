Module real

use UTF8

use seq.real

use standard

Function-(r:real)real 0.0 - r

Function abs(x:real)real if x < 0.0 then 0.0 - x else x

Builtin toreal(i:int)real

Builtin intpart(a:real)int

Function decpart(a:real)real a - toreal.intpart.a


Function  sin(a:real)real sinTau.a

Function  cos(a:real)real cosTau.a

Function  sqrt (a:real)real sqrtTau.a

Function  tan(a:real)real tanTau.a

builtin sinTau(a:real)real

builtin cosTau(a:real)real

builtin tanTau(a:real)real

builtin sqrtTau(a:real)real

Builtin arccos(a:real)real

Builtin arcsin(a:real)real


Function pi real 3.1415926535898

Builtin ?(a:real, b:real)ordering

Function =(a:real, b:real)boolean(a ? b) = EQ

Function >(a:real, b:real)boolean(a ? b) = GT

Function <(a:real, b:real)boolean b > a

Function max(a:real, b:real)real if(a ? b) = GT then a else b

Function min(a:real, b:real)real if(a ? b) = LT then a else b

Builtin +(a:real, b:real)real

Builtin-(a:real, b:real)real

Builtin *(a:real, b:real)real

Builtin /(a:real, b:real)real

Builtin representation(a:real)int

Builtin casttoreal(i:int)real

Function^(a:real, n:int)real
 if n = 0 then 1.0
 else if n = 1 then a
 else if n < 0 then 1.0 / a^(-n)
 else
  let d = n / 2
   a^d * a^(n - d)

Function *(a:int, b:real)real toreal.a * b

Export print(decimals:int, rin:real)seq.word

-------------