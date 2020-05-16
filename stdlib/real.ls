Module real

use UTF8

use otherseq.real

use seq.real

use stdlib

type real is record representation:int

Function type:real internaltype export

Function -(r:real)real 0.0 - r

Function abs(x:real)real if x < 0.0 then 0.0 - x else x

Function toreal(i:int)real builtin.usemangle

Function intpart(a:real)int builtin.usemangle

Function decpart(a:real)real a - toreal.intpart.a

Function sqrt(a:real)real builtin.usemangle

Function sin(a:real)real builtin.usemangle

Function arccos(a:real)real builtin.usemangle

Function arcsin(a:real)real builtin.usemangle

Function cos(a:real)real builtin.usemangle

Function tan(a:real)real builtin.usemangle

Function pi real 3.1415926535898

Function ?(a:real, b:real)ordering builtin.usemangle

Function =(a:real, b:real)boolean(a ? b) = EQ

Function >(a:real, b:real)boolean(a ? b) = GT

Function <(a:real, b:real)boolean export

Function max(a:real, b:real)real if(a ? b) = GT then a else b

Function min(a:real, b:real)real if(a ? b) = LT then a else b

Function +(a:real, b:real)real builtin.usemangle

Function -(a:real, b:real)real builtin.usemangle

Function *(a:real, b:real)real builtin.usemangle

Function /(a:real, b:real)real builtin.usemangle

Function representation(a:real)int export

Function casttoreal(i:int)real builtin."LOCAL 1"

Function^(i:real, n:int)real @(*, identity, 1.0, constantseq(n, i))

Function *(a:int, b:real)real toreal.a * b

Function print(decimals:int, rin:real)seq.word export

- - - - - - - - - - - - -