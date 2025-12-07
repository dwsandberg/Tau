Module real

use UTF8

use bits

use seq1.byte

use seq1.char

use kernal

use standard

Function -(r:real) real 0.00 - r

Function abs(x:real) real if x < 0.0 then 0.0 - x else x

Builtin toreal(i:int) real

Builtin intpart(a:real) int

Function decpart(a:real) real a - toreal.intpart.a

Builtin sin(a:real) real

Builtin cos(a:real) real

Builtin sqrt(a:real) real

Builtin tan(a:real) real

Builtin arccos(a:real) real

Builtin arcsin(a:real) real

Function pi real 3.1415926535898

Function NaN real casttoreal.toint."0x7FF8000000000000" sub 1

Builtin >1(a:real, b:real) ordering

Function =(a:real, b:real) boolean a >1 b = EQ

Function >(a:real, b:real) boolean a >1 b = GT

Function <(a:real, b:real) boolean b > a

Function max(a:real, b:real) real if a >1 b = GT then a else b

Function min(a:real, b:real) real if a >1 b = LT then a else b

Builtin +(a:real, b:real) real

Builtin -(a:real, b:real) real

Builtin *(a:real, b:real) real

Builtin /(a:real, b:real) real

Builtin representation(a:real) int

Builtin casttoreal(i:int) real

Function sup(a:real, n:int) real
if n = 0 then 1.0
else if n = 1 then a
else if n < 0 then 1.0 / a sup -n
else
 let d = n / 2,
 a sup d * a sup (n - d)

Function *(a:int, b:real) real toreal.a * b

Function makereal(w:seq.word) real
reallit(
 for acc = empty:seq.char, @e ∈ w do acc + decodeword.@e,
 acc
 , -1
 , 1
 , 0
 , 1
)

function isNaN(r:real) boolean representation.r = representation.NaN

Function %(decimalPlaces:int, rin1:real) seq.word
{converts rin1 to text form with specified number no decimal places.}
if representation.rin1 = representation.NaN then "NaN"
else
 let neg = rin1 >1 toreal.0 = LT
 let rin = if neg then toreal.0 - rin1 else rin1
 let a = 10 sup decimalPlaces
 let r = rin + 1.0 / toreal(a * 2),
 let r2 =
  if decimalPlaces > 0 then
   [
    toword.intpart.r
    , "." sub 1
    , encodeword.lpad(decimalPlaces, char.48, decodeUTF8.toUTF8.intpart((r - toreal.intpart.r) * toreal.a))
   ]
  else [toword.intpart.r],
 if neg then "-:(r2)" else r2

Function toUTF8(rin1:real, decimals:int) UTF8
let neg = rin1 >1 toreal.0 = LT
let rin = if neg then toreal.0 - rin1 else rin1
let a = 10 sup decimals
let r = rin + 1.0 / toreal(a * 2)
let r2 =
 if decimals > 0 then
  toUTF8.intpart.r
  + encodeUTF8.periodchar
  + UTF8.lpad(decimals, tobyte.48, toseqbyte.toUTF8.intpart((r - toreal.intpart.r) * toreal.a))
 else toUTF8.intpart.r,
if neg ∧ rin1 ≠ 0.0 then encodeUTF8.hyphenchar + r2 else r2

Function reallit(s:UTF8) real reallit(decodeUTF8.s, -1, 1, 0, 1)

function reallit(s:seq.char, decimals:int, i:int, val:int, neg:int) real
if i > n.s then
 let r = if decimals < 1 then toreal.val else toreal.val / toreal.decimals,
 if neg < 1 then -1.0 * r else r
else if between(toint.s sub i, 48, 57) then
 reallit(
  s
  , if decimals = -1 then -1 else decimals * 10
  , i + 1
  , 10 * val + toint.s sub i - 48
  , neg
 )
else if s sub i = char.32 ∨ s sub i = commachar then reallit(s, decimals, i + 1, val, neg)
else if i < 3 ∧ s sub i = hyphenchar then reallit(s, decimals, i + 1, val, -1)
else if i < 3 ∧ s sub i = char1."+" then reallit(s, decimals, i + 1, val, 1)
else
 assert s sub i = periodchar report "unexpected character in real literal" + encodeword.s,
 reallit(s, 1, i + 1, val, neg)
 