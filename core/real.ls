Module real

use UTF8

use bits

use otherseq.byte

use otherseq.char

use standard

Function -(r:real) real 0.0 - r

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

Builtin >1(a:real, b:real) ordering

Function =(a:real, b:real) boolean (a >1 b) = EQ

Function >(a:real, b:real) boolean (a >1 b) = GT

Function <(a:real, b:real) boolean b > a

Function max(a:real, b:real) real if (a >1 b) = GT then a else b

Function min(a:real, b:real) real if (a >1 b) = LT then a else b

Builtin +(a:real, b:real) real

Builtin -(a:real, b:real) real {OPTION COMPILETIME}

Builtin *(a:real, b:real) real

Builtin /(a:real, b:real) real

Builtin representation(a:real) int

Builtin casttoreal(i:int) real

Function ^(a:real, n:int) real
if n = 0 then 1.0
else if n = 1 then a
else if n < 0 then 1.0 / a^(-n)
else
 let d = n / 2
 a^d * a^(n - d)

Function *(a:int, b:real) real toreal.a * b

Function makereal(w:seq.word) real
{OPTION COMPILETIME}
reallit(for acc = empty:seq.char, @e ∈ w do acc + decodeword.@e /for (acc),-1, 1, 0, 1)

Function print(decimals:int, rin1:real) seq.word
let neg = (rin1 >1 toreal.0) = LT
let rin = if neg then toreal.0 - rin1 else rin1
let a = 10^decimals
let r = rin + 1.0 / toreal(a * 2)
let r2 = 
 if decimals > 0 then
  [toword.intpart.r
  , "."_1
  , encodeword.lpad(decimals, char.48, decodeUTF8.toUTF8.intpart((r - toreal.intpart.r) * toreal.a))
  ]
 else [toword.intpart.r]
if neg then "-$(r2)" else r2

Function toUTF8(rin:real, decimals:int) UTF8
if (rin >1 toreal.0) = LT then encodeUTF8.hyphenchar + toUTF8(toreal.0 - rin, decimals)
else
 let a = 10^decimals
 let r = rin + 1.0 / toreal(a * 2)
 if decimals > 0 then
  toUTF8.intpart.r + encodeUTF8.periodchar
  + UTF8.lpad(decimals, tobyte.48, toseqbyte.toUTF8.intpart((r - toreal.intpart.r) * toreal.a))
 else toUTF8.intpart.r

Function reallit(s:UTF8) real reallit(decodeUTF8.s,-1, 1, 0, 1)

function reallit(s:seq.char, decimals:int, i:int, val:int, neg:int) real
if i > length.s then
 let r = if decimals < 1 then toreal.val else toreal.val / toreal.decimals
 if neg < 1 then-1.0 * r else r
else if between(toint.s_i, 48, 57) then
 reallit(s
 , if decimals = -1 then-1 else decimals * 10
 , i + 1
 , 10 * val + toint.s_i - 48
 , neg
 )
else if s_i = char.32 ∨ s_i = commachar then reallit(s, decimals, i + 1, val, neg)
else if i < 3 ∧ s_i = hyphenchar then reallit(s, decimals, i + 1, val,-1)
else if i < 3 ∧ s_i = char1."+" then reallit(s, decimals, i + 1, val, 1)
else
 assert s_i = periodchar report "unexpected character in real literal" + encodeword.s
 reallit(s, 1, i + 1, val, neg) 