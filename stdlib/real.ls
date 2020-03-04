Module real


use seq.real

use stdlib

use otherseq.real

use subreal


type real is record representation:int

Function type:real internaltype  export

Function-(r:real)real 0.0 - r

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

Function =(a:real, b:real)boolean a ? b = EQ

Function >(a:real, b:real)boolean a ? b = GT

Function <(a:real, b:real)boolean export

Function max(a:real, b:real)real if a ? b = GT then a else b

Function min(a:real, b:real)real if a ? b = LT then a else b

Function +(a:real, b:real)real builtin.usemangle

Function-(a:real, b:real)real builtin.usemangle

Function *(a:real, b:real)real builtin.usemangle

Function /(a:real, b:real)real builtin.usemangle

Function representation(a:real)int export

Function casttoreal(i:int)real builtin."PARAM 1"

Function^(i:real, n:int)real @(*, identity, 1.0, constantseq(n, i))

Function *(a:int, b:real)real toreal.a * b


Function makereal(whole:int, decdigits:int)real 
   //  real number value  is whole / 10^decdigits //
 if decdigits < 7 
  then toreal.whole / toreal([ 10, 100, 1000, 10000, 100000, 1000000]_decdigits)
  else toreal.whole / toreal(10^decdigits)

Function print( decimals:int,rin:real) seq.word export


Function reallit(s:UTF8)real export 


Function toUTF8(rin:real, decimals:int) UTF8 export




-------------

module subreal 

use real

use stdlib

use UTF8


use words

use seq.char

use textio

Function print( decimals:int,rin:real)seq.word 
 {(if rin < 0.0 then [ space]else empty:seq.word)+ towords.toUTF8(rin, decimals)}


Function toUTF8(rin:real, decimals:int) UTF8
 if rin ? toreal.0 = LT 
  then   encodeUTF8.hyphenchar + toUTF8(toreal.0 - rin, decimals)
  else let a = 10^decimals 
  let r = rin + 1.0 / toreal(a * 2)
    if decimals > 0 
   then toUTF8.intpart.r +encodeUTF8.periodchar+ lpad(toseqint.toUTF8.intpart((r - toreal.intpart.r)* toreal.a), decimals)
   else toUTF8.intpart.r 


Function reallit(s:UTF8)real reallit(toseqint.s,-1, 1, 0, 1)


function reallit(s:seq.int, decimals:int, i:int, val:int, neg:int)real 
 if i > length.s 
  then let r = if decimals < 1 then toreal.val  else makereal(val,decimals) 
   if neg < 1 then-(1.0 * r)else r 
  else if between(s_i, 48, 57)
  then reallit(s, if decimals =-1 then-1 else decimals + 1, i + 1, 10 * val + s_i - 48, neg)
  else if s_i = 32 ∨ s_i = toint.commachar 
  then reallit(s, decimals, i + 1, val, neg)
  else if i < 3 ∧ s_i = toint.hyphenchar 
  then reallit(s, decimals, i + 1, val,-1)
  else if i < 3 ∧ s_i = toint.(decodeword."+"_1 )_1
  then reallit(s, decimals, i + 1, val,1)
  else assert s_i = toint.periodchar report"unexpected character in real literal"+ encodeword.tocharseq.s 
  reallit(s, decimals + 1, i + 1, val, neg)

Function lpad(l:seq.int, n:int) UTF8 UTF8(constantseq(n - length.l, 48)+ l)


