Module real

type real

use UTF8

use seq.real

/use seq.seq.real 

/use seq.word

/use seq.int

use stdlib

Function-(r:real)real 0.0 - r

Function abs(x:real)real if x < 0.0 then 0.0 - x else x

Function int2real(i:int)real builtin.usemangle

Function intpart(a:real)int builtin.usemangle

Function decpart(a:real)real a - int2real.intpart.a

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

Function representation(a:real)int builtin.NOOP

Function casttoreal(i:int)real builtin.NOOP

Function^(i:real, n:int)real @(*, identity, 1.0, constantseq(n, i))

Function makereal(whole:int, digits:int)real 
 if digits < 7 
  then int2real.whole / int2real([ 10, 100, 1000, 10000, 100000, 1000000]_digits)
  else int2real.whole / int2real(10^digits)

Function print(rin:real, decimals:int)seq.word 
 {(if rin < 0.0 then [ space]else empty:seq.word)+ towords.toUTF8(rin, decimals)}

Function toUTF8(rin:real, decimals:int)seq.int 
 if rin ? int2real.0 = LT 
  then [ hyphenchar]+ toUTF8(int2real.0 - rin, decimals)
  else let a = 10^decimals 
  let r = rin + 1.0 / int2real(a * 2)
  toseqint.toUTF8.intpart.r + if decimals > 0 
   then [ decode("."_1)_1]+ lpad(toseqint.toUTF8.intpart((r - int2real.intpart.r)* int2real.a), decimals)
   else empty:seq.int

Function lpad(l:seq.int, n:int)seq.int constantseq(n - length.l, 48)+ l

Function reallit(s:seq.int)real reallit(s, -1, 1, 0, 1)

Function reallit(s:seq.int, decimals:int, i:int, val:int, neg:int)real 
 if i > length.s 
  then let r = if decimals < 1 
    then int2real.val 
    else if decimals < 7 
    then int2real.val / int2real([ 10, 100, 1000, 10000, 100000, 1000000]_decimals)
    else int2real.val / int2real(10^decimals)
   if neg < 1 then -(1.0 * r) else r 
  else if between(s_i, 48, 57)
  then reallit(s, if decimals = -1 then -1 else decimals + 1, i + 1, 10 * val + s_i - 48, neg)
  else if s_i = 32 ∨ s_i = commachar 
  then reallit(s, decimals, i + 1, val, neg)
  else if i < 3 ∧ s_i = hyphenchar 
  then reallit(s, decimals, i + 1, val, -1)
  else assert s_i = decode("."_1)_1 report"unexpected character in real literal"+ encodeword.s 
  reallit(s, decimals + 1, i + 1, val, neg)

-------------

