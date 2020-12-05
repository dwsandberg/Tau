#!/usr/local/bin/tau ; use testall ; testall

Module testall

Library testall bug7 checking myseq point randomphrase test11 test11a test2 test20 test5 testencoding testmodules testopt testprocess testseq tree2
uses stdlib
exports bug7 checking point randomphrase test11 test11a test2 test5 testall testencoding testmodules testopt testprocess tree2

* usegraph exclude stdlib

use bug7

use checking

use real

use stdlib

use test11

use test11a

use test2

use test5

use testencoding

use testmodules

use testopt

use testprocess

use testseq

Function testall seq.word // this is a comment //
test5 + test11 + test11a + testencoding + testprocess + testmodules + testbug7 + testopt
+ check([ print(3, sqrt.2.0) = "1.414", print(2, toreal.3) = "3.00", intpart.3.1 = 3, print(3, 2.0 / 3.0) = "0.667", 2.0 + 3.0 = 5.0, 2.0 * 3.0 = 6.0, print(5, 2.3 - 1.1) = "1.20000", print(5, cos.0.4) = "0.92106", print(5, sin.0.4) = "0.38942",(1.0 ? 2.0) = LT
,(-1.9 ? -3.0) = GT,(3.00 ? 3.000) = EQ, print(5, tan(pi / 4.0)) = "1.00000", print(5, arcsin.sin.0.5) = "0.50000", print(5, arccos.cos.0.5) = "0.50000", print(3, [ 8, 9, 10, 11]@@ +(0.0, toreal.@e)) = "38.000","23.45000-18.45000"
= print(5, 23.45) + print(5, 5.0 - 23.45),-2^4 = -16, alphasort."function segment s seq int i seq word addcomma toword merge C 1 toword"
= "1 C addcomma function i int merge s segment seq seq toword toword word",(alphasort.["z b","a b","a a","test 23","test 20"])@@ list("","/", @i, @e)
= "a a / a b / test 20 / test 23 / z b"]
,"real")
+ testseq
+ test2

Module dseq.T

use otherseq.T

use stdlib

dseq lets a sequence have a default value even beyond the length of the seq.

/ type dseq is sequence length:int, default:T, data:seq.T

/ Function_(d:dseq.T, i:int)T if i > length.data.d then default.d else(data.d)_i

 
/ Function replace(a:seq.T, b:int, v:T)seq.T
 let d = to:dseq.T(a)
  if length.d = 0 then replace2(a, b, v)
  else
   let s = if b > length.a then
   replace2(data.d + constantseq(b - length.a, default.d), b, v)
   else replace2(data.d, b, v)
    toseq.dseq(length.s, default.d, s)

/ Function dseq(d:T)seq.T toseq.dseq(1, d, [ d])

/ Function dseq(d:T, s:seq.T)seq.T toseq.dseq(1, d, s)

/   function replace2(s:seq.T, index:int, value:T)seq.T  
 let p = to:pseq.T(s)
  if length.p = 0 then
  @(+,_.s, @(+,_.s, empty:seq.T, arithseq(index - 1, 1, 1)) + value, arithseq(length.s - index, 1, index + 1))
  else if index > length.a.p then
  a.p + replace2(b.p, index - length.a.p, value)
  else replace2(a.p, index, value) + b.p
