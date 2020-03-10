#!/usr/local/bin/tau

Module testall

Library testall checking myseq point randomphrase test11 test11a test2 test20 test5 
testencoding  testopt tree2 testmodules
 uses stdlib 
 exports checking randomphrase test11 test11a test2 test5 testall testencoding testopt testmodules

/run randomphrase randomphrase

/run testencoding testencoding

run testall testall

* usegraph exclude stdlib

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

Function testall seq.word 
 test5 + test11 + test11a + testencoding + testmodules+testopt + check([ print(3, sqrt.2.0)="1.414"
 , print(2, toreal.3)="3.00"
 , intpart.3.1 = 3 
 , print(3, 2.0 / 3.0)="0.667"
 , 2.0 + 3.0 = 5.0 
 , 2.0 * 3.0 = 6.0 
 , print(5, 2.3 - 1.1)="1.20000"
 , print(5, cos.0.4)="0.92106"
 , print(5, sin.0.4)="0.38942"
 , 1.0 ? 2.0 = LT 
 ,-1.9 ?-3.0 = GT 
 , 3.00 ? 3.000 = EQ 
 , print(5, tan(pi / 4.0))="1.00000"
 , print(5, arcsin.sin.0.5)="0.50000"
 , print(5, arccos.cos.0.5)="0.50000"
 ,- 2^4 =-16 
 , alphasort."function segment s seq int i seq word addcomma toword merge C 1 toword"="1 C addcomma function i int merge s segment seq seq toword toword word"
 , @(seperator("/")
 , identity 
 ,""
 , alphasort.["z b","a b","a a","test 23","test 20"])
 ="a a / a b / test 20 / test 23 / z b"]
 ,"real")
 + test2

