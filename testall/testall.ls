#!/usr/local/bin/tau

test11a


Module testall

Library testall point test11a checking myseq  point2d randomphrase test11     test20 test5 testencoding testgraph tree2 
 uses stdlib 
 exports checking randomphrase test11 test11a test2 test5 testall testencoding


/run randomphrase randomphrase

/run testencoding testencoding

run testall testall

* usegraph exclude stdlib

use checking


use real

use stdlib

use test11

use test11a

/use test2

use test20

use test5

use testencoding

Function testall seq.word "hello"
+
 test5 + test11 +   test11a +     testencoding +   check([ print(3,sqrt.2.0)="1.414", 
 print(2,toreal.3)="3.00", 
 intpart.3.1 = 3, 
 print(3,2.0 / 3.0)="0.667", 
 2.0 + 3.0 = 5.0, 
 2.0 * 3.0 = 6.0, 
 print(5,2.3 - 1.1)="1.20000", 
 print(5,cos.0.4)="0.92106", 
 print(5,sin.0.4)="0.38942", 
 1.0 ? 2.0 = LT, 
 -1.9 ? -3.0 = GT, 
 3.00 ? 3.000 = EQ, 
 print(5,tan(pi / 4.0))="1.00000", 
 print(5,arcsin.sin.0.5)="0.50000", 
 print(5,arccos.cos.0.5)="0.50000", -2^4=-16,
 test20],"real")

