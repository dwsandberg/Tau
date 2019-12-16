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
 test5 + test11 +   test11a +     testencoding +   check([ print(sqrt.2.0, 3)="1.414", 
 print(int2real.3, 2)="3.00", 
 intpart.3.1 = 3, 
 print(2.0 / 3.0, 3)="0.667", 
 2.0 + 3.0 = 5.0, 
 2.0 * 3.0 = 6.0, 
 print(2.3 - 1.1, 5)="1.20000", 
 print(cos.0.4, 5)="0.92106", 
 print(sin.0.4, 5)="0.38942", 
 1.0 ? 2.0 = LT, 
 -1.9 ? -3.0 = GT, 
 3.00 ? 3.000 = EQ, 
 print(tan(pi / 4.0), 5)="1.00000", 
 print(arcsin.sin.0.5, 5)="0.50000", 
 print(arccos.cos.0.5, 5)="0.50000", 
 test20],"real")

