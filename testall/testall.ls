#!/usr/local/bin/tau

Library testall test2 test5   tree2 test11 test11a myseq  randomphrase
checking testgraph point2d point uses stdlib exports testall checking test2 test5 test11 test11a testencoding
randomphrase

Module testall

/run randomphrase randomphrase

run testall testall


use stdlib

use test2

use test11

use test11a

use test5

use test20

use real

use checking

use options.seq.word

use testencoding

Function testall seq.word 
    test5  +    test11 + test11a   +  testencoding
  +    check([ 
   print(sqrt(2.0),3)="1.414",
   print(int2real(3),2)="3.00",
   intpart(3.1)=3,
   print(2.0 / 3.0,3)="0.667" , 
   2.0 +  3.0 = 5.0 ,
    2.0 * 3.0 = 6.0 , 
    print(2.3 - 1.1,5) = "1.20000",
    print(cos(0.4),5)="0.92106",
    print(sin(0.4),5)="0.38942",
    1.0 ? 2.0=LT, -1.9 ? -3.0=GT,  3.00 ? 3.000=EQ,
    print(tan (pi / 4.0),5)="1.00000",
    print(arcsin (sin (0.5)) ,5)="0.50000",
    print(arccos (cos (0.5)) ,5)="0.50000", 
    test20
    ],"real")+  test2


module testencoding

use stdlib

use checking

use seq.boolean

use seq.testrecord

function =(a:testrecord, b:testrecord)boolean key.a = key.b

function print(a:testrecord)  seq.word  [toword.key.a]+body.a

function hash(a:testrecord)int key.a

type mydata is Encoding testrecord

type mydata2 is Encoding testrecord

type mydata3 is encoding testrecord

function add(z:erecord.testrecord, b:seq.word) int
let d = mapping.z 
encoding.encode(testrecord(length.d + 1, b), z) 

type testrecord is record key:int, body:seq.word

use process.int

Function testencoding seq.word
  // not sure how should behavior of temp encoding and processes should interact. //
  // must export this module so encoding type can be figured out //
  let start=length.mapping.mydata
  let start2=length.mapping.mydata2
  let start3=length.mapping.mydata3
  let   z = @(+,add.mydata,0,  ["firstadd", "secondadd"])
  let z2 = @(+,add.mydata2,0,  ["one", "two","three"]) 
   let z3 =  @(+,add.mydata3,0,  ["temp"]) 
   let p = process.process1
   if aborted.p then "Failed encoding"+message.p else 
  let plen=result.p
  let status=flush.mydata2  
   +flush.mydata+flush.mydata3
  let final=length.mapping.mydata
  let final2=length.mapping.mydata2
  let final3=length.mapping.mydata3
  check([start3=0 , start > 0, start2 > 0,final=start+2, final2=start2+3 ,final3=4
   ,  status="OK OK Encoding is not persistant." , plen=4 ],"encoding")

Function process1  int
   let z3 =  @(+,add.mydata3,0,  ["A","B","C"]) length.mapping.mydata3

Function nextpower(i:int, base:int, start:int)int
 if i > start then nextpower(i, base, start * base)else start


Module test20

use stdlib

type p is struct a:int,b:int,c:int

type q is struct d:int,e:p,f:int

Function p (a:int,b:int,c:int ) p export

Function  q (a:int,b:p,c:int) q export

function z q q(1,p(2,3,4),5)

function f2 seq.int    [ d.z,a.e.z,b.e.z,c.e.z,f.z]

Function test20 boolean f2=[1,2,3,4,5]

Function c11 seq.q
[q(4,p(1,2,3),5)
,q(41,p(11,21,31),51)]
