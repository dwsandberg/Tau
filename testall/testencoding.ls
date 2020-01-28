#!/usr/local/bin/tau

Module testencoding

Testing encodings

use checking

use encoding.testrecord

use process.int

use seq.boolean

use seq.testrecord

use stdlib

Function +(i:int, b:int)int export

run testencoding testencoding

function =(a:testrecord, b:testrecord)boolean key.a = key.b

Function print(a:testrecord)seq.word [ toword.key.a]+ body.a

function hash(a:testrecord)int key.a

type mydata is encoding testrecord

type mydata2 is encoding testrecord

type mydata3 is encoding testrecord

type mydata4 is encoding testrecord

type mydata5 is encoding testrecord

function add(z:erecord.testrecord, b:seq.word)int 
 let d = orderadded.z 
  let x = encode(z, testrecord(length.d + 1, b))
   1

type testrecord is record key:int, body:seq.word

Function testencoding seq.word 
 // must export this module so encoding type can be figured out // 
 let start = length.orderadded.mydata 
  let start2 = length.orderadded.mydata2 
  let start3 = length.orderadded.mydata3 
  let z = @(+, add(mydata), 0, ["firstadd","secondadd"])
  let z2 = @(+, add(mydata2), 0, ["one","two","three"])
  let z3 = @(+, add(mydata3), 0, ["temp"])
  let p = process.process1 
   if aborted.p 
    then"Failed encoding"+ message.p 
    else 
     let plen = result.p 
     let final = length.orderadded.mydata 
     let final2 = length.orderadded.mydata2 
     let final3 = length.orderadded.mydata3 
     let final4 = length.orderadded.mydata4 
      check([ start3 = 0, start = 0, start2 = 0, final = start + 2, final2 = start2 + 3, final3 = 4, final4 = 0, plen = 54,
         3=deepcopy.3,asset.[3,7,9]=deepcopy.asset.[3,7,9],
    deepcopy.testdeep1=testdeep1  
 ],"encoding")

Function process1 int 
 let z3 = @(+, add(mydata3), 0, ["A","B","C"])
  let z4 = @(+, add(mydata4), 0, ["A1","B2","C3","D4","E5"])
   length.orderadded.mydata4 * 10 + length.orderadded.mydata3

Function nextpower(i:int, base:int, start:int)int if i > start then nextpower(i, base, start * base)else start

use tree.seq.word


use blockseq.seq.word

use seq.tree.seq.word



use blockseq.seq.tree.seq.word


use deepcopy.int

use deepcopy.set.int

use set.int

use deepcopy.testdeep

use seq.char


type  testdeep is record fld1:seq.word, 
fld2:tree.seq.word,fld3:seq.char

function testdeep1 testdeep  testdeep("A BC DEF",tree("LIT 1",[tree("PARAM 1")]),decodeword("TEST"_1))

function =(a:testdeep,b:testdeep) boolean  fld1.a=fld1.b &and fld2.a=fld2.b &and fld3.a=fld3.b

Function test55 seq.word
   if  3=deepcopy.3 &and  asset.[3,7,9]=deepcopy.asset.[3,7,9]
    &and deepcopy.testdeep1=testdeep1  then "OK!" else "error"
  