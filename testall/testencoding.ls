#!/usr/local/bin/tau

run testencoding testencoding

module testencoding

Testing encodings

use checking

use ipair.linklists2


use process.int

use seq.boolean

use seq.testrecord

use stdlib

Function +(i:int,b:int) int export

   
 


function =(a:testrecord, b:testrecord)boolean key.a = key.b

Function print(a:testrecord)seq.word [ toword.key.a]+ body.a

function hash(a:testrecord)int key.a

type mydata is Encoding testrecord

type mydata2 is Encoding testrecord

type mydata3 is encoding testrecord

type mydata4 is encoding testrecord

type mydata5 is Encoding testrecord

function add(z:erecord.testrecord, b:seq.word)int 
 let d = mapping.z 
  let x=encode(testrecord(length.d + 1, b), z)
  1

type testrecord is record key:int, body:seq.word

Function testencoding seq.word 
 // must export this module so encoding type can be figured out // 
  let start = length.mapping.mydata 
  let start2 = length.mapping.mydata2 
  let start3 = length.mapping.mydata3 
  let z = @(+, add.mydata, 0, ["firstadd","secondadd"])
  let z2 = @(+, add.mydata2, 0, ["one","two","three"])
  let z3 = @(+, add.mydata3, 0, ["temp"])  
  let p = process.process1 
  if aborted.p 
  then"Failed encoding"+ message.p 
  else let plen = result.p 
   // let status = flush.mydata2 + flush.mydata + flush.mydata3 + flush.mydata5 //
  let final = length.mapping.mydata 
  let final2 = length.mapping.mydata2 
  let final3 = length.mapping.mydata3 
  let final4 = length.mapping.mydata4 
  check([ start3 = 0, 
  start > 0, 
  start2 > 0, 
  final = start + 2, 
  final2 = start2 + 3, 
  final3 = 4, 
  final4 = 0, 
  // status ="OK OK Encoding is not persistant.OK", // 
  plen = 54],"encoding")

Function process1 int 
 let z3 = @(+, add.mydata3, 0, ["A","B","C"])
  let z4 = @(+, add.mydata4, 0, ["A1","B2","C3","D4","E5"])
  length.mapping.mydata4 * 10 + length.mapping.mydata3

Function nextpower(i:int, base:int, start:int)int 
 if i > start then nextpower(i, base, start * base)else start

