#!/usr/local/bin/tau

run testprocess testprocess

Module testprocess

use stdlib

use process.seq.word

use process.int

use checking

use process.boolean

use process.returntype

use real

type returntype is record a:int,b:int,c:seq.word

function  testprocess3  returntype   returntype(  4 ,40,"a test")


 function isprefix(prefix:seq.word, s:seq.word)boolean subseq(s, 1, length.prefix)= prefix
 
 

function testout(i:int)seq.word ["one two three"_i]

function redgreen seq.word "red green"

function arg4(a:int,b:int,c:int,d:int) int a+b+c+d

Function testprocess seq.word 
let z = subseq("f red green",2,3)
 let y = [  not.isprefix("out of bounds","out"),
  isprefix("out of bounds", message.process.testout.0),
  isprefix("out of bounds", message.process.testout.-10)
, isprefix("out of bounds", message.process.testout.4)
 , message.process.testout.1 = "normal exit"
 , aborted.process.testout.5 
 , not.aborted.process.testout.2 
  ,  result.process.testout.3 ="three"
 , result.process.isprefix("red",z)
 , result.process.redgreen=redgreen
 ,  result.process.arg4(1,2,3,4)=10
 , message.process.result.process.testout.4 ="no result of aborted process" 
 , a.result.process.testprocess3=4 &and b.result.process.testprocess3=40
 ,t513,t514  ,isprefix("invalid digit", message.process.toint."0A"_1)
 ,t520
  ] 
   check(y,"testprocess")
   
use UTF8

function t518 boolean isprefix("invalid digit", message.process.toint."0A"_1)

function t520 boolean
let s = message.process.subtest520.merge."45t6.3"
  isprefix("unexpected character in real literal",s)

function subtest520(t:word)int
 intpart.reallit.UTF8.tointseq.decodeword.t
  

   
_________

Primes

function t513 boolean"3 5 7 11 13 17 19 23 29 31 37"= findprimes(3, 40)

function t514 boolean 
 let c=10000
 let a = process.countprimes(3, c)
  let b = process.countprimes(c+1, 2 * c)
   [ 1228,1033]= [ result.a, result.b]
   

function findprimes(start:int, end:int)seq.word 
 @(+, isprime3,"", arithseq((end - start + 2)/ 2, 2, start))

function countprimes(start:int, end:int)int @(+, isprime4, 0, arithseq((end - start + 2)/ 2, 2, start))

function isprime3(i:int)seq.word if isprime.i then [ toword.i]else""

function isprime4(i:int)int if isprime.i then 1 else 0

function isprime(i:int)boolean 
 if i mod 2 = 0 
  then i = 2 
  else 
   let a = i / 2 // intpart.sqrt.toreal.i //
   let b =(a + i / a)/ 2 
    subisprime(i, 3, b)

function subisprime(i:int, f:int, b:int)boolean if f > b then true else if i mod f = 0 then false else subisprime(i, f + 2, b)

