Module test5

use UTF8

use checking

use fileio

use graph.int

use ipair.word

use myseq.int


use process.int

use process.seq.word

use randomphrase

use real

use seq.arc.int

use seq.char

use seq.int

use seq.ipair.word

use seq.ordering

use seq.tree.word

use seq.word

use set.arc.int

use set.int

use set.word

use stdlib

use textio

use tree.int

use tree.word

use  otherseq.word

use otherseq.int

use words

/use invertedseq.word

Function test5 seq.word 
 let y = [  t502, t507,  
   t513, t514, t515, t516, t517, t518, t519, t520 
  , t522,  t524]
   check(y,"test5")
   
 

function print(a:seq.int)seq.word 
 "["+ @(seperator(","), toword,"", a)+"]"

Function t502 boolean 
 "23.45000 - 18.45000"= print(5, 23.45)+ print(5, 5.0 - 23.45)


function showcodes(i:int)seq.word [ toword.i, encodeword.[ char.i]]

Function t507 boolean 
 "code glyph 48 0 49 1 50 2 51 3 52 4 53 5 54 6 55 7 56 8 57 9 58:59 ; 60 < 61 = 62 > 63 ? 64 @ 65 A 66 B 67 C 68 D 69 E 70 F 
 71 G 72 H 73 I 74 J 75 K 76 L 77 M 78 N 79 O 80 P 81 Q 82 R 83 S 84 T 85 U 86 V 87 W 88 X 89 Y 90 Z"
 = @(+, showcodes,"code glyph", arithseq(43, 1, 48))
 
 function t515 boolean 
 let s = UTF8.[ 40, 50]+ encodeUTF8.char.335 + encodeUTF8.char.50 + encodeUTF8.char.336 
   @(+, toword,"", myseq.toseqint.s)="40 50 335 50 336"

function t519 boolean"&quot()+,-.:= []^_"= standalonechars

function ttt(c:int)seq.word if classify.c = 1 then [ encodeword.[ char.c]]else""

Function standalonechars seq.word @(+, ttt,"", arithseq(127, 1, 0))

Function t524 boolean 
 // testing UNICODE to word conversion and no-break space in integer 8746 // decodeword."1 2∪"_1 = [ char.49, char.160, char.50, char.87 46]










_______________

Primes

function t513 boolean"3 5 7 11 13 17 19 23 29 31 37"= findprimes(3, 40)

function t514 boolean 
 let a = process.countprimes(3, 5000000)
  let b = process.countprimes(5000001, 10000000)
   [ 348512, 316066]= [ result.a, result.b]

function findprimes(start:int, end:int)seq.word 
 @(+, isprime3,"", arithseq((end - start + 2)/ 2, 2, start))

function countprimes(start:int, end:int)int @(+, isprime4, 0, arithseq((end - start + 2)/ 2, 2, start))

function isprime3(i:int)seq.word if isprime.i then [ toword.i]else""

function isprime4(i:int)int if isprime.i then 1 else 0

function isprime(i:int)boolean 
 if i mod 2 = 0 
  then i = 2 
  else 
   let a = intpart.sqrt.toreal.i 
   let b =(a + i / a)/ 2 
    subisprime(i, 3, b)

function subisprime(i:int, f:int, b:int)boolean if f > b then true else if i mod f = 0 then false else subisprime(i, f + 2, b)

________________



function isprefex(prefix:seq.word, s:seq.word)boolean subseq(s, 1, length.prefix)= prefix

function testout(i:int)seq.word ["one two three"_i]

function t517 boolean 
 isprefex("out of bounds", message.process.testout.0)∧ isprefex("out of bounds", message.process.testout.-10)
 ∧ isprefex("out of bounds", message.process.testout.4)
 ∧ message.process.testout.1 ="normal exit"
 ∧ aborted.process.testout.5 
 ∧ not.aborted.process.testout.2 
 ∧ result.process.testout.3 ="three"
 ∧ message.process.result.process.testout.4 ="no result of aborted process"

function t518 boolean isprefex("invalid digit", message.process.toint."0A"_1)


function t520 boolean 
 let s = message.process.subtest520.merge."45t6.3"
   subseq(s, 1, length.s - 1)="unexpected character in real literal"

function subtest520(t:word)int 
 let x = reallit.UTF8.tointseq.decodeword.merge."45t6.3"
   intpart.x


function filetest(i:int)boolean 
 let name ="test"+ toword.i +".txt"
  let a = createbytefile(name, arithseq(i, 1, 48))
   fileexists.name ∧ i = length.getfile.name

Function t522 boolean @(∧, filetest, true, arithseq(9, 1, 4))




function testset set.int asset.[ 2, 5, 6, 9, 12, 15, 35, 36]

function ?2(a:int, b:int)ordering a / 10 ? b / 10

function print(a:set.int)seq.word @(+, toword,"", toseq.a)



function t516 boolean toseq.findelement2(testset, 36)= [ 35, 36]∧ toseq.findelement2(testset, 15)= [ 12, 15]


