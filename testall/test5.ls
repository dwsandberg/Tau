Module test5

use UTF8

use checking

use graph.int

use invertedseq.word

use ipair.word

use myseq.int


use point2d

use process.int

use process.seq.word

use randomphrase

use real

use seq.arc.int

use seq.int

use seq.ipair.word

use seq.word

use set.arc.int

use set.int

use set.word

use stdlib

use textio

Function test5 seq.word 
  let y = [ test501, t502, t503, t504, t505, t506, t507, t508, t509, t510, 
  t511, t512, t513, t514, t515, t516, t517, t518, t519, t520, 
  t521, t522, t523]
  check(y,"test5")

Function test501 boolean {"(6, 8)"= print(point2d(2, 3)+ point2d(4, 5))}

function print(a:seq.int)seq.word 
 {"["+ @(seperator.",", toword,"", a)+"]"}

Function t502 boolean 
 {"23.45000"+ [ space]+"-18.45000"= print(23.45, 5)+ print(5.0 - 23.45, 5)}

Function t503 boolean {"[ 2, 3, 4, 5]"= print.[ 2, 3, 4, 5]}

Function t504 boolean 10 = @(+, *.1, 0, [ 1, 2, 3, 4])

Function t505 boolean 24 = @(*, *.1, 1, [ 1, 2, 3, 4])

Function t506 boolean [ 1, 2, 3, 4]= @(+, +.empty:seq.int, empty:seq.int, [ 1, 2, 3, 4])

function showcodes(i:int)seq.word [ toword.i, encodeword.toseqint.UTF8.i]

Function t507 boolean 
 {"code glyph 48 0 49 1 50 2 51 3 52 4 53 5 54 6 55 7 56 8 57 9 58:59 ; 60 < 61 = 62 > 63 ? 64 @ 65 A 66 B 67 C 68 D 69 E 70 F 71 G 72 H 73 I 74 J 75 K 76 L 77 M 78 N 79 O 80 P 81 Q 82 R 83 S 84 T 85 U 86 V 87 W 88 X 89 Y 90 Z"= @(+, showcodes,"code glyph", arithseq(43, 1, 48))}

Function t508 boolean 
 let a = 6 * 6 
  a + a = 72

function modr(a:int, b:int)int b mod a + 1

function incrementcount(s:seq.int, i:int)seq.int replace(s, i, s_i + 1)

function print(i:ipair.word)seq.word [ toword.index.i]+":"+ value.i

Function t509 boolean 
 let s = @(incrementcount, identity, constantseq(100, 0), @(+, modr.100, empty:seq.int, randomseq(3456, 100001)))
  let totalcounts = @(+, identity, 0, s)
  length.s = 100 ∧ totalcounts = 100001

Function t510 boolean 
 {"a b c d e 1 2 3 4 k"= replace("a b c d e"+"1 2 3 4 5", 10,"k"_1)}

Function t511 boolean 
 {"1 2 k 4 5"= replace("1 2 3 4 5", 3,"k"_1)}

Function t512 boolean 
 let r = @(+, print, empty:seq.word, toipair.add(add(invertedseq("HI"_1), 3,"HI"_1), ipair(4,"dI"_1)))
  r in ["3:HI 4:dI","4:dI 3:HI"]

function testset set.int asset.[ 2, 5, 6, 9, 12, 15, 35, 36]

function print(a:set.int)seq.word @(+, toword,"", toseq.a)

function ?2(a:int, b:int)ordering a / 10 ? b / 10

_______________

Primes

function t513 boolean {"3 5 7 11 13 17 19 23 29 31 37"= findprimes(3, 40)}

function t514 boolean 
 let a = process.countprimes(3, 5000000)
  let b = process.countprimes(5000001, 10000000)
  [ 348512, 316066]= [ result.a, result.b]

function findprimes(start:int, end:int)seq.word 
 @(+, isprime3,"", arithseq((end - start + 2)/ 2, 2, start))

function countprimes(start:int, end:int)int @(+, isprime4, 0, arithseq((end - start + 2)/ 2, 2, start))

function isprime3(i:int)seq.word 
 if isprime.i then [ toword.i]else""

function isprime4(i:int)int if isprime.i then 1 else 0

function isprime(i:int)boolean 
 if i mod 2 = 0 
  then i = 2 
  else let a = intpart.sqrt.int2real.i 
  let b =(a + i / a)/ 2 
  subisprime(i, 3, b)

function subisprime(i:int, f:int, b:int)boolean 
 if f > b then true else if i mod f = 0 then false else subisprime(i, f + 2, b)

________________

function t515 boolean 
 let s = UTF8.[ 40, 50]+ UTF8.335 + UTF8.50 + UTF8.336 
  @(+, toword,"", myseq.toseqint.s)="40 50 335 50 336"

function t516 boolean toseq.findelement2(testset, 36)= [ 35, 36]∧ toseq.findelement2(testset, 15)= [ 12, 15]

function isprefex(prefix:seq.word, s:seq.word)boolean subseq(s, 1, length.prefix)= prefix

function testout(i:int)seq.word ["one two three"_i]

function t517 boolean 
 isprefex("out of bounds", message.process.testout.0)∧ isprefex("out of bounds", message.process.testout(-10))∧ isprefex("out of bounds", message.process.testout.4)∧ message.process.testout.1 ="normal exit"∧ aborted.process.testout.5 ∧ not.aborted.process.testout.2 ∧ result.process.testout.3 ="three"∧ message.process.result.process.testout.4 ="no result of aborted process"

function t518 boolean isprefex("invalid digit", message.process.toint("0A"_1))

function t519 boolean {"&quot()+,-.: = []^_"= standalonechars }

function ttt(c:int)seq.word 
 if classify.c = 1 then [ encodeword.[ c]]else""

Function standalonechars seq.word @(+, ttt,"", arithseq(127, 1, 0))

function t520 boolean 
 let s = message.process.subtest520.merge."45t6.3"
  subseq(s, 1, length.s - 1)="unexpected character in real literal"

function subtest520(t:word)int 
 let x = reallit.decode.merge."45t6.3"
  intpart.x

Function t521 boolean {"The umber ant ambles the opal nurse"= getphrase.20 }

____________

graphs

Function n1 int 1

Function n2 int 2

Function n3 int 3

Function n4 int 4

Function n5 int 5

Function n6 int 6

Function n7 int 7

Function n8 int 8

function t522 boolean 
 let g = newgraph.[ arc(n1, n2), arc(n3, n2), arc(n2, n4), arc(n1, n4), arc(n5, n6), arc(n6, n7), arc(n7, n5), arc(n6, n8), arc(n5, n1)]
  let r = print.g +"transversal"+ print.sinksfirst.g +"Suc"+ print.toseq.successors(g, n2)+"sinks"+ print.sinks(g, asset.[ n4], n2)
  r ="GRAPH:(1 2)(1 4)(2 4)(3 2)(5 1)(5 6)(6 7)(6 8)(7 5)transversal [ 4, 8, 2, 1, 3]Suc [ 4]sinks [ 2]"

function t523 boolean 
 let g = newgraph.[ arc(n1, n2), arc(n3, n2), arc(n2, n4)]
  let closure = [ arc(n1, n2), arc(n1, n4), arc(n2, n4), arc(n3, n2), arc(n3, n4)]
  closure = toseq.arcs.transitiveClosure.g

function print(g:graph.int)seq.word {"GRAPH:"+ @(+, print,"", toseq.arcs.g)}

function print(a:arc.int)seq.word {"("+ toword.tail.a + toword.head.a +")"}

