#!/usr/local/bin/tau

run test11 test11

Module test11

use otherseq.int

use point.int

use seq.boolean

use seq.int

use otherseq.int


use seq.ordering

use otherseq.word

use stdlib

use textio



function t001 boolean 0 - 4 = 1 - 2 - 3

function t002 boolean 2 = 24 / 4 / 3

function fact(a:int)int if a = 1 then 1 else a * fact.(a - 1)

function t003 boolean 24 = fact.4

function power(a:int, b:int)int
 if b = 1 then a
 else power(a, b / 2) * power(a, b - b / 2)

function t004 boolean 1024 = power(2, 10)

function t005 boolean 45 = if 2 = 2 then 45 else 23

function t006 boolean 34 = if(6 ? 2) = GT then 34 else 16 + 4

test cat of sequences

function t007 boolean [ 2, 3] = [ 2] + [ 3]

function ff(seed:int, x:int)int if x = 1 then pseudorandom.seed else ff(pseudorandom.seed, x - 1)

function t008 boolean // testing random number generator // 1043618065 = ff(1, 10000)

function gen(n:int)seq.int
 if n = 1 then [ n]else gen.(n - 1) + [ n * n]

function t009 boolean [ 1, 4, 9, 16, 25] = gen.5

function genb(n:int)seq.int
 if n = 1 then [ 5]
 else genb.(n - 1) + genb.(n - 1) + [ n]

function t010 boolean [ 5, 5, 2, 5, 5, 2, 3, 5, 5, 2, 5, 5, 2, 3, 4] = genb.4

covert integer to sequence of digits

function int2seq(n:int, b:int)seq.int
 if(n ? b) = LT then [ n]
 else int2seq(n / b, b) + [ n - n / b * b]

function t011 boolean [ 2, 3, 9, 5] = int2seq(2395, 10)

function t012 boolean [ GT, GT, LT]
= [ [ 2, 8] ? [ 2, 7], [ 3, 8] ? [ 2, 8], [ 1, 8] ? [ 2, 8]]

function t013 boolean EQ = ([ 2, 8, 1] ? [ 2, 8, 1])

function t014 boolean [ LT, GT] = [ [ 2, 8] ? [ 2, 8, 1], [ 2, 8, 1] ? [ 2, 8]]

function t015 boolean [ true, false, false, false] = [ true ∧ true, true ∧ false, false ∧ true, false ∧ false]

function t016 boolean [ true, true, true, false] = [ true ∨ true, true ∨ false, false ∨ true, false ∨ false]

test on in

function t017 boolean [ true, true, false]
= [ 2 in [ 1, 2, 3], 3 in [ 1, 2, 3], 5 in [ 1, 2, 3]]

test of + using functional notation pretty printer messes up this example this should be 3 = +(1, 2).

function t018 boolean 3 = 1 + 2

function t019 boolean 1 = findindex(3, [ 3])

function t020 boolean 5 = findindex(1, [ 2, 4, 3, 8, 1, 3] + constantseq(4, 1))

function t021 boolean 28 = constantseq(13, 5)_7 + length.constantseq(23, 3)

/ function t022 boolean [ 3, 6]= all(3, [ 2, 4, 3, 8, 1, 3])

function t022 boolean [ toword.384] + toword.52 = "384 52"

function t023 boolean 9 = (0 - 21) mod 15

 function t024 boolean point(3, 4, 5) = point(3, 4, 5)

 function t025 boolean false = (point(3, 4, 1) = point(3, 4, 5))

 function t026 boolean false = (point(3, 7, 5) = point(3, 4, 5))

 function t027 boolean point(10, 6, 3) = point(8, 3, 2) + point(2, 3, 1)

 function t028 boolean point(6, 0, 1) = point(8, 3, 2) - point(2, 3, 1)

 function t029 boolean 6 = x.point(6, 0, 1)

function t030 boolean [ false, false, true, true] = [ isbyte.(0 - 1), isbyte.256, isbyte.255, isbyte.0]

function isbyte(i:int)boolean between(i, 0, 255)

function t031 boolean false = @(∧, isbyte, true, [ 0 - 1, 256, 255, 0])

function t032 boolean @(∧, isbyte, true, [ 23, 4, 5, 255, 7, 2, 255])

function t033 boolean 6 = (toint.if true then"3"_1 else"5"_1) + 3

function t034 boolean 3464 = (3456 + if true then 3 else 1) + 5

function print(a:seq.int)seq.word"[" + @(seperator(","), toword,"", a) + "]"

function t035 boolean"[ 2, 3, 4, 5]" = print.[ 2, 3, 4, 5]

function t036 boolean 10 = @(+, *(1), 0, [ 1, 2, 3, 4])

function t037 boolean 24 = @(*, *(1), 1, [ 1, 2, 3, 4])

function t038 boolean [ 1, 2, 3, 4] = @(+, +(empty:seq.int), empty:seq.int, [ 1, 2, 3, 4])

function t039 boolean
let a = 6 * 6
 a + a = 72

function t040 boolean"a b c d e 1 2 3 4 k"
= replace("a b c d e" + "1 2 3 4 5", 10,"k"_1)

function t041 boolean"1 2 k 4 5" = replace("1 2 3 4 5", 3,"k"_1)

function t042 boolean @(-, identity, 100, [ 1, 2]) = 97

function showcodes(i:int)seq.word [ toword.i, encodeword.[ char.i]]

Function t043 boolean"code glyph 48 0 49 1 50 2 51 3 52 4 53 5 54 6 55 7 56 8 57 9 58:59 ; 60 < 61 = 62 > 63 ? 64 @ 65 A 66 B 67 C 68 D 69 E 70 F 71 G 72 H 73 I 74 J 75 K 76 L 77 M 78 N 79 O 80 P 81 Q 82 R 83 S 84 T 85 U 86 V 87 W 88 X 89 Y 90 Z"
= @(+, showcodes,"code glyph", arithseq(43, 1, 48))


function t045 boolean '"()+,-.:= []^_' = standalonechars

function ttt(c:int)seq.word
 let class = classifychar_c
  if class in "0 SPACE"then""else [ class]

Function standalonechars seq.word @(+, ttt,"", arithseq(length.classifychar, 1, 1))

Function t046 boolean // testing UNICODE to word conversion and no-break space in integer 8746 // decodeword."1 2∪"_1
= [ char.49, char.160, char.50, char.87 46]

function testset set.int asset.[ 2, 5, 6, 9, 12, 15, 35, 36]

function ?2(a:int, b:int)ordering a / 10 ? b / 10

function print(a:set.int)seq.word @(+, toword,"", toseq.a)

function t047 boolean toseq.findelement2(testset, 36) = [ 35, 36] ∧ toseq.findelement2(testset, 15) = [ 12, 15]



use checking

use set.int

use seq.int

Function test11 seq.word
let y = [ t001, t002, t003, t004, t005, t006, t007, t008, t009, t010
, t011, t012, t013, t014, t015, t016, t017, t018, t019, t020
, t021, t022, t023, t024, t025, t026, t027, t028, t029, t030
, t031, t032, t033, t034, t035, t036, t037, t038, t039, t040
, t041, t042, t043, t045, t046, t047]  
 check(y,"test11")