Module test11

use oseq.int

use point.int

use seq.boolean

use seq.int

use seq.ordering

use stdlib

Function dummyfunction int 3

function t001 boolean 0-4 = 1-2-3 

function t002 boolean 2 = 24 / 4 / 3

function fact(a:int)int if a = 1 then 1 else a * fact(a - 1)

function t003 boolean 24 = fact.4

function power(a:int, b:int)int 
 if b = 1 then a else power(a, b / 2)* power(a, b - b / 2)

function t004 boolean 1024 = power(2, 10)

function t005 boolean 45 = if 2 = 2 then 45 else 23

function t006 boolean 34 = if 6 ? 2 = GT then 34 else 16 + 4

test cat of sequences

function t007 boolean [ 2, 3]= [ 2]+ [ 3]

function ff(seed:int, x:int)int 
 if x = 1 then pseudorandom.seed else ff(pseudorandom.seed, x - 1)

function t008 boolean 
 // testing random number generator // 1043618065 = ff(1, 10000)

function gen(n:int)seq.int if n = 1 then [ n]else gen(n - 1)+ [ n * n]

function t009 boolean [ 1, 4, 9, 16, 25]= gen.5

function genb(n:int)seq.int 
 if n = 1 then [ 5]else genb(n - 1)+ genb(n - 1)+ [ n]

function t010 boolean [ 5, 5, 2, 5, 5, 2, 3, 5, 5, 2, 5, 5, 2, 3, 4]= genb.4

covert integer to sequence of digits

function int2seq(n:int, b:int)seq.int 
 if n ? b = LT then [ n]else int2seq(n / b, b)+ [ n - n / b * b]

function t011 boolean [ 2, 3, 9, 5]= int2seq(2395, 10)

function t012 boolean [ GT, GT, LT]= [ [ 2, 8]? [ 2, 7], [ 3, 8]? [ 2, 8], [ 1, 8]? [ 2, 8]]

function t013 boolean EQ =([ 2, 8, 1]? [ 2, 8, 1])

function t014 boolean [ LT, GT]= [ [ 2, 8]? [ 2, 8, 1], [ 2, 8, 1]? [ 2, 8]]

function t015 boolean [ true, false, false, false]= [ true ∧ true, true ∧ false, false ∧ true, false ∧ false]

function t016 boolean [ true, true, true, false]= [ true ∨ true, true ∨ false, false ∨ true, false ∨ false]

test on in

function t017 boolean [ true, true, false]= [ 2 in [ 1, 2, 3], 3 in [ 1, 2, 3], 5 in [ 1, 2, 3]]

test of + using functional notation pretty printer messes up this example this should be 3 = +(1, 2).

function t018 boolean 3 = 1 + 2

function t019 boolean 1 = findindex(3, [ 3])

function t020 boolean 5 = findindex(1, [ 2, 4, 3, 8, 1, 3]+ constantseq(4, 1))

function t021 boolean 28 = constantseq(13, 5)_7 + length.constantseq(23, 3)

/ function t022 boolean [ 3, 6]= all(3, [ 2, 4, 3, 8, 1, 3])

function t022 boolean [ toword.384]+ toword.52 ="384 52"

function t023 boolean 9 =(0 - 21)mod 15

Function t024 boolean point(3, 4, 5)= point(3, 4, 5)

Function t025 boolean false =(point(3, 4, 1)= point(3, 4, 5))

Function t026 boolean false =(point(3, 7, 5)= point(3, 4, 5))

Function t027 boolean point(10, 6, 3)= point(8, 3, 2)+ point(2, 3, 1)

Function t028 boolean point(6, 0, 1)= point(8, 3, 2) - point(2, 3, 1)

Function t029 boolean 6 = x.point(6, 0, 1)

Function t030 boolean [ false, false, true, true]= [ isbyte(0 - 1), isbyte.256, isbyte.255, isbyte.0]

function isbyte(i:int)boolean between(i, 0, 255)

Function t031 boolean false = @(∧, isbyte, true, [ 0 - 1, 256, 255, 0])

Function t032 boolean @(∧, isbyte, true, [ 23, 4, 5, 255, 7, 2, 255])

/ / Function t110 boolean [ 23, 4, 5, 255, 7, 2, 255]= byteseq.[ 23, 4, 5, 255, 7, 2, 255]

/ / Function t111 boolean [ 23, 4, 5, 255, 7, 2, 255]= byteseq.[ 23, 4, 5, 255, 7, 2, 255]

Function test11 seq.word 
 let y = [ t002, t003, t004, t005, t006, t007, t008, t009, t010, t011, 
  t012, t013, t014, t015, t016, t017, t018, t019, t020, t021, 
  t022, t023, t024, t025, t026, t027, t028, t029, t030, t031]
  let x = @(+, check.y,"", arithseq(length.y, 1, 1))
  if x =""then"PASS test11"else"FAIL test11"+ x

Function check(l:seq.boolean, i:int)seq.word 
 if l_i then""else [ toword.i]

