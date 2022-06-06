Module testprocess

use UTF8

use bits

use checking

use real

use standard

use process.boolean

use otherseq.int

use process.int

use process.real

use process.returntype

use process.seq.word

type returntype is a:int, b:int, c:seq.word

function testprocess3 returntype returntype(4, 40, "a test")

function isprefix(prefix:seq.word, s:seq.word)boolean subseq(s, 1, length.prefix) = prefix

function testout(i:int)seq.word["one two three"_i]

function square(a:real)real a * a

function square(a:int)real toreal.a * toreal.a

function /(a:real, b:int)real a / toreal.b

function redgreen seq.word"red green"

function arg4(a:int, b:int, c:int, d:int)int a + b + c + d

Function testreal seq.word
check([print(3, sqrt.2.0) = "1.414"
, print(2, toreal.3) = "3.00"
, intpart.3.1 = 3
, print(3, 2.0 / 3.0) = "0.667"
, 2.0 + 3.0 = 5.0
, 2.0 * 3.0 = 6.0
, print(5, 2.3 - 1.1) = "1.20000"
, print(5, cos.0.4) = "0.92106"
, print(5, sin.0.4) = "0.38942"
, (1.0 ? 2.0) = LT
, (-1.9 ? -3.0) = GT
, (3.00 ? 3.000) = EQ
, print(5, tan(pi / 4.0)) = "1.00000"
, print(5, arcsin.sin.0.5) = "0.50000"
, print(5, arccos.cos.0.5) = "0.50000"
, print(3, for acc = 0.0, @e ∈[8, 9, 10, 11]do acc + toreal.@e /for(acc))
= "38.000"
, "23.45000-18.45000" = print(5, 23.45) + print(5, 5.0 - 23.45)
, -2^4 = -16
, alphasort."function segment s seq int i seq word addcomma toword merge C 1 toword"
= "1 C addcomma function i int merge s segment seq seq toword toword word"
, for acc = ""
, @e ∈ alphasort.["z b", "a b", "a a", "test 23", "test 20"]
do acc + @e + "/"/for(acc >> 1)
= "a a / a b / test 20 / test 23 / z b"
]
, "real"
)

Function testprocess seq.word
let z = subseq("f red green", 2, 3)
let y = 
 [not.isprefix("out of bounds", "out")
 , isprefix("not an index", message.process.testout.0)
 , isprefix("not an index", message.process.testout.-10)
 , isprefix("out of bounds", message.process.testout.4)
 , isprefix("invalid digit", message.process.toint."0A"_1)
 , message.process.testout.1 = "normal exit"
 , aborted.process.testout.5
 , not.aborted.process.testout.2
 , result.process.square.3.0 = 9.0
 , {10}result.process.pi = pi
 , result.process.intpart.3.1 = 3
 , result.process.square.4 = 16.0
 , result.process.print(3, 3.0) = "3.000"
 , result.process(3 * 4.0) = 12.0
 , result.process(12.0 / 3) = 4.0
 , result.process.testout.3 = "three"
 , result.process.isprefix("red", z)
 , result.process.redgreen = redgreen
 , result.process.arg4(1, 2, 3, 4) = 10
 , {20}message.process.result.process.testout.4 = "no result of aborted process"
 , isprefix("unexpected character in real literal", message.process.makereal."45t6.3")
 , a.result.process.testprocess3 = 4 ∧ b.result.process.testprocess3 = 40
 , t513
 , t514
 ]
check(y, "testprocess")

_________

Primes

function t513 boolean"3 5 7 11 13 17 19 23 29 31 37" = findprimes(3, 40)

function t514 boolean
let c = 10000
let a = process.countprimes(3, c)
let b = process.countprimes(c + 1, 2 * c)
[1228, 1033] = [result.a, result.b]

function findprimes(start:int, finish:int)seq.word
for acc = "", @e ∈ arithseq((finish - start + 2) / 2, 2, start)do if isprime.@e then acc + toword.@e else acc /for(acc)

function countprimes(start:int, finish:int)int
for acc = 0, @e ∈ arithseq((finish - start + 2) / 2, 2, start)do if isprime.@e then acc + 1 else acc /for(acc)

function isprime(i:int)boolean
if i mod 2 = 0 then i = 2
else
 let a = i / 2
 {intpart.sqrt.toreal.i}
 let b = (a + i / a) / 2
 for acc = true, f ∈ arithseq(a, 2, 3)while acc ∧ f ≤ b do i mod f ≠ 0 /for(acc)

_________________

Function randomtest(samplesize:int)seq.word
let r = 
 sort.for acc = empty:seq.int, i ∈ randomint.samplesize do
  for acc2 = acc, j ∈ arithseq(16, 4, 0)do acc2 + (toint(tobits.i >> j ∧ 0xF) + 4 * j)/for(acc2)
 /for(acc)
for acc = empty:seq.int, last = -1, count = -1, sum = 0, t ∈ r do
 if last ≠ t ∧ count > 0 then next(acc + count * 256, t, 1, sum + count)
 else next(acc, t, count + 1, sum)
/for(let mean = toreal.sum / 256.0
for sqs = 0.0, x ∈ acc do
 let cnt = toreal(x / 256)
 sqs + (cnt - mean)^2
/for(let stddev = sqrt(sqs / 256.0)
if mean / stddev > 5.4 then"PASS"else"FAIL"/if
+ print(3, toreal.samplesize * 16.0 / 256.0)
+ "mean"
+ print(3, mean)
+ "std dev"
+ print(3, stddev))) 