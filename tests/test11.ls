Module test11

use seq.boolean

use checking

use otherseq.int

use set.int

use testPoint.int

use seq.ordering

use standard

use textio

use otherseq.word

function t001 boolean 0 - 4 = 1 - 2 - 3

function t002 boolean 2 = 24 / 4 / 3

function fact(a:int) int if a = 0 then 1 else if a = 1 then 1 else a * fact(a - 1)

function t003 boolean 24 = fact.4

function power(a:int, b:int) int
if b = 0 then 1 else if b = 1 then a else power(a, b / 2) * power(a, b - b / 2)

function t004 boolean 1024 = power(2, 10)

function t005 boolean 45 = if 2 = 2 then 45 else 23

function t006 boolean 34 = if 6 >1 2 = GT then 34 else 16 + 4

test cat of sequences

function t007 boolean [2, 3] = [2] + [3]

function ff(seed:int, x:int) int
if x = 1 then pseudorandom.seed else ff(pseudorandom.seed, x - 1)

function t008 boolean {testing random number generator} 1043618065 = ff(1, 10000)

function gen(n:int) seq.int if n = 1 then [n] else gen(n - 1) + [n * n]

function t009 boolean [1, 4, 9, 16, 25] = gen.5

function genb(n:int) seq.int
if n = 1 then [5] else genb(n - 1) + genb(n - 1) + [n]

function t010 boolean [5, 5, 2, 5, 5, 2, 3, 5, 5, 2, 5, 5, 2, 3, 4] = genb.4

covert integer to sequence of digits

function int2seq(n:int, b:int) seq.int
if n >1 b = LT then [n] else int2seq(n / b, b) + [n - n / b * b]

function t011 boolean [2, 3, 9, 5] = int2seq(2395, 10)

function t012 boolean
[GT, GT, LT] = [[2, 8] >1 [2, 7], [3, 8] >1 [2, 8], [1, 8] >1 [2, 8]]

function t013 boolean EQ = ([2, 8, 1] >1 [2, 8, 1])

function t014 boolean [LT, GT] = [[2, 8] >1 [2, 8, 1], [2, 8, 1] >1 [2, 8]]

function t015 boolean
[true, false, false, false]
 = [true ∧ true, true ∧ false, false ∧ true, false ∧ false]

function t016 boolean
[true, true, true, false] = [true ∨ true, true ∨ false, false ∨ true, false ∨ false]

test on in

function t017 boolean
[true, true, false] = [2 ∈ [1, 2, 3], 3 ∈ [1, 2, 3], 5 ∈ [1, 2, 3]]

test of+using functional notation pretty printer messes up this example this should be 3 =+(1, 2
).

function t018 boolean 3 = 1 + 2

function t019 boolean 1 = findindex([3], 3)

function t020 boolean 5 = findindex([2, 4, 3, 8, 1, 3] + constantseq(4, 1), 1)

function t021 boolean 28 = 7_constantseq(13, 5) + n.constantseq(23, 3)

/ function t022 boolean [3, 6] = all (3, [2, 4, 3, 8, 1, 3])

function t022 boolean [toword.384] + toword.52 = "384 52"

function t023 boolean 9 = (0 - 21) mod 15

function t024 boolean point(3, 4, 5) = point(3, 4, 5)

function t025 boolean false = (point(3, 4, 1) = point(3, 4, 5))

function t026 boolean false = (point(3, 7, 5) = point(3, 4, 5))

function t027 boolean point(10, 6, 3) = point(8, 3, 2) + point(2, 3, 1)

function t028 boolean point(6, 0, 1) = point(8, 3, 2) - point(2, 3, 1)

function t029 boolean 6 = x.point(6, 0, 1)

function t030 boolean
[false, false, true, true] = [isbyte(0 - 1), isbyte.256, isbyte.255, isbyte.0]

function isbyte(i:int) boolean between(i, 0, 255)

function t031 boolean
false = for acc = true, e ∈ [0 - 1, 256, 255, 0] do acc ∧ isbyte.e, acc

function t032 boolean for acc = true, e ∈ [23, 4, 5, 255, 7, 2, 255] do acc ∨ isbyte.e, acc

function t033 boolean 6 = (toint.if true then 1_"3" else 1_"5") + 3

function t034 boolean 3464 = 3456 + (if true then 3 else 1) + 5

function print(a:seq.int) seq.word "[^(%(",", a) >> 1)]"

function t035 boolean "[2, 3, 4, 5]" = print.[2, 3, 4, 5]

function t036 boolean 10 = for acc = 0, e ∈ [1, 2, 3, 4] do acc + e, acc

function t037 boolean 24 = for acc = 1, e ∈ [1, 2, 3, 4] do acc * e, acc

Function t038 boolean
[1, 2, 3, 4] = for acc = empty:seq.int, e ∈ [1, 2, 3, 4] do acc + e, acc

function t039 boolean let a = 6 * 6, a + a = 72

function t040 boolean "a b c d e 1 2 3 4 k" = replace("a b c d e 1 2 3 4 5", 10, 1_"k")

function t041 boolean "1 2 k 4 5" = replace("1 2 3 4 5", 3, 1_"k")

function t042 boolean 97 = for acc = 100, e ∈ [1, 2] do acc - e, acc

function t043 boolean
"code glyph 48 0 49 1 50 2 51 3 52 4 53 5 54 6 55 7 56 8 57 9 58:59 ; 60 < 61 = 62 >"
 + "63 ? 64 @ 65 A 66 B 67 C 68 D 69 E 70 F 71 G 72 H 73 I 74 J 75 K 76 L 77 M 78 N 79 O"
 + "80 P 81 Q 82 R 83 S 84 T 85 U 86 V 87 W 88 X 89 Y 90 Z"
 = 
 for acc = "code glyph", e ∈ arithseq(43, 1, 48) do acc + [toword.e, encodeword.[char.e]],
 acc

function t044 boolean "^(dq) ()+,-.. :: = []^_{}" = standalonechars

use bits

use seq.byte

function standalonechars seq.word
for acc0 = [tobyte.70], i ∈ arithseq(127 - 32, 1, 33)
do acc0 + tobyte.i + tobyte.70 + tobyte.i + tobyte.32 + tobyte.70
for acc1 = "F", w ∈ 1_breakparagraph.acc0
do if w ∈ "F" ∨ n.decodeword.w > 2 ∨ w = 1^acc1 then acc1 else acc1 + w,
acc1 << 1

function t045 boolean
{testing UNICODE to word conversion and no-break space in integer 8746}
decodeword.1_"1 2∪" = [char.49, char.160, char.50, char.87 46]

function testset set.int asset.[2, 5, 6, 9, 12, 15, 35, 36]

function >2(a:int, b:int) ordering a / 10 >1 b / 10

function t046 boolean
toseq.findelement2(testset, 36) = [35, 36]
 ∧ toseq.findelement2(testset, 15) = [12, 15]

type Tpair is a:int, b:seq.word

Function test11 seq.word
let list = [
 t001
 , t002
 , t003
 , t004
 , t005
 , t006
 , t007
 , t008
 , t009
 , t010
 , t011
 , t012
 , t013
 , t014
 , t015
 , t016
 , t017
 , t018
 , t019
 , t020
 , t021
 , t022
 , t023
 , t024
 , t025
 , t026
 , t027
 , t028
 , t029
 , t030
 , t031
 , t032
 , t033
 , t034
 , t035
 , t036
 , t037
 , t038
 , t039
 , t040
 , t041
 , t042
 , t043
 , t044
 , t045
 , t046
 , a.Tpair(3, "three") = 3
 , "this is a test" << 2 = "a test"
 , "this is a test" >> 3 = "this"
 , t050
 , t051
 , t052
 , t053
 , t054
],
check(list, "test11")

function t050 boolean
{nested for with same signature for next}
for acc1 = 0, t = 5, j ∈ [1, 2, 3]
do next(for acc2 = acc1, u = 6, i ∈ [4, 5] do next(acc2 + 1, 5), acc2, 6),
acc1 = 6

function t051 boolean
{next with single accumulator}
for acc = "", w ∈ "f g" do next(acc + w),
acc = "f g"

function t052 boolean {constant empty sequence} for acc = "d", w ∈ "" do acc + w, acc = "d"

function t053 boolean
{using multiple accumulators from inner loop in outer loop}
for outer1 = 0, outer2 = 1, i ∈ [1, 2, 3, 4]
do
 for inner1 = 1, inner2 = 2, w ∈ "X Y" do next(inner1, inner2),
 next(outer1 + i, outer2 * i * (inner2 - inner1)),
%.outer1 + %.outer2 = "10 24"

function t054 boolean
{reusing element}
for sum = 0, element ∈ [1, 2, 3, 4] do sum + element
for product = 1, element ∈ [1, 2, 3, 4] do product * element,
[sum, product] = [10, 24] 