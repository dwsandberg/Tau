Module opttests

use standard

use bits

use real

use UTF8

use otherseq.word

Function optest1 int 3 + 4

Function optest2 int 3 * 4

Function optest3 int if true then 1 else 2

Function optest4 int if false then 1 else 2

Function optest5 word 1_"FIRST"

Function optest6 word merge."A B"

Function optest7 seq.word "A B"

Function optest8 int 3_[1, 2, 3 + 4]

Function optest9 int let a = 5 let c = 6, a + c

Function optest10 int 12 / 5

Function optest11 int 5 - 4

Function optest12 boolean true = false

Function optest13 real 6.0 - 5.0

Function optest14 bits bits.11 << 2

Function optest15 bits bits.11 >> 2

Function optest16(a:seq.char) seq.int
{This is just a type change and the compiler recognizes this and does not generate code}
for acc = empty:seq.int, @e ∈ a do acc + toint.@e,
acc

Function optest17 char 1_decodeword.1_"HJK"

Function optest18 bits bits.10 ∨ bits.19

Function optest19 bits bits.10 ∧ bits.19

Function optest20 int parabits.3

Function optest21 char char1."AJK"

Function optest22 boolean 1_"A" = encodeword.[char.65]

Function optest23 int optest23a(6, 3)

function parabits(nopara:int) int
let b = nopara,
toint((bits.if b > 6 then 0 else b + 1) << 5)

Function optest23a(a:int, b:int) int (a + a) / b

Function optest24(i:int) int if i ∈ [5] then 24 else 0

Function optest25(i:int) int if 5 ∈ [3, 5] then 25 else 0

Function optest27(a:int, result:int) int
{tail recursion}
if a = 1 then result else optest27(a - 1, a * result)

Function optest26(b:seq.int) int
{remove is member}
let t = 3_b,
if t = 3333 ∨ t ∈ [5, 7, 8, 9] ∨ t = 10 then 25 else 2

Function optest28(a:int, b:int) boolean a > 0 ∧ b < 10

Function optest29(a:int, b:int) boolean a > 0 ∨ b < 10

Function optest30(w:word, a:int, b:int) int if w ∈ "test" then a else b

Function optest31(i:int) int if 1_"a" ∈ "b c" then 0 else 31

Function optest32(t:seq.word) seq.word dropparameter(t, "")

function dropparameter(a:seq.word, result:seq.word) seq.word a

Function optest33 int {does IDX work} n.[3, 4, 5, 6] + 29

Function optest34(s:seq.int, i:int) int
let t = i_s,
if t ∈ [1, 9, 5, 2, 12, 3] ∨ t = 4 then 10 else 11

Function optest35(s:seq.word, i:int) int
if i_s ∈ "e d c b a" ∨ i_s = 1_"x" then 10 else 11

Function optest36(i:word) int if i ∈ "a b c" then 26 else 0

Function optest37(s:seq.word, i:int) int
if i_s = 1_"xxx" then
3
else if i_s ∈ "a b" then
4
else if i_s ∈ "c d z" then
4
else 5

Function optest38(a:int, b:int, c:int, d:int) ordering
{what is this test for?}
optest38a(a >1 b, c >1 d)

Function optest38a(a:ordering, b:ordering) ordering let x = a, if x = EQ then b else x

Function optest39 int 2_optest16.[char.45, char.46]

Function optest40 seq.word for a = "", w ∈ "this for loop should be a noop" do a + w, a

Function optest41 seq.int
{detection of noop with constant sequence}
for a = empty:seq.int, w ∈ [2, 3, 4] do a + w,
a

Function optest42(i:int) int
{Move br2 together for detection of jump instruction}
if i = 1 then 10 else if i = 3 then 30 else if i = 7 then 70 else 0

Function optest43(i:int, b:int) int
{branch into middle of possible jump list. Must break into to Jumps}
if i = 4 ∧ b = 10 then
 if i = -3 then
 30
 else if i = -4 then
 40
 else if i = -5 then
 50
 else if i = -10 then
 50
 else if i = -12 then
 60
 else 100
else if i = 7 then
70
else if i = 2 then
20
else if i = 5 then
30
else if i = 1 then
10
else if i = -3 then
30
else if i = -4 then
40
else if i = -5 then
50
else if i = -10 then
50
else if i = -12 then
60
else 100

Function optest44(i:int, b:int) int
{Variant of optest43 with last Br2 being default case}
if i = 4 ∧ b = 10 then
 if i = -3 then
 30
 else if i = -4 then
 40
 else if i = -5 then
 50
 else if i = -10 then
 50
 else if i = -12 then
 60
 else if b = 5 then
 200
 else 100
else if i = 7 then
70
else if i = 2 then
20
else if i = 5 then
30
else if i = 1 then
10
else if i = -3 then
30
else if i = -4 then
40
else if i = -5 then
50
else if i = -10 then
50
else if i = -12 then
60
else if b = 5 then
200
else 100

Function optest45(a:seq.int) int
{" 64 = (int, int) boolean" and" Br2" are in different tree nodes in basicBlockTree after pass2}
for current = 0, shift = 0, b ∈ a do if shift = 64 then next(current, 8) else next(current, 9),
3

Function optest46(i:int) int
{remove of unused branches}
if true then if false then 1 else 2 else 3

Function optest47(a:int, b:int, result:int) int
{recursion}
let e = if b = 0 then "C" else "B"
let d = a + b,
if b = 0 then result else optest47(a, b - 1, result * a)

Function optest48(a:seq.word) seq.word
{reverse is combined in loop}
for acc = "", w ∈ reverse.a do acc + w,
acc

use seq.word

Function optest49 word
let s = "a test"
let i = 2
assert i > 0 ∧ i ≤ n.s ∨ getseqtype.s > 1 report "out of bounds",
idxNB(s, i) 