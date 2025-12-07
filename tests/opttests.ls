Module opttests

precedence > for >1 >2

use UTF8

use bits

use real

use standard

use seq1.word

use seq.word

use symbol1

use seq.mytype

Function optest1 int 3 + 4

Function optest2 int 3 * 4

Function optest3 int if true then 1 else 2

Function optest4 int if false then 1 else 2

Function optest5 word  "FIRST" sub 1

Function optest6 word merge."A B"

Function optest7 seq.word "A B"

Function optest8 int [1, 2, 3 + 4] sub 3

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

Function optest17 char  (decodeword.("HJK" sub 1)) sub 1

Function optest18 bits bits.10 ∨ bits.19

Function optest19 bits bits.10 ∧ bits.19

Function optest20 int parabits.3

Function optest21 char char1."AJK"  

Function optest22 boolean  "A" sub 1 = encodeword.[char.65]

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
let t =  b sub 3,
if t = 4 ∨ t ∈ [5, 7, 8, 9] ∨ t = 3333 then 25 else 20 

Function optest28(a:int, b:int) boolean a > 0 ∧ b < 10

Function optest29(a:int, b:int) boolean a > 0 ∨ b < 10

Function optest30(w:word, a:int, b:int) int if w ∈ "test" then a else b

Function optest31(i:int) int if "a" sub 1 ∈ "b c" then 0 else 31

Function optest32(t:seq.word) seq.word dropparameter(t, "")

function dropparameter(a:seq.word, result:seq.word) seq.word a

Function optest33 int {does IDX work} n.[3, 4, 5, 6] + 29

Function optest34(s:seq.int, i:int) int
let t = s sub i ,
if t ∈ [1, 9, 5, 2, 12, 3] ∨ t = 4 then 10 else 11

Function optest35(s:seq.word, i:int) int
if  s sub i ∈ "e d c b a" ∨  s sub i =  "x" sub 1 then 10 else 11

Function optest36(i:word) int 
if i ∈ "" then 27
else if i ∈ "a b c" then 26 else 0

Function optest37(s:seq.word, i:int) int
if s sub i  =  "xxx"sub 1 then
3
else if  s sub i ∈ "a b" then
4
else if  s sub i ∈ "c d z" then
4
else 5

Function optest38(a:int, b:int, c:int, d:int) ordering
{what is this test for?}
optest38a(a >1 b, c >1 d)

Function optest38a(a:ordering, b:ordering) ordering let x = a, if x = EQ then b else x

Function optest39 int  (optest16.[char.45, char.46]) sub 2

Function optest40 seq.word for a = "", w ∈ "this for loop should be a noop" do a + w, a

Function optest41 boolean
{detection of noop with constant sequence}
for a = empty:seq.int, w ∈ [2, 3, 4] do a + w,
a sub 1 =2 ∧   a sub 2=3 ∧  a sub 3=4

Function optest42(i:int) int
{Move br2 together for detection of jump instruction}
if i = 1 then 10 else if i = 3 then 30 else if i = 7 then 70 else 0

Function optest43(i:int, b:int) int
{branch into middle of possible jump list. Must break into two Jumps}
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

Function optest49 word
let s = "a test"
let i = 2
assert i > 0 ∧ i ≤ n.s ∨ getseqtype.s > 1 report "out of bounds",
idxNB(s, i)

Function optest50(i:int, b:int) int
if   i+3 =9 then 90
else if i=7 then 70
else if i=3 then 30
else if i=1 then 20
else if i=0 then 0
else 55



Function optest51(partno:int) seq.word
if partno = 2 then ""
else if partno ∈ [8, 9] then "R"
else if partno = 10 then if partno = 1 then "~ENTRY" else ""
else if partno ∈ [11, 14, 16] then ""
else if partno = 15 then "R"
else "R"

use seq.char

Function optest52(b:char) int
{???? not finding =(char,char) boolean }
if  b ∈ [char(40),char(41),char.42,char.43] then 33
else 34

Function optest53  boolean
Exit=symbol(moduleref."* real", "makereal", [seqof.typeword], typereal)


Function optest54 int 
{testing compile time evaluation}
 let b= 3 * 2 / 0
 if 5 > 3 then
  2 + toint( 0x5 ∧  0xFF ∨ 0x10 << 3 >> 4 ∧  mask(5)  )-1
  else 0

use seq.boolean

Function optest55 boolean
 { c1 will be record constant and c2 will be sequence constant
   but sill could be equal }
  let c1=arithseq(2,3,0)
  let c2=[0,3]
  let c3=[4-4,3]
  let c4 =[3,3]
  let z=[c2=c3,c2 ≠ c4 ,c1 =c2 , c1 ≠ c4]
     z=[true,true,true,true]  
     
Function optest56(i:int,a:int) int
       if i=9 then 2 else
       if i =3 ∧ a=5 then 6
       else if i ∈ [6,7,8] then 10
       else 7

     i ∈ [2,4,5] ∨ (i ∈ [9,6,7]) ∨ i=10
     




/Function optest50(i:int, b:int) int
{Check to see that duplicate labels are not included in Jump because LLVM requires no duplicates in
Switch instruction. }
if i = 5555 then
80
else if i = 7 then
70
else if i = 2 then
20
else if i = 5555 then
30
else if i = 1 then
60
else if i = 5555 then
200
else 100 