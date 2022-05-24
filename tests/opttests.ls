uses=stdlib exports=opttests 
Library=opttests

Module COMPILETIME

use standard

use bits

use real

Export  /or(bits,bits)bits

Export  /and(bits,bits)bits

Export  >>(bits,int)bits

Export  <<(bits,int)bits

Export  +(int,int)int

Export  >(int,int)boolean

Export  =(int,int)boolean

Export  -(int,int)int

Export  -(real,real) real

Export  =(boolean,boolean) boolean

Export  *(int,int)int

Export  /(int,int)int


Module opttests 

use standard

use bits

use real


Function optest1 int 3 + 4

Function optest2 int 3 * 4

Function optest3 int if true then 1 else 2

Function optest4 int if false then 1 else 2

Function optest5 word"FIRST"_1

Function optest6 word merge."A B"

Function optest7 seq.word"A" + "B"

Function optest8 int [ 1, 2, 3 + 4]_3

Function optest9 int let a = 5
let c = 6
 a + c

Function optest10 int 12 / 5

Function optest11 int 5 - 4

Function optest12 boolean true = false

Function optest13 real 6.0 - 5.0

Function optest14 bits bits.11 << 2

Function optest15 bits bits.11 >> 2

Function optest16 int(optest16a.[ char.45, char.46])_2

Function optest17 char(decodeword."HJK"_1)_1

Function optest18 bits bits.10 ∨ bits.19

Function optest19 bits bits.10 ∧ bits.19

Function optest20 int parabits.3

Function optest21 char char1."AJK"

Function optest22 boolean"A"_1 = encodeword.[ char.65]

Function optest23 int optest23a(6, 3)

function parabits(nopara:int)int
let b = nopara
 toint(bits.if b > 6 then 0 else b + 1 /if << 5)

Function optest23a(a:int, b:int)int(a + a) / b

Function optest24(i:int)int if i ∈ [ 5]then 24 else 0

Function optest25(i:int)int if 5 ∈ [ 3,5]then 25 else 0

Function optest26(i:word)int if i ∈  " a b c" then 26 else 0


Function optest27(a:int, result:int)int
 { tail recursion } if a = 1 then result else optest27(a - 1, a * result)

Function optest28(a:int, b:int)boolean a > 0 ∧ b < 10

Function optest29(a:int, b:int)boolean a > 0 ∨ b < 10

Function optest30(w:word, a:int, b:int)int if w ∈ "test"then a else b

Function optest31(i:int)int if first."a" ∈ " b c " then 0 else 31

Function optest32(t:seq.word)seq.word dropparameter(t,"")

function dropparameter(a:seq.word, result:seq.word)seq.word a

Function optest33 int { does IDX work } length.[ 3, 4, 5, 6] + 29

Function optest34(s:seq.int, i:int)int
 if s_i ∈ [ 1,9,5,2,12, 3] ∨ s_i = 4 then 10 else 11

Function optest35(s:seq.word, i:int)int
 if s_i ∈ "  e d c b a "  ∨ s_i = first."x" then 10 else 11


Function optest36(b:seq.int)int
 if b_3 = 3333 ∨ b_3 ∈ [ 5, 7, 8, 9] ∨ b_3 = 10 then
  25
 else 2

Function optest37(s:seq.word, i:int)int
 if s_i = "xxx"_1 then 3
 else if s_i ∈ "a b"then 4
 else if s_i ∈ "c d z"then 4 else 5


Function optest38(a:int, b:int, c:int, d:int)ordering optest38a(a ? b, c ? d)

Function optest38a(a:ordering, b:ordering)ordering let x = a
 if x = EQ then b else x

Function optest16a(a:seq.char)seq.int
 { This is just a type change and the compiler recognizes this and does not generate code }
 for acc = empty:seq.int, @e /in a do acc + toint.@e /for(acc)