
Module testopt

use UTF8

use bits

use main2

use real

use standard

use textio

use seq.char

use seq.int

use set.word

use otherseq.seq.word

use seq.seq.word

Function testopt seq.word let p2 = secondPass."stdlib.testoptconfig"
let cl = ["7","12","1","2","WORD FIRST","WORD AB", '"A B"',"7","11","2"
,"1","false()standard","4607182418800017408","44","2","46","72","27","2","128"
,"65","true()standard","4", { optest24 }
"Start(int)
/br %1 5 =(int, int)standard Br2(1, 2)
/br 24 Exit 
/br 0 Exit 
/br EndBlock 
/br","25", { optest26 }
"Start(int) 
/br %1 WORD a =(int, int)standard Br2(3, 1) 
/br %1 WORD b =(int, int)standard Br2(2, 1) 
/br %1 WORD c =(int, int)standard Br2(1, 2) 
/br 26 Exit 
/br 0 Exit 
/br EndBlock 
/br","%1 %2 LOOPBLOCK:3(int, int)$loopblock.int 
/br %3 1 =(int, int)standard Br2(1, 2)
/br %4 Exit 
/br %3 1-(int, int)standard %3 %4 *(int, int)standard CONTINUE 2 
/br EndBlock 
/br",{ optest28 }"Start(boolean)
/br %1 0 >(int, int)standard Br2(1, 2)
/br 10 %2 >(int, int)standard Exit 
/br false()standard Exit 
/br EndBlock 
/br",{ optest29 }"Start(boolean)
/br %1 0 >(int, int)standard Br2(1, 2)
/br true()standard Exit 
/br 10 %2 >(int, int)standard Exit 
/br EndBlock 
/br", { optest30 }
"Start(int)
/br %1 WORD test =(int, int)standard Br2(1, 2)
/br %2 Exit 
/br %3 Exit 
/br EndBlock 
/br"
,  "31"  
,"%1", { test 33 }"33","Start(int) 
 /br %1 %2_(seq.int, int)seq.int DEFINE 3 %3 3 >(int, int)standard Br2(4, 1) 
 /br %3 3 =(int, int)standard Br2(8, 1) 
 /br %3 1 =(int, int)standard Br2(7, 1) 
 /br %3 2 =(int, int)standard Br2(6, 7) 
 /br %3 5 >(int, int)standard Br2(3, 1) 
 /br %3 5 =(int, int)standard Br2(4, 1) 
 /br %3 4 =(int, int)standard Br2(3, 4) 
 /br %3 9 =(int, int)standard Br2(2, 1) 
 /br %3 12 =(int, int)standard Br2(1, 2) 
 /br 10 Exit 
 /br 11 Exit 
 /br EndBlock 
 /br",{test 35} "Start(int) 
/br %1 %2_(seq.word, int)seq.word DEFINE 3 
%3 WORD c >(int, int)standard Br2(4, 1) 
/br %3 WORD c =(int, int)standard Br2(6, 1) 
/br %3 WORD e =(int, int)standard Br2(5, 1) 
/br %3 WORD b =(int, int)standard Br2(4, 5) 
/br %3 WORD a =(int, int)standard Br2(3, 1) 
/br %3 WORD x =(int, int)standard Br2(2, 1) 
/br %3 WORD d =(int, int)standard Br2(1, 2) 
/br 10 Exit 
/br 11 Exit 
/br EndBlock 
/br",{test 36} "Start(int) 
/br %1 3_(seq.int, int)seq.int DEFINE 2 %2 8 >(int, int)standard Br2(4, 1) 
/br %2 8 =(int, int)standard Br2(6, 1) 
/br %2 5 =(int, int)standard Br2(5, 1) 
/br %2 7 =(int, int)standard Br2(4, 5) 
/br %2 9 =(int, int)standard Br2(3, 1) 
/br %2 10 =(int, int)standard Br2(2, 1) 
/br %2 3333 =(int, int)standard Br2(1, 2) 
/br 25 Exit 
/br 2 Exit 
/br EndBlock /br",{test 37} "Start(int) 
/br %1 %2_(seq.word, int)seq.word DEFINE 3 %3 WORD b >(int, int)standard Br2(4, 1) 
/br %3 WORD b =(int, int)standard Br2(7, 1) 
/br %3 WORD z =(int, int)standard Br2(7, 1) 
/br %3 WORD xxx =(int, int)standard Br2(4, 7) 
/br %3 WORD c =(int, int)standard Br2(5, 1) 
/br %3 WORD a =(int, int)standard Br2(3, 1) 
/br %3 WORD d =(int, int)standard Br2(3, 4) 
/br 3 Exit 
/br 4 Exit 
/br 4 Exit 
/br 5 Exit 
/br EndBlock /br"]
let r = for acc ="", @e = arithseq(length.cl, 1, 1)do acc + getcode(p2, cl, @e)/for(acc)
+ if [ 40, 20, 30, 20]
= [ multitarget(4, true, false), multitarget(4, false, false), multitarget(3, false, true), multitarget(2, false, false)]then
 ""
else"fail multitarget"
 if isempty.r then"PASS testopt"else"testopt" + r

function filter(name:word, s:seq.word)seq.word if name = s_1 then s else""

Function getcode(p2:seq.seq.word, codelist:seq.seq.word, no:int)seq.word
let t1 = for acc ="", @e = p2 do acc + filter(merge("optest" + toword.no), @e)/for(acc)
let t = subseq(t1, findindex("testopt"_1, t1) + 1, length.t1)
let code = removeoptions(t, length.t)
 { assert false report t1 +" /br"+ t +" /br"+ code }
 if codelist_no = code ∨ no = 26 ∧ shuffletest.sameto(code, codelist_no, 1,"")then
  ""
 else
  " /br  /< literal FAILED  /> test" + toword.no + "in optest  /br" + code + " /p"
  + codelist_no
  + " /p diffs:"
  + sameto(code, codelist_no, 1,"")
  + " /p"
  + toseq.asset."a b c d xxx"

function shuffletest(s:seq.word)boolean
 s
 ∈ ["17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 d a 85 8 9 92 xxx d 100 10 7 101 9 10 109 4 3 113 5 4 117 3 5","17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 xxx a 85 10 9 100 8 7 101 9 10 109 4 3 113 5 4 117 3 5","47 b xxx 62 xxx b 85 8 9 109 4 3 113 3 4","17 xxx c 32 xxx c 47 b xxx 62 c b 85 8 9 100 9 7 105 3 4 109 4 3"]

function sameto(a:seq.word, b:seq.word, i:int, diffs:seq.word)seq.word
 if i > length.a ∨ i > length.b then diffs
 else if a_i = b_i then sameto(a, b, i + 1, diffs)
 else sameto(a, b, i + 1, diffs + [ toword.i, a_i, b_i])

function removeoptions(s:seq.word, i:int)seq.word
 if i = length.s then
  if subseq(s, i - 8, i) ≠ "option(int, seq.word )internal"then s
  else removeoptions(s, i - 10)
 else if s_i ≠ '"'_1 then removeoptions(s, i - 1)
 else subseq(s, 1, i - 1)

Function multitarget(value1:int, a:boolean, b:boolean)int
 { check to see optimization handles this case correctly }
 if if value1 = 4 then a else false then 40
 else if if value1 = 3 then b else false then 30 else 20

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
 for acc = empty:seq.int, @e = a do acc + toint.@e /for(acc)