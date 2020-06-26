#!/usr/local/bin/tau

Module testopt

run testopt testopt

use bits

use main2

use real

use seq.char

use seq.int

use seq.seq.word

use seq.word

use stdlib

use textio

use otherseq.seq.word

use UTF8

Function testopt seq.word
let p2 = secondPass."testall"_1
let cl = ["7","12","1","2","WORD FIRST","WORD AB",'"A B"',"7","11","2"
,"1","0","4607182418800017408"," 44"," 2"," 46"," 72","27","2","128","65","1","4",
// optest24   // "%1 5 Q3DZbuiltinZintZint 2 2 3 BR 3 
 &br 24 EXITBLOCK 1 
 &br 0 EXITBLOCK 1 
 &br BLOCK 3  &br "  
 ,// optest25 // "
  %1 3 Q5FZintzseqZintzseqZint 2 DEFINE 2 %2 9 Q3EZbuiltinZintZint 2 5 2 BR 3 
&br %2 9 Q3DZbuiltinZintZint 2 7 3 BR 3 
&br %2 5 Q3DZbuiltinZintZint 2 7 4 BR 3 
&br %2 8 Q3DZbuiltinZintZint 2 7 8 BR 3 
&br %2 10 Q3DZbuiltinZintZint 2 7 6 BR 3 
&br %2 3333 Q3DZbuiltinZintZint 2 7 8 BR 3 
&br 25 EXITBLOCK 1 
&br 2 EXITBLOCK 1 
&br BLOCK 8
&br  "
 ,"26"
,"%1 %2  3 LOOPBLOCK  3  
&br %3  1 Q3DZbuiltinZintZint 2 3 4 BR 3 
 &br %4 EXITBLOCK 1 
 &br %3 1 Q2DZbuiltinZintZint 2 %3 %4 Q2AZbuiltinZintZint 2 CONTINUE 2  
 &br BLOCK 4 &br",
"%1  0 Q3EZbuiltinZintZint 2  2  3  BR 3  
&br 10 %2 Q3EZbuiltinZintZint 2   EXITBLOCK 1  
 &br 0  EXITBLOCK 1 
  &br  BLOCK 3 &br",
"%1  0 Q3EZbuiltinZintZint 2  2  3   BR 3  
&br 1  EXITBLOCK 1  
&br 10 %2 Q3EZbuiltinZintZint 2 EXITBLOCK 1  &br BLOCK 3 &br"
, //  optest30 // "%1 WORD test Q3DZbuiltinZintZint 2 2 3 BR 3  
&br %2 EXITBLOCK 1 
&br %3 EXITBLOCK 1 
&br BLOCK 3 &br", // test 31 // "%1 %2 Q5FZintzseqZintzseqZint 2 DEFINE 3 %3 3 Q3EZbuiltinZintZint 2 4 2 BR 3 
&br %3 3 Q3DZbuiltinZintZint 2 5 3 BR 3 
&br %3 1 Q3DZbuiltinZintZint 2 5 6 BR 3 
&br %3 4 Q3DZbuiltinZintZint 2 5 6 BR 3 
&br 10 EXITBLOCK 1 
&br 11 EXITBLOCK 1 
&br BLOCK 6 &br "  ]  
let r = @(+, getcode(p2,cl),"", arithseq(length.cl, 1, 1))
 if isempty.r then"PASS testopt"else"testopt" + r

Function filter(name:word, s:seq.word)seq.word if name = s_1 then s else""

function filter(a:seq.char,s:seq.word)seq.word 
if subseq(decodeword.s_1,1,length.a)=a then s else ""

Function getcode(p2:seq.seq.word, para:seq.word, codelist:seq.seq.word, no:int)seq.word
 let name = merge.("optest" + toword.no + "Ztestopt" + para)
 let t = @(+, filter(name),"", p2)
 let code = subseq(t, 3, length.t)
  if codelist_no = code then""else"&br FAIL" + toword.no + code +"&p"+codelist_no
  
Function getcode(p2:seq.seq.word,  codelist:seq.seq.word, no:int)seq.word
 let name =  decodeword."optest"_1 + decodeword.toword.no + decodeword."Ztestopt"_1  
 let t = @(+, filter(name),"", p2)
 let code = subseq(t, 3, length.t)
  if codelist_no = code then""else"&br FAIL" + toword.no + code +"&p"+codelist_no
  
  

Function optest1 int 3 + 4

Function optest2 int 3 * 4

Function optest3 int if true then 1 else 2

Function optest4 int if false then 1 else 2

Function optest5 word"FIRST"_1

Function optest6 word merge."A B"

Function optest7 seq.word"A" + "B"

Function optest8 int [ 1, 2, 3 + 4]_3

Function optest9 int
let a = 5
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

Function optest18 bits bits.10 &or bits.19

Function optest19 bits bits.10 &and bits.19

Function optest20 int parabits(3)

Function optest21 char char1."AJK"

Function optest22 boolean  "A"_1=encodeword.[ char.65]

Function optest23 int optest23a(6,3)

Function parabits(nopara:int)int let b=nopara toint((bits.(  if b > 6 then 0 else   b + 1)) << 5)

Function optest23a(a:int,b:int) int (a+a) / b

Function optest24(i:int) int  
  if i in [5] then 24 else  0

Function optest25(b:seq.int)  int   
 if   b_3=3333  &or   b_3 in [5,8,9]   &or   b_3=10  then 25 else 2

/Function optest26 int    
let x= [1, 3 ^ 5,3] 
     assert length.x=3 report "XXXXXX arg" 
           if length.x=2 &and false then
 5         else 10
 
Function optest26(s:seq.word,i:int) int  
  if s_i = "xxx"_1 then 3 else if s_i in "a b" then 4 else if s_i in "c d" then 4 else 5

Function optest27(a:int, result:int)int
 // tail recursion // if a = 1 then result else optest27(a - 1, a * result)

Function optest28(a:int, b:int)boolean a > 0 ∧ b < 10

Function optest29(a:int, b:int)boolean a > 0 ∨ b < 10

Function optest30(w:word,a:int,b:int) int    if    w  in "test"    then a else b

Function optest31(s:seq.int,i:int) int    if    s_i  in [1,3] &or s_i =4    then 10 else 11


Function optest16a(a:seq.char)seq.int
 // This is just a type change and the compiler recognizes this and does not generate code // @(+, toint, empty:seq.int, a)