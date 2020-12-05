#!/usr/local/bin/tau ; use testopt ; testopt

Module testopt

use UTF8

use bits

use seq.char

use seq.int

use main2

use real

use stdlib

use textio

use otherseq.seq.word

use seq.seq.word

use seq.word

use set.word

Function testopt seq.word
let p2 = secondPass."testall"_1
let cl = ["7","12","1","2","WORD FIRST","WORD AB", '"A B"',"7","11","2"
,"1","0","4607182418800017408","44","2","46","72","27","2","128"
,"65","1","4", // optest24 //"%1 5 =(int, int)builtin 2 3 BR 3 
&br 24 EXITBLOCK 1 
&br 0 EXITBLOCK 1 
&br BLOCK 3 
&br", // optest25 //
"%1 3_(int seq, int)seq.int DEFINE 2 %2 9 >(int, int)builtin 5 2 BR 3 
&br %2 9 =(int, int)builtin 7 3 BR 3 
&br %2 5 =(int, int)builtin 7 4 BR 3 
&br %2 8 =(int, int)builtin 7 8 BR 3 
&br %2 10 =(int, int)builtin 7 6 BR 3 
&br %2 3333 =(int, int)builtin 7 8 BR 3 
&br 25 EXITBLOCK 1 
&br 2 EXITBLOCK 1 
&br BLOCK 8 
&br","%1 %2_(word seq, int)seq.word DEFINE 3 %3 WORD c >(int, int)builtin 5 2 BR 3 
&br %3 WORD c =(int, int)builtin 7 3 BR 3 
&br %3 WORD xxx =(int, int)builtin 8 4 BR 3 
&br %3 WORD b =(int, int)builtin 9 10 BR 3 
&br %3 WORD a =(int, int)builtin 9 6 BR 3 
&br %3 WORD d =(int, int)builtin 7 10 BR 3 
&br 4 EXITBLOCK 1 
&br 3 EXITBLOCK 1 
&br 4 EXITBLOCK 1 
&br 5 EXITBLOCK 1 
&br BLOCK 10
&br","%1 %2 3 LOOPBLOCK(int, int, int)
&br %3 1 =(int, int)builtin 3 4 BR 3 
&br %4 EXITBLOCK 1 
&br %3 1-(int, int)builtin %3 %4 *(int, int)builtin CONTINUE 2 
&br BLOCK 4 
&br","%1 0 >(int, int)builtin 2 3 BR 3 
&br 10 %2 >(int, int)builtin EXITBLOCK 1 
&br 0 EXITBLOCK 1 
&br BLOCK 3 
&br","%1 0 >(int, int)builtin 2 3 BR 3 
&br 1 EXITBLOCK 1 
&br 10 %2 >(int, int)builtin EXITBLOCK 1 
&br BLOCK 3 
&br", // optest30 //
"%1 WORD test =(int, int)builtin 2 3 BR 3 
&br %2 EXITBLOCK 1 
&br %3 EXITBLOCK 1 
&br BLOCK 3 
&br"
, // test 31 //
"%1 %2_(int seq, int)seq.int DEFINE 3 %3 3 >(int, int)builtin 4 2 BR 3 
&br %3 3 =(int, int)builtin 5 3 BR 3 
&br %3 1 =(int, int)builtin 5 6 BR 3 
&br %3 4 =(int, int)builtin 5 6 BR 3 
&br 10 EXITBLOCK 1 
&br 11 EXITBLOCK 1 
&br BLOCK 6 
&br","%1"]
let r = arithseq(length.cl, 1, 1)@@ +("", getcode(p2, cl, @e))
 if isempty.r then"PASS testopt"else"testopt" + r

function filter(name:word, s:seq.word)seq.word if name = s_1 then s else""

Function getcode(p2:seq.seq.word, codelist:seq.seq.word, no:int)seq.word
 let t1 = p2 @@ +("", filter(merge("optest" + toword.no), @e))
 let t = subseq(t1, findindex("testopt"_1, t1) + 1, length.t1)
 let code = removeoptions(t, length.t)
  // assert false report t1 +" &br"+ t +" &br"+ code //
  if codelist_no = code ∨ no = 26 ∧ shuffletest.sameto(code, codelist_no, 1,"")then
  ""
  else
   " &br  &{ literal FAILED  &} test" + toword.no + "in optest  &br" + code + " &p"
   + codelist_no
   + " &p diffs:"
   + sameto(code, codelist_no, 1,"")
   + " &p"
   + toseq.asset."a b c d xxx"
   
 function shuffletest(s:seq.word) boolean
 s
 in ["17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 d a 85 8 9 92 xxx d 100 10 7 101 9 10 109 4 3 113 5 4 117 3 5","17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 xxx a 85 10 9 100 8 7 101 9 10 109 4 3 113 5 4 117 3 5","47 b xxx 62 xxx b 85 8 9 109 4 3 113 3 4","17 xxx c 32 xxx c 47 b xxx 62 c b 85 8 9 100 9 7 105 3 4 109 4 3"]

function sameto(a:seq.word,b:seq.word,i:int,diffs:seq.word) seq.word
 if i > length.a ∨ i > length.b then diffs
 else if a_i = b_i then sameto(a, b, i + 1, diffs)
 else sameto(a, b, i + 1, diffs + [ toword.i, a_i, b_i])

function removeoptions(s:seq.word, i:int)seq.word
 if i = length.s then
 if not(subseq(s, i - 7, i) = "option(T, word seq)builtin")then s
  else removeoptions(s, i - 9)
 else if not(s_i = '"'_1)then removeoptions(s, i - 1)
 else subseq(s, 1, i - 1)

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

Function optest18 bits bits.10 ∨ bits.19

Function optest19 bits bits.10 ∧ bits.19

Function optest20 int parabits.3

Function optest21 char char1."AJK"

Function optest22 boolean"A"_1 = encodeword.[ char.65]

Function optest23 int optest23a(6, 3)

function parabits(nopara:int)int
 let b = nopara
  toint((bits.if b > 6 then 0 else b + 1) << 5)

Function optest23a(a:int, b:int)int(a + a) / b

Function optest24(i:int)int if i in [ 5]then 24 else 0

Function optest25(b:seq.int)int
 if b_3 = 3333 ∨ b_3 in [ 5, 8, 9] ∨ b_3 = 10 then
 25
 else 2

/Function optest26 int let x = [ 1, 3^5, 3]assert length.x = 3 report"XXXXXX arg"if length.x = 2 &and false then 5 else 10

Function optest26(s:seq.word, i:int)int
 if s_i = "xxx"_1 then 3
 else if s_i in "a b"then 4 else if s_i in "c d"then 4 else 5

Function optest27(a:int, result:int)int
 // tail recursion // if a = 1 then result else optest27(a - 1, a * result)

Function optest28(a:int, b:int)boolean a > 0 ∧ b < 10

Function optest29(a:int, b:int)boolean a > 0 ∨ b < 10

Function optest30(w:word, a:int, b:int)int if w in "test"then a else b

Function optest31(s:seq.int, i:int)int
 if s_i in [ 1, 3] ∨ s_i = 4 then 10 else 11

Function optest32(t:seq.word)seq.word dropparameter(t,"")

function dropparameter(a:seq.word, result:seq.word)seq.word a

Function optest33(a:int, b:int, c:int, d:int)ordering optest33a(a ? b, c ? d)

Function optest33a(a:ordering, b:ordering)ordering
 let x = a
  if x = EQ then b else x

Function optest16a(a:seq.char)seq.int
 // This is just a type change and the compiler recognizes this and does not generate code //
 a @@ +(empty:seq.int, toint.@e)