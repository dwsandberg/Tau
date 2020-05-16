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

/use words

use UTF8

Function testopt seq.word
let p2 = secondPass."testall"_1
let cl = ["7","12","1","2","WORD FIRST","WORD AB",'"A B"',"7","11","2"
,"1","0","4607182418800017408"," 44"," 2"," 46"," 72"]
let c2 = constantseq(99,"")
+ [
"%1 %2  3 LOOPBLOCK  3  &br %3  1 Q3DZbuiltinZintZint 2 3 4 BR 3  &br %4 EXITBLOCK 1 &br
    %3 1 Q2DZbuiltinZintZint 2 %3 %4 Q2AZbuiltinZintZint 2 CONTINUE 2  &br BLOCK 4 &br",
"%1  0 Q3EZbuiltinZintZint 2  2  3  BR 3  &br 10 %2 
Q3EZbuiltinZintZint 2   EXITBLOCK 1   &br 0  EXITBLOCK 1  &br  BLOCK 3 &br",
"%1  0 Q3EZbuiltinZintZint 2  2  3   BR 3  1  &br
 EXITBLOCK 1  &br 10 %2 Q3EZbuiltinZintZint 2 EXITBLOCK 1  &br BLOCK 3 &br"]
let r = @(+, getcode(p2,"", cl),"", arithseq(length.cl, 1, 1))
+ @(+, getcode(p2,"ZintZint", c2),"", arithseq(length.c2 - 99, 1, 100))
 if isempty.r then"PASS testopt"else"testopt" + r

Function filter(name:word, s:seq.word)seq.word if name = s_1 then s else""

Function getcode(p2:seq.seq.word, para:seq.word, codelist:seq.seq.word, no:int)seq.word
 let name = merge.("optest" + toword.no + "Ztestopt" + para)
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

Function optest100(a:int, result:int)int
 // tail recursion // if a = 1 then result else optest100(a - 1, a * result)

Function optest101(a:int, b:int)boolean a > 0 ∧ b < 10

Function optest102(a:int, b:int)boolean a > 0 ∨ b < 10

Function optest16a(a:seq.char)seq.int
 // This is just a type change and the compiler recognizes this and does not generate code // @(+, toint, empty:seq.int, a)