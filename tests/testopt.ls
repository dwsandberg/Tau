Module testopt

use compileTimeT.callconfig

use compilerfrontT.callconfig

use testanal.callconfig

use file

use seq.file

use llvmcode

use standard

use symbol1

use set.symdef

use seq.seq.word

Function multitarget(value1:int, a:boolean, b:boolean) int
{check to see optimization handles this case correctly}
if if value1 = 4 then a else false then 40
else if if value1 = 3 then b else false then 30
else 20

Function testopt(in:seq.file) seq.word
let p2 = toseq.prg.compilerFront:callconfig("pass2", in, "opttests", "")
let cl =
 [
  "7"
  , "12"
  , "1"
  , "2"
  , "WORD FIRST"
  , "WORD AB"
  , dq."A B"
  , "7"
  , "11"
  , "2"
  , "1"
  , "false boolean"
  , "4607182418800017408"
  , "44"
  , "2"
  , "%1"
  , "72"
  , "27"
  , "2"
  , "128"
  , "65"
  , "true boolean"
  , "4"
  , {optest24}
  "Start(int)/br
  %1 5 =(int, int)boolean Br2(1, 2)/br
  24 Exit /br
  0 Exit /br
  EndBlock /br
  "
  , "25"
  , {test 26} "%1 3 seq.int:sub"
  + "(seq.int, int)int Define 2 Start(int)/br
  %2 JmpB 15 4:1 5:1 7:1 8:1 9:1 3333:1:2 Jmp 15 /br
  25 Exit /br
  20 Exit /br
  EndBlock /br
  "
  , "%1 %2 Loop:3(int, int)int /br
  %3 1 =(int, int)boolean Br2(1, 2)/br
  %4 Exit /br
  %3 1-(int, int)int %3 %4 *(int, int)int Continue 2 /br
  EndBlock /br
  "
  , {optest28}
  "Start(boolean)/br
  %1 0 >(int, int)boolean Br2(1, 2)/br
  10 %2 >(int, int)boolean Exit /br
  false boolean Exit /br
  EndBlock /br
  "
  , {optest29}
  "Start(boolean)/br
  %1 0 >(int, int)boolean Br2(1, 2)/br
  true boolean Exit /br
  10 %2 >(int, int)boolean Exit /br
  EndBlock /br
  "
  , {optest30}
  "Start(int)/br
  %1 WORD test =(int, int)boolean Br2(1, 2)/br
  %2 Exit /br
  %3 Exit /br
  EndBlock /br
  "
  , "31"
  , "%1"
  , {test 33} "33"
  , "%1 %2 seq.int:sub(seq.int, int)int Define 3 Start(int)/br
  %3 JmpB 17 1:1 9:1 5:1 2:1 12:1 3:1 4:1:2 Jmp 17 /br
  10 Exit /br
  11 Exit /br
  EndBlock /br
  "
  , {test 35}
  "Start(int)/br
  %1 %2 seq.word:sub"
  + "(seq.word, int)word Define 3 %3 JmpB 15 WORD e:1 WORD d:1 WORD c:1 WORD b:1 WORD a:1 WORD x:1:2 Jmp 15 /br
  10 Exit /br
  11 Exit /br
  EndBlock /br
  "
  , {optest36}
  "Start(int)/br
  %1 JmpB 9 WORD a:1 WORD b:1 WORD c:1:2 Jmp 9 /br
  26 Exit /br
  0 Exit /br
  EndBlock /br
  "
  , {test 37}
  "Start(int)/br
  %1 %2 seq.word:sub"
  + "(seq.word, int)word Define 3 %3 JmpB 15 WORD xxx:1 WORD a:2 WORD b:2 WORD c:2 WORD d:2 WORD z:2:3 Jmp 15 /br
  3 Exit /br
  4 Exit /br
  5 Exit /br
  EndBlock /br
  "
  , "%1 %2 >1(int, int)ordering Define 5 %3 %4 >1(int, int)ordering Define 6 Start(int)/br
  %5 1 =(int, int)boolean Br2(1, 2)/br
  %6 Exit /br
  %5 Exit /br
  EndBlock /br
  "
  , "46"
  , {40}dq."this for loop should be a noop"
  , "true boolean"
  , "Start(int)/br
  %1 JmpB 9 1:1 3:2 7:3:4 Jmp 9 /br
  10 Exit /br
  30 Exit /br
  70 Exit /br
  0 Exit /br
  EndBlock /br
  "
  , {43}
  "Start(int)/br
  %1 4 =(int, int)boolean Br2(1, 2)/br
  %2 10 =(int, int)boolean Br2(5, 1)/br
  %1 JmpB 11 7:1 2:2 5:5 1:3:4 Jmp 11 /br
  70 Exit /br
  20 Exit /br
  10 Exit /br
  %1 JmpB 13-3:1-4:2-5:3-10:3-12:4:5 Jmp 13 /br
  30 Exit /br
  40 Exit /br
  50 Exit /br
  60 Exit /br
  100 Exit /br
  EndBlock /br
  "
  , "Start(int)/br
  %1 4 =(int, int)boolean Br2(1, 2)/br
  %2 10 =(int, int)boolean Br2(5, 1)/br
  %1 JmpB 11 7:1 2:2 5:5 1:3:4 Jmp 11 /br
  70 Exit /br
  20 Exit /br
  10 Exit /br
  %1 JmpB 13-3:1-4:2-5:3-10:3-12:4:5 Jmp 13 /br
  30 Exit /br
  40 Exit /br
  50 Exit /br
  60 Exit /br
  %2 5 =(int, int)boolean Br2(1, 2)/br
  200 Exit /br
  100 Exit /br
  EndBlock /br
  "
  , "0 0 %1 getseqlength(ptr)int Define 2 0 Loop:3(int, int, int)int /br
  %5 %2 =(int, int)boolean Br2(1, 2)/br
  0 Exit /br
  %5 1+(int, int)int Define 6 %1 %6 idxNB(seq.int, int)int Define 7 %4 64 =(int, int)boolean Br2(1, 2)/br
  %3 8 %6 Continue 3 /br
  %3 9 %6 Continue 3 /br
  EndBlock /br
  Define 8 3"
  , {46} "2"
  , {47}
  "%1 %2 %3 Loop:4(int, int, int)int /br
  Start(seq.int)/br
  %5 0 =(int, int)boolean Br2(1, 2)/br
  :(dq."C")Exit /br
  :(dq."B")Exit /br
  EndBlock /br
  Define 7 %4 %5+(int, int)int Define 8 %5 0 =(int, int)boolean Br2(1, 2)/br
  %6 Exit /br
  %4 %5 1-(int, int)int %6 %4 *(int, int)int Continue 3 /br
  EndBlock /br
  "
  , dq.""
  + "%1 getseqlength(ptr)int Define 2 %2 1+(int, int)int Loop:3(seq.int, int)int /br
  %4 1 =(int, int)boolean Br2(1, 2)/br
  0 Exit /br
  %4-1+(int, int)int Define 5 %1 %5 idxNB(seq.int, int)int Define 6 %3 %6 seq(1)seq.int seq.word:+(seq.word, seq.word)seq.word %5 Continue 2 /br
  EndBlock /br
  Define 7 %3"
  , {49} "WORD test"
  , "Start(int)/br
  %1 3+(int, int)int 9 =(int, int)boolean Br2(1, 2)/br
  90 Exit /br
  %1 JmpB 11 7:1 3:2 1:3 0:4:5 Jmp 11 /br
  70 Exit /br
  30 Exit /br
  20 Exit /br
  0 Exit /br
  55 Exit /br
  EndBlock /br
  "
  , {51}
  "Start(seq.int)/br
  %1 JmpB 19 2:4 8:1 9:1 10:2 11:4 14:4 16:4 15:1:1 Jmp 19 /br
  :(dq."R")Exit /br
  %1 1 =(int, int)boolean Br2(1, 2)/br
  :(dq."~ENTRY")Exit /br
  :(dq."")Exit /br
  EndBlock /br
  "
  , {52}
  "Start(int)/br
  %1 JmpB 11 40:1 41:1 42:1 43:1:2 Jmp 11 /br
  33 Exit /br
  34 Exit /br
  EndBlock /br
  "
  , ""
  , {54} "6 0 /(int, int)int Define 1 14"
  , {55} ""
  , {56} ""
 ]
{,{50}"Start(int)/br
%1 5555 =(int, int)boolean Br2(1, 2)/br
80 Exit /br
%1 7 Jump(int, int)boolean Br2(4, 1)/br
2 Br2(4, 1)/br
5555 Br2(4, 1)/br
1 Br2(4, 5)/br
70 Exit /br
20 Exit /br
30 Exit /br
60 Exit /br
%1 5555 =(int, int)boolean Br2(1, 2)/br
200 Exit /br
100 Exit /br
EndBlock /br
"]}
let r =
 for acc = "", @e ∈ arithseq(n.cl, 1, 1) do acc + getcode(p2, cl, @e),
 acc
 + if [40, 20, 30, 20]
 = [
  multitarget(4, true, false)
  , multitarget(4, false, false)
  , multitarget(3, false, true)
  , multitarget(2, false, false)
 ] then ""
 else "fail multitarget",
analtests:callconfig + if isempty.r then "PASS testopt" else "testopt:(r)"

function getcode(p2:seq.symdef, codelist:seq.seq.word, no:int) seq.word
let name = merge."optest:(no)"
for code = "", p ∈ p2 do if name = name.sym.p then %.code.p else code,
if codelist sub no = code
 ∨ no = 260 ∧ shuffletest.sameto(code, codelist sub no, 1, "") then ""
else
 "/br:(red."FAILED")test:(no)in optest. Got: /br
 :(code)/p Expected::(codelist sub no)"

function shuffletest(s:seq.word) boolean
s
 ∈ [
 "17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 d a 85 8 9 92 xxx d 100 10 7 101 9 10 109 4 3 113 5 4 117 3 5"
 , "17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 xxx a 85 10 9 100 8 7 101 9 10 109 4 3 113 5 4 117 3 5"
 , "47 b xxx 62 xxx b 85 8 9 109 4 3 113 3 4"
 , "17 xxx c 32 xxx c 47 b xxx 62 c b 85 8 9 100 9 7 105 3 4 109 4 3"
]

function sameto(a:seq.word, b:seq.word, i:int, diffs:seq.word) seq.word
if i > n.a ∨ i > n.b then diffs
else if a sub i = b sub i then sameto(a, b, i + 1, diffs)
else sameto(a, b, i + 1, diffs + [toword.i, a sub i, b sub i]) 