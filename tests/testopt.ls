Module testopt

use compileTimeT.callconfig

use compilerfrontT.callconfig

use file

use llvmcode

use standard

use symbol2

use set.symdef

use seq.seq.word

Function multitarget(value1:int, a:boolean, b:boolean) int
{check to see optimization handles this case correctly}
if if value1 = 4 then a else false then
40
else if if value1 = 3 then b else false then
30
else 20

Function testopt(in:seq.file) seq.word
let p2 = toseq.prg.compilerFront:callconfig("pass2", in, "TESTOPT", "opttests")
let cl = [
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
  "Start (int)
   /br %1 5 = (int, int) boolean Br2 (1, 2)
   /br 24 Exit
   /br 0 Exit
   /br EndBlock
   /br"
 , "25"
 , {test 26}
  "3 %1 seq.int:_(int, seq.int) int Define 2 Start (int)
   /br %2 3333 Jump (int, int) boolean Br2 (6, 1)
   /br 5 Br2 (5, 1)
   /br 7 Br2 (4, 1)
   /br 8 Br2 (3, 1)
   /br 9 Br2 (2, 1)
   /br 10 Br2 (1, 2)
   /br 25 Exit
   /br 2 Exit
   /br EndBlock
   /br"
 , "%1 %2 Loop:3 (int, int) int
  /br %3 1 = (int, int) boolean Br2 (1, 2)
  /br %4 Exit
  /br %3 1-(int, int) int %3 %4 * (int, int) int Continue 2
  /br EndBlock
  /br"
 , {optest28}
  "Start (boolean)
   /br %1 0 > (int, int) boolean Br2 (1, 2)
   /br 10 %2 > (int, int) boolean Exit
   /br false boolean Exit
   /br EndBlock
   /br"
 , {optest29}
  "Start (boolean)
   /br %1 0 > (int, int) boolean Br2 (1, 2)
   /br true boolean Exit
   /br 10 %2 > (int, int) boolean Exit
   /br EndBlock
   /br"
 , {optest30}
  "Start (int)
   /br %1 WORD test = (int, int) boolean Br2 (1, 2)
   /br %2 Exit
   /br %3 Exit
   /br EndBlock
   /br"
 , "31"
 , "%1"
 , {test 33} "33"
 , "%2 %1 seq.int:_(int, seq.int) int Define 3 Start (int)
  /br %3 1 Jump (int, int) boolean Br2 (7, 1)
  /br 9 Br2 (6, 1)
  /br 5 Br2 (5, 1)
  /br 2 Br2 (4, 1)
  /br 12 Br2 (3, 1)
  /br 3 Br2 (2, 1)
  /br 4 Br2 (1, 2)
  /br 10 Exit
  /br 11 Exit
  /br EndBlock
  /br"
 , {test 35}
  "Start (int)
   /br %2 %1 seq.word:_(int, seq.word) word Define 3 %3 WORD e = (int, int) boolean Br2 (
   6, 1)
   /br %3 WORD d = (int, int) boolean Br2 (5, 1)
   /br %3 WORD c = (int, int) boolean Br2 (4, 1)
   /br %3 WORD b = (int, int) boolean Br2 (3, 1)
   /br %3 WORD a = (int, int) boolean Br2 (2, 1)
   /br %2 %1 seq.word:_(int, seq.word) word WORD x = (int, int) boolean Br2 (1, 2)
   /br 10 Exit
   /br 11 Exit
   /br EndBlock
   /br"
 , {optest36}
  "Start (int)
   /br %1 WORD a = (int, int) boolean Br2 (3, 1)
   /br %1 WORD b = (int, int) boolean Br2 (2, 1)
   /br %1 WORD c = (int, int) boolean Br2 (1, 2)
   /br 26 Exit
   /br 0 Exit
   /br EndBlock
   /br"
 , {test 37}
  "Start (int)
   /br %2 %1 seq.word:_(int, seq.word) word WORD xxx = (int, int) boolean Br2 (1, 2)
   /br 3 Exit
   /br %2 %1 seq.word:_(int, seq.word) word Define 3 %3 WORD a = (int, int) boolean Br2 (
   5, 1)
   /br %3 WORD b = (int, int) boolean Br2 (4, 1)
   /br %2 %1 seq.word:_(int, seq.word) word Define 4 %4 WORD c = (int, int) boolean Br2 (
   3, 1)
   /br %4 WORD d = (int, int) boolean Br2 (2, 1)
   /br %4 WORD z = (int, int) boolean Br2 (1, 2)
   /br 4 Exit
   /br 5 Exit
   /br EndBlock
   /br"
 , ""
 , ""
 , {40} "^(dq."")^(dq."this for loop should be a noop")"
  + "seq.int:+(seq.int, seq.int) seq.int Define 1 %1"
 , ""
 , "Start (int)
  /br %1 1 = (int, int) boolean Br2 (3, 1)
  /br %1 3 = (int, int) boolean Br2 (3, 1)
  /br %1 7 = (int, int) boolean Br2 (3, 4)
  /br 10 Exit
  /br 30 Exit
  /br 70 Exit
  /br 0 Exit
  /br EndBlock
  /br"
 , {43}
  "Start (int)
   /br %1 4 = (int, int) boolean Br2 (1, 2)
   /br %2 10 = (int, int) boolean Br2 (5, 1)
   /br %1 1 Jump (int, int) boolean Br2 (16, 1)
   /br 2 Br2 (14, 1)
   /br 5 Br2 (8, 1)
   /br 7 Br2 (11, 1)
   /br %1^(merge."-12") Jump (int, int) boolean Br2 (9, 1)
   /br^(merge."-10") Br2 (7, 1)
   /br^(merge."-5") Br2 (6, 1)
   /br^(merge."-4") Br2 (4, 1)
   /br
   ^(merge."-3") Br2 (2, 1)
   /br 100 Exit
   /br 30 Exit
   /br 40 Exit
   /br 50 Exit
   /br 60 Exit
   /br 70 Exit
   /br 20 Exit
   /br 10 Exit
   /br EndBlock
   /br"
 , "Start (int)
  /br %1 4 = (int, int) boolean Br2 (1, 2)
  /br %2 10 = (int, int) boolean Br2 (5, 1)
  /br %1 1 Jump (int, int) boolean Br2 (18, 1)
  /br 2 Br2 (16, 1)
  /br 5 Br2 (10, 1)
  /br 7 Br2 (13, 1)
  /br %1^(merge."-12") Jump (int, int) boolean Br2 (11, 1)
  /br^(merge."-10") Br2 (9, 1)
  /br^(merge."-5") Br2 (8, 1)
  /br^(merge."-4") Br2 (6, 1)
  /br
  ^(merge."-3") Br2 (4, 1)
  /br %2 5 = (int, int) boolean Br2 (2, 1)
  /br 100 Exit
  /br 200 Exit
  /br 30 Exit
  /br 40 Exit
  /br 50 Exit
  /br 60 Exit
  /br 70 Exit
  /br 20 Exit
  /br 10 Exit
  /br EndBlock
  /br"
 , "0 0 %1 getseqlength (ptr) int Define 2 0 Loop:3 (int, int, int) int
  /br %5 %2 = (int, int) boolean Br2 (1, 2)
  /br 0 Exit
  /br %5 1+(int, int) int Define 6 %1 getseqtype (ptr) int Define 9 Start (int)
  /br %9 1 > (int, int) boolean Br2 (1, 2)
  /br %1 %6 callidx (seq.int, int) int Exit
  /br %1 %6 idxseq (seq.int, int) int Exit
  /br EndBlock
  /br Define 7 %4 64 = (int, int) boolean Br2 (1, 2)
  /br %3 8 %6 Continue 3
  /br %3 9 %6 Continue 3
  /br EndBlock
  /br Define 8 3"
 , {46} "2"
 , {47}
  "%1 %2 %3 Loop:4 (int, int, int) int
   /br Start (seq.int)
   /br %5 0 = (int, int) boolean Br2 (1, 2)
   /br^(dq."C") Exit
   /br^(dq."B") Exit
   /br EndBlock
   /br Define 7 %4 %5+(int, int) int Define 8 %5 0 = (int, int) boolean Br2 (1, 2)
   /br %6 Exit
   /br %4 %5 1-(int, int) int %6 %4 * (int, int) int Continue 3
   /br EndBlock
   /br"
 , "^(dq."")"
  + "%1 getseqlength (ptr) int Define 2 %2 1+(int, int) int Loop:3 (seq.int, int) int
   /br %4 1 = (int, int) boolean Br2 (1, 2)
   /br 0 Exit
   /br %4^(merge."-1")+(int, int) int Define 5 %1 getseqtype (ptr) int Define 8 Start (int)
   /br %8 1 > (int, int) boolean Br2 (1, 2)
   /br %1 %5 callidx (seq.int, int) int Exit
   /br %1 %5 idxseq (seq.int, int) int Exit
   /br EndBlock
   /br Define 6 %3 %6 seq (1) seq.int seq.word:+(seq.word, seq.word) seq.word %5
   Continue 2
   /br EndBlock
   /br Define 7 %3"
 , {49} "WORD test"
 , {50}
  "Start (int)
   /br %1 5555 = (int, int) boolean Br2 (1, 2)
   /br 80 Exit
   /br %1 7 Jump (int, int) boolean Br2 (4, 1)
   /br 2 Br2 (4, 1)
   /br 5555 Br2 (4, 1)
   /br 1 Br2 (4, 5)
   /br 70 Exit
   /br 20 Exit
   /br 30 Exit
   /br 60 Exit
   /br %1 5555 = (int, int) boolean Br2 (1, 2)
   /br 200 Exit
   /br 100 Exit
   /br EndBlock
   /br"
]
let r =
 for acc = "", @e ∈ arithseq(n.cl, 1, 1) do acc + getcode(p2, cl, @e),
  acc
  + 
   if
    [40, 20, 30, 20]
    = [
     multitarget(4, true, false)
     , multitarget(4, false, false)
     , multitarget(3, false, true)
     , multitarget(2, false, false)
    ]
   then
   ""
   else "fail multitarget",
if isempty.r then "PASS testopt" else "testopt^(r)"

function getcode(p2:seq.symdef, codelist:seq.seq.word, no:int) seq.word
let name = merge."optest^(no)"
for code = "", p ∈ p2 do if name = name.sym.p then %.code.p else code,
if no_codelist = code ∨ no = 260 ∧ shuffletest.sameto(code, no_codelist, 1, "") then
""
else "
 /br <* literal FAILED *> test^(no) in optest. Got: 
 /br^(code)
 /p Expected:^(no_codelist)"

function shuffletest(s:seq.word) boolean
s
 ∈ [
 "17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 d a 85 8 9 92 xxx d 100 10 7 101 9 10 109 4
  3 113 5 4 117 3 5"
 , "17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 xxx a 85 10 9 100 8 7 101 9 10 109 4 3 113 5
  4 117 3 5"
 , "47 b xxx 62 xxx b 85 8 9 109 4 3 113 3 4"
 , "17 xxx c 32 xxx c 47 b xxx 62 c b 85 8 9 100 9 7 105 3 4 109 4 3"
]

function sameto(a:seq.word, b:seq.word, i:int, diffs:seq.word) seq.word
if i > n.a ∨ i > n.b then
diffs
else if i_a = i_b then
sameto(a, b, i + 1, diffs)
else sameto(a, b, i + 1, diffs + [toword.i, i_a, i_b]) 