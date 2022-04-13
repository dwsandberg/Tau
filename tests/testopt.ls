Module testopt

use main2

use standard

use symbol2

use seq.symdef

use set.word

use otherseq.seq.word

use textio

Function multitarget(value1:int, a:boolean, b:boolean)int
{check to see optimization handles this case correctly}
if if value1 = 4 then a else false then 40
else if if value1 = 3 then b else false then 30 else 20

use bits

use file

use seq.file

Function testopt(f:file) seq.word
let p2 = prg.compilerfront:libllvm("pass2",
breakparagraph.{getfile:byte("tests/opttests.ls")} data.f)
let cl = 
 ["7"
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
 , "internal:false boolean"
 , "4607182418800017408"
 , "44"
 , "2"
 , "46"
 , "72"
 , "27"
 , "2"
 , "128"
 , "65"
 , "internal:true boolean"
 , "4"
 , {optest24}
 "Start(int) /br %1 5 internal:=(int, int)boolean Br2(1, 2) /br 24 Exit  /br 0 Exit  /br EndBlock  /br"
 , "25"
 , {optest26}
 "Start(int) /br %1 WORD a internal:=(int, int)boolean Br2(3, 1) /br %1 WORD b internal:=(int, int)boolean Br2(2, 1) /br 
%1 WORD c internal:=(int, int)boolean Br2(1, 2) /br 26 Exit  /br 0 Exit  /br EndBlock  /br"
 , "%1 %2 $loopblock.int:LOOPBLOCK:3(int, int) /br %3 1 internal:=(int, int)boolean Br2(1, 2) /br %4 Exit  /br %3 1 internal 
:-(int, int)int %3 %4 internal:*(int, int)int CONTINUE 2  /br EndBlock  /br"
 , {optest28}
 "Start(boolean) /br %1 0 internal:>(int, int)boolean Br2(1, 2) /br 10 %2 internal:>(int, int)boolean Exit  /br internal 
:false boolean Exit  /br EndBlock  /br"
 , {optest29}
 "Start(boolean) /br %1 0 internal:>(int, int)boolean Br2(1, 2) /br internal:true boolean Exit  /br 10 %2 internal:>(int 
, int)boolean Exit  /br EndBlock  /br"
 , {optest30}
 "Start(int) /br %1 WORD test internal:=(int, int)boolean Br2(1, 2) /br %2 Exit  /br %3 Exit  /br EndBlock  /br"
 , "31"
 , "%1"
 , {test 33}"33"
 , "Start(int)
/br %1 %2 seq.int:_(seq.int, int)int Define 3 %3 1 internal:=(int, int)boolean Br2(7, 1)
/br %3 9 internal:=(int, int)boolean Br2(6, 1)
/br %3 5 internal:=(int, int)boolean Br2(5, 1)
/br %3 2 internal:=(int, int)boolean Br2(4, 1)
/br %3 12 internal:=(int, int)boolean Br2(3, 1)
/br %3 3 internal:=(int, int)boolean Br2(2, 1)
/br %1 %2 seq.int:_(seq.int, int)int 4 internal:=(int, int)boolean Br2(1, 2)
/br 10 Exit 
/br 11 Exit 
/br EndBlock 
/br"
 , {test 35}
 "Start(int)
/br %1 %2 seq.word:_(seq.word, int)word Define 3 %3 WORD e internal:=(int, int)boolean Br2(6, 1)
/br %3 WORD d internal:=(int, int)boolean Br2(5, 1)
/br %3 WORD c internal:=(int, int)boolean Br2(4, 1)
/br %3 WORD b internal:=(int, int)boolean Br2(3, 1)
/br %3 WORD a internal:=(int, int)boolean Br2(2, 1)
/br %1 %2 seq.word:_(seq.word, int)word WORD x internal:=(int, int)boolean Br2(1, 2)
/br 10 Exit 
/br 11 Exit 
/br EndBlock 
/br"
 , {test 36}
 "Start(int)
/br %1 3 seq.int:_(seq.int, int)int 3333 internal:=(int, int)boolean Br2(6, 1)
/br %1 3 seq.int:_(seq.int, int)int Define 2 %2 5 internal:=(int, int)boolean Br2(5, 1)
/br %2 7 internal:=(int, int)boolean Br2(4, 1)
/br %2 8 internal:=(int, int)boolean Br2(3, 1)
/br %2 9 internal:=(int, int)boolean Br2(2, 1)
/br %1 3 seq.int:_(seq.int, int)int 10 internal:=(int, int)boolean Br2(1, 2)
/br 25 Exit 
/br 2 Exit 
/br EndBlock 
/br"
 , {test 37}
 "Start(int)
/br %1 %2 seq.word:_(seq.word, int)word WORD xxx internal:=(int, int)boolean Br2(1, 2)
/br 3 Exit 
/br %1 %2 seq.word:_(seq.word, int)word Define 3 %3 WORD a internal:=(int, int)boolean Br2(2, 1)
/br %3 WORD b internal:=(int, int)boolean Br2(1, 2)
/br 4 Exit 
/br %1 %2 seq.word:_(seq.word, int)word Define 4 %4 WORD c internal:=(int, int)boolean Br2(3, 1)
/br %4 WORD d internal:=(int, int)boolean Br2(2, 1)
/br %4 WORD z internal:=(int, int)boolean Br2(1, 2)
/br 4 Exit 
/br 5 Exit 
/br EndBlock 
/br"
 ]
let r = 
 for acc = "", @e ∈ arithseq(length.cl, 1, 1)do acc + getcode(p2, cl, @e)/for(acc)
 + if[40, 20, 30, 20]
 = [multitarget(4, true, false)
 , multitarget(4, false, false)
 , multitarget(3, false, true)
 , multitarget(2, false, false)
 ]then
  ""
 else"fail multitarget"
if isempty.r then"PASS testopt"else"testopt" + r

Function getcode(p2:seq.symdef, codelist:seq.seq.word, no:int)seq.word
let name = merge("optest" + toword.no)
let code = 
 for acc = "", p ∈ p2 do
  if name = name.sym.p then print.removeoptions.code.p else acc
 /for(acc)
if codelist_no = code ∨ no = 26 ∧ shuffletest.sameto(code, codelist_no, 1, "")then
 ""
else
 " /br  /< literal FAILED  /> test" + toword.no + "in optest  /br" + code
 + " /p"
 + codelist_no
 + " /p diffs:"
 + sameto(code, codelist_no, 1, "")
 + " /p"
 + toseq.asset."a b c d xxx"

function shuffletest(s:seq.word)boolean
s
∈ ["17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 d a 85 8 9 92 xxx d 100 10 7 101 9 10 109 4 3 113 5 4 117 3 5"
, "17 a c 32 a c 47 b xxx 55 7 8 62 c b 70 8 9 71 9 10 77 xxx a 85 10 9 100 8 7 101 9 10 109 4 3 113 5 4 117 3 5"
, "47 b xxx 62 xxx b 85 8 9 109 4 3 113 3 4"
, "17 xxx c 32 xxx c 47 b xxx 62 c b 85 8 9 100 9 7 105 3 4 109 4 3"
]

function sameto(a:seq.word, b:seq.word, i:int, diffs:seq.word)seq.word
if i > length.a ∨ i > length.b then diffs
else if a_i = b_i then sameto(a, b, i + 1, diffs)
else sameto(a, b, i + 1, diffs + [toword.i, a_i, b_i]) 