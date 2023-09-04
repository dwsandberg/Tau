Module testPEG

use PEG

use standard

use file

use otherseq.seq.word

use otherseq.word

Function testPEG seq.word
{ENTRYPOINT}
let tbl = maketable."S ! f1 A /action /1
 /br / ! f1 Z /action /1
 /br / Header /action /1
 /br / /action nomatch
 /br A a B c d /action /1 1
 /br / a B c /action /1 2
 /br / a B /action /1 3
 /br B /action 4
 /br * Z ! e ! D any /action /0 5
 /br D d d d /action /Discard
 /br Header id (FPL) Type Comment /action /1 (/2) /3
 /br / id Type Comment /action /1 /2
 /br / id:Type (FPL) Type Comment /action /1:/2 (/3) /4
 /br / id:Type Type Comment /action /1:/2 /3
 /br FPL FP FPL' /action /1 /2
 /br * FPL', FP /action /0, /1
 /br FP any:Type /action /1:/2
 /br / Type /action /1
 /br Type id.Type /action /1./2
 /br / id /action /1
 /br id !, !] ! {! (!) !:!. any /action /All
 /br * Comment C /action /Discard"
let result =
 check(tbl, "a", "Match 4 3")
 + check(tbl, "a c", "Match 4 2")
 + check(tbl, "a c d", "Match 4 1")
 + check(tbl, "b b b d d", "Match 5 5 5 5 5")
 + check(tbl, "e", "MatchPrefix")
 + check(tbl, "a c e", "MatchPrefix 4 2")
 + check(tbl, "d d d", "MatchPrefix")
 + check(tbl, "f1 int C", "Match f1 int")
 + check(tbl, "f1:seq.int seq.int", "Match f1:seq.int seq.int")
 + check(tbl, "f1:int (int) seq.int", "Match f1:int (int) seq.int")
 + check(
  tbl
  , "f1 (a:int, b:boolean) seq.seq.int"
  , "Match f1 (a:int, b:boolean) seq.seq.int"
 )
 + checkerror("A a /action a /br A b /action b", "Duplicate Non-Terminal:A")
 + checkerror("A a", "PEGgrammar: expected one /action in A a /br A a"),
if isempty.result then "Pass PEG" else "Fail PEG^(result)"

function checkerror(input:seq.word, expect:seq.word) seq.word
let got = message.process.checkgrammar.input,
if got = expect then "" else "Fail got:^(got) expected:^(expect)"

function checkgrammar(gin:seq.word) PEGtable maketable.gin

use process.PEGtable

function check(tbl:PEGtable, input:seq.word, expect:seq.word) seq.word
let got = run(tbl, input),
if got = expect then "" else "Fail^(input) got:^(got) expected:^(expect)" 