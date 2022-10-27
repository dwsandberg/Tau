Module test11a

use callconfig

use compilerfrontT.callconfig

use checking

use file

use seq.file

use process.midpoint

use standard

use symbol2

use set.symdef

Function test11a(in:seq.file) seq.word
let z = 
 [compare(in, "a+b+c", "(a+b)+c")
 , compare(in, "a * b * c", "(a * b) * c")
 , compare(in, "a+b * c", "a+(b * c)")
 , compare(in, "-a+b", "(-a)+b")
 , compare(in, "a+-b", "a+(-b)")
 , compare(in, "a^2+b", "(a^2)+b")
 , compare(in, "length.[1, 2]", "length ([1, 2])")
 , compare(in
 , "if true then 1 else if true then 3 else 4 /if+5"
 , "if true then 1 else (if true then 3 else 4 /if+5)"
 )
 , testerror(in, "<* literal syntax error *>", "function f1 (a:int) boolean (a")
 , testerror(in, "<* literal syntax error *>", "function f1 (a:int) boolean [a")
 , testerror(in, "<* literal syntax error *>", "function f1 (a:int) boolean [a+")
 , testerror(in, "<* literal stray} *>", "function f1 (a:int) boolean a+} a")
 , testerror(in
 , "Function f1 is defined twice in module testit"
 , "function f1 (a:int) int 3 /p function f1 (a:int) int 3"
 )
 , testerror(in
 , "<* literal then and else types are different *>"
 , "function f1 (a:int) int if true then true else 0"
 )
 , testerror(in
 , "<* literal cond of if must be boolean but is int *>"
 , "function f1 (a:int) int if 1 then 2 else 3"
 )
 , testerror(in
 , "<* literal condition in assert must be boolean"
 , "function f1 (a:int) int assert 1 report 2 3"
 )
 , testerror(in
 , "<* literal report in assert must be seq of word in:"
 , "function f1 (a:int) int assert true report 2 3"
 )
 , testerror(in, "<* literal cannot resolve type hhh", "function f1 (z:hhh) int 3")
 , testerror(in, "<* literal cannot resolve type xxx", "function f1 (z:int) xxx 3")
 , testerror(in, "recursive type problem:", "type testtype is fld1:testtype")
 , testerror(in
 , "module testit contains unresolved exports:testit:f1 (int, int) int"
 , "Export f1 (int, int) int"
 )
 , testerror(in, "Export result type does not match", "Export+(int, int) boolean")
 , testerror(in
 , "module testit contains lines that cannot be resolved:use int.notdefined"
 , "use int.notdefined"
 )
 , testerror(in
 , "module testit contains lines that cannot be resolved:use notdefined"
 , "use notdefined"
 )
 , testerror(in, "Duplicate type definition", "type t1 is a:int /p type t1 is b:int")
 , testerror(in, "Duplicate module name", "Module testit")
 ]
check(z, "test11a") + checkprec

function testcomp2(in:seq.file, s:seq.word) seq.word
let txt = 
 "Library = testcomp uses = stdlib exports = testit
  /p module testit
  /p use standard
  /p $(s)"
let p = 
 process.compilerFront:callconfig("pass1", [file("a.ls", txt)] + in << 1)
if aborted.p then message.p
else
 for acc = "", sd ∈ toseq.prg.result.p do acc + "/br /br" + %.sym.sd + %.code.sd /for (acc)

function compare(in:seq.file, exp1:seq.word, exp2:seq.word) boolean
testcomp2(in, "Function f1 (a:int, b:int, c:int) int $(exp1)")
= testcomp2(in, "Function f1 (a:int, b:int, c:int) int $(exp2)")

function isprefix(p:seq.word, s:seq.word) boolean subseq(s, 1, length.p) = p

function testerror(in:seq.file, m:seq.word, code:seq.word) boolean
let r = testcomp2(in, code)
let a = isprefix(m, r)
assert isprefix(m, r) report "Fail test11a expected:$(m) /br got:$(subseq(r, 1, length.m))"
a

type checkprec is toseq:seq.word

function checkprec seq.word
assert-(1 * 1) - 5 = -6 report "Fail prec"
let a = 
 [x.1 + {should not change assocativity} x.2 + x.3
 , x.1 + x.2 + x.3
 , x.1 * x.2 * x.3
 , (x.1)^(x.2)^(x.3)
 , (x.1)_(x.2)_(x.3)
 ,-x.1 * (x.2)^(x.3)
 , x.1 * x.2 + x.3
 , x.1 + x.2 * x.3
 , uni.x.1 * x.2
 , uni.(x.1)^(x.2)
 , x.1 + x.2 = x.3
 , x.1 = x.2 + x.3
 , (x.1 > x.2) = x.3
 , x.1 = x.2 > x.3
 , x.1 = x.2 ∧ x.3
 , x.1 ∧ x.2 = x.3
 , x.1 ∧ x.2 ∨ x.3
 , x.1 ∨ x.2 ∧ x.3
 , uni.x.1 + x.2
 ]
let b = 
 ["((1+2)+3)"
 , "((1+2)+3)"
 , "((1 * 2) * 3)"
 , "((1^2)^3)"
 , "((1_2)_3)"
 , "((-1) * (2^3))"
 , "((1 * 2)+3)"
 , "(1+(2 * 3))"
 , "((uni 1) * 2)"
 , "(uni (1^2))"
 , "((1+2) = 3)"
 , "(1 = (2+3))"
 , "((1 > 2) = 3)"
 , "((1 = 2) > 3)"
 , "((1 = 2) ∧ 3)"
 , "(1 ∧ (2 = 3))"
 , "((1 ∧ 2) ∨ 3)"
 , "(1 ∨ (2 ∧ 3))"
 , "((uni 1)+2)"
 ]
check(for acc = empty:seq.seq.word, @e ∈ a do acc + toseq.@e /for (acc)
, b
, "precedence test"
)

function check(y:seq.seq.word, b:seq.seq.word, testname:seq.word) seq.word
let x = 
 for acc = "", i ∈ arithseq(length.y, 1, 1) do if y_i = b_i then acc else acc + toword.i /for (acc)
if x = "" then "PASS $(testname)"
else "<* literal FAILED *> test $(x) in $(testname)"

function x(a:int) checkprec checkprec.[toword.a]

function -(a:checkprec) checkprec checkprec."(-$(toseq.a))"

function uni(a:checkprec) checkprec checkprec."(uni $(toseq.a))"

function ^(a:checkprec, b:checkprec) checkprec checkprec."($(toseq.a)^$(toseq.b))"

function _(a:checkprec, b:checkprec) checkprec checkprec."($(toseq.a)_$(toseq.b))"

function *(a:checkprec, b:checkprec) checkprec checkprec."($(toseq.a) * $(toseq.b))"

function +(a:checkprec, b:checkprec) checkprec checkprec."($(toseq.a)+$(toseq.b))"

function =(a:checkprec, b:checkprec) checkprec checkprec."($(toseq.a) = $(toseq.b))"

function >(a:checkprec, b:checkprec) checkprec checkprec."($(toseq.a) > $(toseq.b))"

function ∧(a:checkprec, b:checkprec) checkprec checkprec."($(toseq.a) ∧ $(toseq.b))"

function ∨(a:checkprec, b:checkprec) checkprec checkprec."($(toseq.a) ∨ $(toseq.b))" 