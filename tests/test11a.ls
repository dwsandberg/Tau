Module test11a

use compilerfrontT.callconfig

use checking

use file

use seq.file

use llvmcode

use process.midpoint

use standard

use symbol1

use set.symdef

use seq.seq.word

Function test11a(inp:seq.file) seq.word
let in =
 for acc = empty:seq.file, f ∈ inp do if ext.fn.f ∈ "libinfo" then acc + f else acc,
 acc
let z =
 [
  compare(in, "a+b+c", "(a+b)+c")
  , compare(in, "a * b * c", "(a * b)* c")
  , compare(in, "a+b * c", "a+(b * c)")
  , compare(in, "-a+b", "(-a)+b")
  , compare(in, "a+-b", "a+(-b)")
  , compare(in, "a sup 2+b", "(a sup 2)+b")
  , compare(in, "n.[1, 2]", "n([1, 2])")
  , testerror(
   in
   , "<* literal In module testit name of field is missing in: *>"
   , "type testtype is a:int, int"
  )
  , {???? testerror(in,"<* literal syntax error *>","function f1(a:int)boolean(a"), testerror(in,"<* literal syntax error *>","function f1(a:int)boolean[a"), testerror(in,"<* literal syntax error *>","function f1(a:int)boolean[a+"),}
  testerror(
   in
   , "Function f1 is defined twice in module testit"
   , "function f1(a:int)int 3 /p function f1(a:int)int 3"
  )
  , testerror(
   in
   , "<* literal then and else types are different *>"
   , "function f1(a:int)int if true then true else 0"
  )
  , testerror(
   in
   , "<* literal cond of if must be boolean but is int *>"
   , "function f1(a:int)int if 1 then 2 else 3"
  )
  , testerror(
   in
   , "<* literal condition in assert must be boolean"
   , "function f1(a:int)int assert 1 report 2, 3"
  )
  , testerror(
   in
   , "<* literal report in assert must be seq of word in:"
   , "function f1(a:int)int assert true report 2, 3"
  )
  , testerror(
   in
   , "function f1(z:hhh)<* literal cannot resolve type hhh *>"
   , "function f1(z:hhh)int 3"
  )
  , testerror(
   in
   , "function f1(z:int)xxx 3 <* literal cannot resolve type xxx *>"
   , "function f1(z:int)xxx 3"
  )
  , testerror(in, "recursive type problem:", "type testtype is fld1:testtype, fld2:int")
  , testerror(
   in
   , "module testit contains unresolved exports:testit:f1(int, int)int"
   , "Export f1(int, int)int"
  )
  , testerror(in, "Export result type does not match", "Export+(int, int)boolean")
  , testerror(
   in
   , "module testit contains lines that cannot be resolved:use int.notdefined"
   , "use int.notdefined"
  )
  , testerror(in, "module testit contains lines that cannot be resolved:use notdefined", "use notdefined")
  , testerror(in, "Duplicate type definition", "type t1 is a:int /p type t1 is b:int")
  , testerror(in, "Duplicate module name", "Module testit")
 ],
check(z, "test11a") + checkprec

use seq1.boolean

function testcomp2(in:seq.file, s:seq.word) seq.word
let txt = "/p module testit /p use standard /p:(s)"
let p =
 process.compilerFront:callconfig("pass1", [file("a.ls", txt)] + in, "testit", ""),
if aborted.p then message.p
else
 for acc = "", sd ∈ toseq.prg.result.p
 do
  acc
  + "/br /br
  "
  + %.sym.sd
  + %.code.sd,
 acc

function compare(in:seq.file, exp1:seq.word, exp2:seq.word) boolean
testcomp2(in, "Function f1(a:int, b:int, c:int)int:(exp1)")
 = testcomp2(in, "Function f1(a:int, b:int, c:int)int:(exp2)")

function isprefix(p:seq.word, s:seq.word) boolean subseq(s, 1, n.p) = p

function testerror(in:seq.file, m:seq.word, code:seq.word) boolean
let r = testcomp2(in, code)
let a = isprefix(m, r)
assert a report "Fail test11a expected::(m)/br got::(r)/p:(code)",
a

type checkprec is toseq:seq.word

function checkprec seq.word
assert-(1 * 1) - 5 = -6 report "Fail prec"
let a =
 [
  x.1 + {commet should not change assocativity}x.2 + x.3
  , x.1 + x.2 + x.3
  , x.1 * x.2 * x.3
  , (x.1) sup ((x.2) sup x.3)
  , (x.1) sub ((x.2) sub x.3)
  , -x.1 * (x.2) sup x.3
  , x.1 * x.2 + x.3
  , x.1 + x.2 * x.3
  , uni.x.1 * x.2
  , uni.(x.1) sup x.2
  , x.1 + x.2 = x.3
  , x.1 = x.2 + x.3
  , x.1 > x.2 = x.3
  , x.1 = x.2 > x.3
  , x.1 = x.2 ∧ x.3
  , x.1 ∧ x.2 = x.3
  , x.1 ∧ x.2 ∨ x.3
  , x.1 ∨ x.2 ∧ x.3
  , uni.x.1 + x.2
 ]
let b =
 [
  "((1+2)+3)"
  , "((1+2)+3)"
  , "((1 * 2)* 3)"
  , "(1 sup(2 sup 3))"
  , "(1 sub(2 sub 3))"
  , "((-1)*(2 sup 3))"
  , "((1 * 2)+3)"
  , "(1+(2 * 3))"
  , "((uni 1)* 2)"
  , "(uni(1 sup 2))"
  , "((1+2)= 3)"
  , "(1 =(2+3))"
  , "((1 > 2)= 3)"
  , "((1 = 2)> 3)"
  , "((1 = 2)∧ 3)"
  , "(1 ∧(2 = 3))"
  , "((1 ∧ 2)∨ 3)"
  , "(1 ∨(2 ∧ 3))"
  , "((uni 1)+2)"
 ]
for acc = empty:seq.seq.word, e ∈ a do acc + toseq.e,
check(acc, b, "precedence test")

function check(y:seq.seq.word, b:seq.seq.word, testname:seq.word) seq.word
let x =
 for acc = "", i ∈ arithseq(n.y, 1, 1)
 do if y sub i = b sub i then acc else acc + toword.i,
 acc,
if x = "" then "PASS:(testname)" else "<* literal FAILED *> test:(x)in:(testname)"

function x(a:int) checkprec checkprec.[toword.a]

function -(a:checkprec) checkprec checkprec."(-:(toseq.a))"

function uni(a:checkprec) checkprec checkprec."(uni:(toseq.a))"

function sup(a:checkprec, b:checkprec) checkprec checkprec."(:(toseq.a)sup:(toseq.b))"

function sub(a:checkprec, b:checkprec) checkprec checkprec."(:(toseq.a)sub:(toseq.b))"

function *(a:checkprec, b:checkprec) checkprec checkprec."(:(toseq.a)*:(toseq.b))"

function +(a:checkprec, b:checkprec) checkprec checkprec."(:(toseq.a)+:(toseq.b))"

function =(a:checkprec, b:checkprec) checkprec checkprec."(:(toseq.a)=:(toseq.b))"

function >(a:checkprec, b:checkprec) checkprec checkprec."(:(toseq.a)>:(toseq.b))"

function ∧(a:checkprec, b:checkprec) checkprec checkprec."(:(toseq.a)∧:(toseq.b))"

function ∨(a:checkprec, b:checkprec) checkprec checkprec."(:(toseq.a)∨:(toseq.b))" 