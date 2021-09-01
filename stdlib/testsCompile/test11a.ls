
Module test11a

use checking

use main2

use standard

use seq.boolean

use seq.checkprec

use process.seq.seq.word

Function test11a seq.word let z = [ compare("a + b + c","(a + b)+ c")
, compare("a * b * c","(a * b)* c")
, compare("a + b * c","a +(b * c)")
, compare("-a + b","(-a)+ b")
, compare("a +-b","a +(-b)")
, compare("a^2 + b","(a^2)+ b")
, compare("length.[ 1, 2]","length([ 1, 2])")
, testerror(" /< literal parse error:unexpected end of paragraph  />", ["function f1(a:int)boolean(a"])
, testerror(" /< literal parse error:unexpected end of paragraph  />", ["function f1(a:int)boolean [ a"])
, testerror(" /< literal parse error:unexpected end of paragraph  />", ["function f1(a:int)boolean [ a +"])
, testerror("Function f1 is defined twice in module testit", ["function f1(a:int)int 3","function f1(a:int)int 3"])
, testerror(" /< literal then and else types are different  />", ["function f1(a:int)int if true then true else 0"])
, testerror(" /< literal cond of if must be boolean but is int />", ["function f1(a:int)int if 1 then 2 else 3"])
, testerror(" /< literal condition in assert must be boolean", ["function f1(a:int)int assert 1 report 2 3"])
, testerror(" /< literal report in assert must be seq of word in:", ["function f1(a:int)int assert true report 2 3"])
, testerror(" /< literal cannot resolve type hhh ", ["function f1(z:hhh)int 3"])
, testerror(" /< literal cannot resolve type xxx ", ["function f1(z:int)xxx 3"])
, testerror("recursive type problem: ", ["type testtype is fld1:testtype"])
, testerror("module testit contains unresolved exports: testit:f1(int, int)int", ["Export f1(int, int)int"])
, testerror("Export result type does not match", ["Export +(int, int)boolean"])
,  testerror("module testit contains lines that cannot be resolved:use int.notdefined", ["use int.notdefined"])
, testerror("module testit contains lines that cannot be resolved:use notdefined", ["use notdefined"])
]
 check(z,"test11a") + checkprec
 
 use symbol2
 
 use process.compileinfo

Function testcomp2(s:seq.seq.word)seq.word
let p = process.compilerfront("pass1", "testcomp",s,"stdlib","testit")
 if aborted.p then message.p
 else
  for acc ="", @e = astext.result.p do acc + " /br  /br" + @e /for(acc)

Function compare(exp1:seq.word, exp2:seq.word)boolean
let e1 = testcomp2.["module testit","use standard","Function f1(a:int, b:int, c:int)int" + exp1]
let e2 = testcomp2.["module testit","use standard","Function f1(a:int, b:int, c:int)int" + exp2]
let i1 = findindex("f1ZtestitZintZintZint"_1, e1)
let i2 = findindex("f1ZtestitZintZintZint"_1, e2)
 e1 = e2

Function isprefix(p:seq.word, s:seq.word)boolean subseq(s, 1, length.p) = p

Function testerror(m:seq.word, code:seq.seq.word)boolean
let r = testcomp2(["module testit","use standard"] + code)
let a = isprefix(m, r)
 assert isprefix(m, r)report"Fail test11a expected:" + m + " /br got:" + subseq(r, 1, length.m)
  a

type checkprec is toseq:seq.word

Function checkprec seq.word assert-(1 * 1) - 5 = -6 report"Fail prec"
let a = [ x.1 + { should not change assocativity } x.2 + x.3, x.1 + x.2 + x.3, x.1 * x.2 * x.3,(x.1)^(x.2)^(x.3),(x.1)_(x.2)_(x.3),-x.1 * (x.2)^(x.3), x.1 * x.2 + x.3, x.1 + x.2 * x.3, uni.x.1 * x.2, uni.(x.1)^(x.2)
, x.1 + x.2 = x.3, x.1 = x.2 + x.3,(x.1 > x.2) = x.3, x.1 = x.2 > x.3, x.1 = x.2 ∧ x.3, x.1 ∧ x.2 = x.3, x.1 ∧ x.2 ∨ x.3, x.1 ∨ x.2 ∧ x.3, uni.x.1 + x.2]
let b = ["((1 + 2)+ 3)","((1 + 2)+ 3)","((1 * 2)* 3)","((1^2)^3)","((1_2)_3)","((-1)*(2^3))","((1 * 2)+ 3)","(1 +(2 * 3))","((uni 1)* 2)","(uni(1^2))"
,"((1 + 2)= 3)","(1 =(2 + 3))","((1 > 2)= 3)","((1 = 2)> 3)","((1 = 2)∧ 3)","(1 ∧(2 = 3))","((1 ∧ 2)∨ 3)","(1 ∨(2 ∧ 3))","((uni 1)+ 2)"]
 check(for acc = empty:seq.seq.word, @e = a do acc + toseq.@e /for(acc), b,"precedence test")

function check2(l:seq.seq.word, b:seq.seq.word, i:int)seq.word
 if l_i = b_i then""else [ toword.i]

Function check(y:seq.seq.word, b:seq.seq.word, testname:seq.word)seq.word
let x = for acc ="", @e = arithseq(length.y, 1, 1)do acc + check2(y, b, @e)/for(acc)
 if x = ""then"PASS" + testname
 else" /< literal FAILED  /> test" + x + "in" + testname

function x(a:int)checkprec checkprec.[ toword.a]

function-(a:checkprec)checkprec checkprec("(-" + toseq.a + ")")

function uni(a:checkprec)checkprec checkprec("(uni" + toseq.a + ")")

function^(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + "^" + toseq.b + ")")

function_(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + "_" + toseq.b + ")")

function *(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + "*" + toseq.b + ")")

Function bi(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + "!" + toseq.b + ")")

function +(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + "+" + toseq.b + ")")

function =(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + "=" + toseq.b + ")")

function >(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + ">" + toseq.b + ")")

function ∧(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + "∧" + toseq.b + ")")

function ∨(a:checkprec, b:checkprec)checkprec
 checkprec("(" + toseq.a + "∨" + toseq.b + ")")