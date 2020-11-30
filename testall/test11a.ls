#!/usr/local/bin/tau ; use test11a ; test11a

Module test11a

use seq.boolean

use checking

use main2

use stdlib

use process.seq.seq.word

use seq.word

Function test11a seq.word // testcomp2.["module testit","use stdlib","function f1(a:int)boolean [ a +"]//
let z = [ compare("a + b + c","{(a + b)+ c }")
, compare("a * b * c","{(a * b)* c }")
, compare("a + b * c","a +(b * c)")
, compare("-a + b","{(-a)+ b }")
, compare("a +-b","{ a +(-b)}")
, compare("a^2 + b","(a^2)+ b")
, compare("length.[ 1, 2]","length([ 1, 2])")
, compare("{ a + b } * c","{(a + b)* c }")
, testerror("parse error:unexpected end of paragraph", ["function f1(a:int)boolean(a"])
, testerror("parse error:unexpected end of paragraph", ["function f1(a:int)boolean [ a"])
, testerror("parse error:unexpected end of paragraph", ["function f1(a:int)boolean [ a +"])
, testerror("Function f1 is defined twice in module testit", ["function f1(a:int)int 3","function f1(a:int)int 3"])
, testerror("then and else types are different", ["function f1(a:int)int if true then true else 0"])
, testerror("cond of if must be boolean", ["function f1(a:int)int if 1 then 2 else 3"])
, testerror("condition in assert must be boolean", ["function f1(a:int)int assert 1 report 2 3"])
, testerror("report in assert must be seq of word in:", ["function f1(a:int)int assert true report 2 3"])
, testerror("parameter type hhh is undefined", ["function f1(z:hhh)int 3"])
, testerror("parameter type xxx is undefined", ["function f1(z:int)xxx 3"])
, testerror("unresolved types:module:testit type testtype is record fld1:testtype", ["type testtype is record fld1:testtype"])
, testerror("unresolved exports", ["Export f1(int, int)int "])
, testerror("export return type missmatch", ["Export +(int, int)boolean "])
, testerror("Cannot find module", ["use int.notdefined"])
, testerror("Cannot find module", ["use notdefined"])]
 check(z,"test11a")

Function testcomp2(s:seq.seq.word)seq.word
 let p = process.testcomp.s
  if aborted.p then message.p else @(+, +." &br  &br","", result.p)

Function compare(exp1:seq.word, exp2:seq.word)boolean
 let e1 = testcomp2
 .["module testit","use stdlib","Function f1(a:int, b:int, c:int)int" + exp1]
 let e2 = testcomp2
 .["module testit","use stdlib","Function f1(a:int, b:int, c:int)int" + exp2]
 let i1 = findindex("f1ZtestitZintZintZint"_1, e1)
 let i2 = findindex("f1ZtestitZintZintZint"_1, e2)
  e1 = e2

Function isprefix(p:seq.word, s:seq.word)boolean subseq(s, 1, length.p) = p

Function testerror(m:seq.word, code:seq.seq.word)boolean
 let r = testcomp2(["module testit","use stdlib"] + code)
 let a = isprefix(m, r)
  assert isprefix(m, r)report"Fail test11a expected:" + m + " &br got:" + subseq(r, 1, length.m)
   a