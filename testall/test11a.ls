Module test11a

run test11a test11a

use checking

use main2

use process.seq.seq.word

use seq.boolean

use seq.word

use stdlib

use blockseq.int

Function test11a seq.word // testcomp2.["module testit","use stdlib","function f1(a:int)boolean [ a +"]//
let z = [ compare("a + b + c","{(a + b)+ c }")
, compare("a*b*c","{(a*b)*c }")
, compare("a + b*c","{(a +(b*c)}")
, compare("-a + b","{(-a)+ b }")
, compare("a +-b","{ a +(-b)}")
, compare("a^2 + b","(a^2)+ b")
, compare("length.[ 1, 2]","length([ 1, 2])")
, compare("{ a + b } * c","{(a + b)* c }")
, testerror("ERR parse error expect:)> got:end of paragraph", ["function f1(a:int)boolean(a"])
, testerror("ERR parse error expect:)> got:end of paragraph", ["function f1(a:int)boolean(a"])
, // 11 //
testerror("ERR parse error expect:]), > got:end of paragraph", ["function f1(a:int)boolean [ a"])
, testerror("ERR parse error expect:N(I @ W A $wordlist assert { E > comment if [ let got:end of paragraph", ["function f1(a:int)boolean [ a +"])
, testerror("ERR Function f1 is defined twice in module testit", ["function f1(a:int)int 3","function f1(a:int)int 3"])
, testerror("ERR then and else types are different", ["function f1(a:int)int if true then true else 0"])
, testerror("ERR cond of if must be boolean", ["function f1(a:int)int if 1 then 2 else 3"])
, testerror("ERR condition in assert must be boolean", ["function f1(a:int)int assert 1 report 2 3"])
, testerror("ERR report in assert must be seq of word in:", ["function f1(a:int)int assert true report 2 3"])]
 check(z,"test11a")

Function testcomp2(s:seq.seq.word)seq.word
 let p = process.testcomp.s
  if aborted.p then"ERR" + message.p else @(+, +("&br &br"),"", result.p)

Function compare(exp1:seq.word, exp2:seq.word)boolean
 let e1 = testcomp2
 .["module testit","use stdlib","function f1(a:int, b:int, c:int)int" + exp1]
 let e2 = testcomp2
 .["module testit","use stdlib","function f1(a:int, b:int, c:int)int" + exp2]
 let i1 = findindex("f1ZtestitZintZintZint"_1, e1)
 let i2 = findindex("f1ZtestitZintZintZint"_1, e2)
  subseq(e1, i1, length.e1) = subseq(e2, i2, length.e2)

Function isprefix(p:seq.word, s:seq.word)boolean subseq(s, 1, length.p) = p

Function testerror(m:seq.word, code:seq.seq.word)boolean
 isprefix(m, testcomp2.(["module testit","use stdlib"] + code))