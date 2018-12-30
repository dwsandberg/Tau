#!/usr/local/bin/tau

Module test11a

run test11a test11a

use checking

use main2

use process.seq.seq.word

use seq.boolean

use seq.word

use stdlib

Function test11a seq.word 
 let z = [ compare("a + b + c","{(a + b)+ c }"), 
  compare("a*b*c","{(a*b)*c }"), 
  compare("a + b*c","{(a +(b*c)}"), 
  compare("-a + b","{(-a)+ b }"), 
  compare("a +-b","{ a +(-b)}"), 
  compare("a^2 + b","(a^2)+ b"), 
  compare("length.[ 1, 2]","length([ 1, 2])"), 
  compare("{ a + b } * c","{(a + b)* c }"), 
  "ERR parse error expect:)> got:end of paragraph &br &keyword function f1(a:int)boolean(a"= testcomp2.["module testit","use stdlib","function f1(a:int)boolean(a"]∧"ERR parse error expect:)>], got:end of paragraph &br &keyword function f1(a:int)boolean [ a"= testcomp2.["module testit","use stdlib","function f1(a:int)boolean [ a"]∧"ERR parse error expect:(> { comment [ if let assert $wordlist @ A E W N I got:end of paragraph &br &keyword function f1(a:int)boolean [ a +"= testcomp2.["module testit","use stdlib","function f1(a:int)boolean [ a +"]]
  check(z,"test11a")

Function testcomp2(s:seq.seq.word)seq.word 
 let p = process.testcomp.s 
  if aborted.p 
  then"ERR"+ message.p 
  else @(+, +."&br &br","", result.p)

Function compare(exp1:seq.word, exp2:seq.word)boolean 
 let e1 = testcomp2.["module testit","use stdlib","function f1(a:int, b:int, c:int)int"+ exp1]
  let e2 = testcomp2.["module testit","use stdlib","function f1(a:int, b:int, c:int)int"+ exp2]
  let i1 = findindex("f1ZtestitZintZintZint"_1, e1)
  let i2 = findindex("f1ZtestitZintZintZint"_1, e2)
  subseq(e1, i1, length.e1)= subseq(e2, i2, length.e2)


