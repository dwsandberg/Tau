#!/usr/local/bin/tau

Module test11a

run test11a test11a

use fileio



use process.tree.word

use seq.boolean

use seq.int

use seq.ordering

use seq.seq.seq.word

use seq.tree.int

use seq.tree.word

use seq.word

use stdlib

use textio

use tree.int

use tree.word

function tr1 tree.int tree(56, [ tree.200, tree.1, tree(5, [ tree.4])])

function tr2 tree.int tree(37, [ tr1, tr1])

Function t401 boolean [ 56, 200, 3]= [ label.tr1, label(tr1_1), nosons.tr1]

function ?(a:tree.int, b:tree.int) ordering
    subx( a,b, 1,label.a ? label.b  &and nosons.a ? nosons.b) 
    
function subx(a:tree.int,b:tree.int,i:int,o:ordering) ordering
 if o = EQ  &and i &le nosons.a then
   subx(a,b,i+1, a_i ? b_i)
 else o 

Function t402 boolean 
[ GT, EQ, EQ]= [ tr2_1 ? tr2, tr2_1 ? tr2_2, tr1_2 ? tree(1)]

Function t403 boolean {"a"= print.tree("a"_1)}

Function t404 boolean {"a.b"= print.tree("a"_1, [ tree("b"_1)])}

Function t405 boolean {"a(ab, b)"= print.expression."a(ab, b)#"}

Function t406 boolean {"*(*(3, 5), 8)"= print.expression."3 * 5 * 8 #"}

Function t407 boolean 
 {"+(+(a, *(*(4, b(c, b)), 5)), 8)"= print.expression."a + 4 * b(c, b)* 5 + 8 #"}

Function t408 boolean {"3"= print.expression."3 #"}

Function t409 boolean 
 {"if(=(a, 1), +(b, 3), +(c, 4))"= print.expression."if a = 1 then b + 3 else c + 4 #"}

test apply

Function t410 boolean 
 {"@(+, b.+(a, 3), g, $build(c, d, e))"= print.expression."@(+, b(a + 3), g, [ c, d, e])#"}

Function t411 boolean 
 {"@(+, b, g, $build(c, d, e))"= print.expression."@(+, b, g, [ c, d, e])#"}

Function t412 boolean 
 {"+(comment(4, this, is, a, comment), 8)"= print.expression."// this is a comment // 4 + 8"}
 
 Function t413 boolean 
 {"let(a, makereal(45, 1), let(b, *(a, a), +(b, 3)))"= print.expression."let a = 4.5 let b = a * a b + 3"}



Function prefix(p:seq.word, d:seq.word)boolean subseq(d, 1, length.p)= p

function parse(x:seq.word)tree.word  tree("xxx"_1) 

function print(t:tree.word) seq.word  if nosons.t=0 then [label.t]
else [label.t]+if nosons.t=1 then "."+print(t_1)
else  "("+@(seperator(","),print,"",sons.t)+")"

function expression(s:seq.word) tree.word tree("xxx"_1)


Function t414 boolean @(∧, filetest, true, arithseq(9, 1, 4))

Function t415 boolean @(-, identity, 100, [ 1, 2])= 97

Function t416 boolean // testing UNICODE to word conversion and no-break space in integer 8746 //
decode("1 2∪"_1) = [49, 160 ,50, 87 46 ] 

/Function prettytext(s:seq.word)seq.word prettyexpression.s

Function test23 seq.seq.word ["k"]

@(+, prettytext, empty:seq.seq.word, ["(@ a b c d)","s_i^2","(a / b)-(c / d)","a * b + c","a + b + c","a + b * c"+"(a + b)* c","a +(b + c)","(a + b)*(c + d)","s(3)_(i + 1)","(@ a b c d)+ 3","[ 1, 3, 4]","(if a = b * c then a + b else a-b)+ r","""ab""+""(c + b)""","Z +(if C then A else B)+ s","-(a + b)","-a^2","-a","-a + b","b(a)","b(a + b)","a(b(c))","a(b(c)^2)","a(b(c^2))","input(r)_n(r)"])

Function test24 seq.seq.word ["k"]

@(+, prettyparagraph, empty:seq.seq.word, ["Function space seq(word)[ encodeword.[ 32]]","function f1(u:int, y:seq(real))int 1","type r1 is struct input:seq(word), n:int, tr:seq(tree(word))","type bb is encoding seq(int)","Function f3(int, b:real)seq(word)export"])

function filetest(i:int)boolean 
 let name ="test"+ toword.i +".txt"
  let a = createbytefile(name, arithseq(i, 1, 48))
  fileexists.name ∧ i = length.getfile.name

Function test11a seq.word 
 let z = [ t401, 
  t402, 
  t403, 
  t404, 
  t405, 
  t406, 
  t407, 
  t408, 
  t409, 
  t410, 
  t411, 
  t412, 
  t413, 
  t414, 
  t415, 
  t416,
  "EXPECTED)&br &keyword function a boolean(a #"= message.process.parse."function a boolean(a", 
  "EXPECTED]&br &keyword function a boolean [ a)"= message.process.parse."function a boolean [ a)", 
  "EXPECTED)&br &keyword function a boolean(a +"= message.process.parse."function a boolean(a +", 
  "EXPECTED)&br &keyword function a boolean(a +"= message.process.parse."function a boolean(a +,", 
  "EXPECTED)&br &keyword function a boolean(a +"= message.process.parse."function a boolean(a +)", 
  "EXPECTED)&br &keyword function a boolean(a +"= message.process.parse."function a boolean(a +]"]
  let a = @(+, check.z,"", arithseq(length.z, 1, 1))
  if a =""then"PASS test11a"else"FAIL test11a"+ a

function check(l:seq.boolean, i:int)seq.word 
 if l_i then""else [ toword.i]

------------------------------------

