#!/usr/local/bin/tau

run testmodules testmodules

Module testmodules

use graph.word

use seq.arc.word

use set.arc.word

use set.word

use stdlib

use tree.int

use tree.word

use seq.tree.word

use seq.ordering

use checking

use seq.arc.int

use set.arc.int

use graph.int

use set.int

use randomphrase

use test20


Function testmodules seq.word 
 let y = [  t501, t502,t503,t504,t505,t506,t507,test20]
   check(y,"testmodules")
   
function print(a:seq.int)seq.word 
 "["+ @(seperator(","), toword,"", a)+"]"

   
---

Test trees

function tr1 tree.int tree(56, [ tree.200, tree.1, tree(5, [ tree.4])])

function tr2 tree.int tree(37, [ tr1, tr1])

Function t501 boolean [ 56, 200, 3]= [ label.tr1, label.tr1_1, nosons.tr1]

function ?(a:tree.int, b:tree.int)ordering subx(a, b, 1, label.a ? label.b ∧ nosons.a ? nosons.b)

function subx(a:tree.int, b:tree.int, i:int, o:ordering)ordering 
 if o = EQ ∧ i ≤ nosons.a then subx(a, b, i + 1, a_i ? b_i)else o

function print(t:tree.word)seq.word 
 if nosons.t = 0 
  then [ label.t]
  else [ label.t]+(
   if nosons.t = 1 
   then"."+ print.t_1 
   else"("+ @(seperator(","), print,"", sons.t)+")")

Function t502 boolean [ GT, EQ, EQ]= [ tr2_1 ? tr2, tr2_1 ? tr2_2, tr1_2 ? tree.1]

Function t503 boolean"a"= print.tree."a"_1

Function t504 boolean"a.b"= print.tree("a"_1, [ tree."b"_1])


Function n1 int 1

Function n2 int 2

Function n3 int 3

Function n4 int 4

Function n5 int 5

Function n6 int 6

Function n7 int 7

Function n8 int 8

function  t505 boolean 
 let g = newgraph.[ arc(n1, n2)
  , arc(n3, n2)
  , arc(n2, n4)
  , arc(n1, n4)
  , arc(n5, n6)
  , arc(n6, n7)
  , arc(n7, n5)
  , arc(n6, n8)
  , arc(n5, n1)]
  let r = print.g +"transversal"+ print.sinksfirst.g +"Suc"+ print.toseq.successors(g, n2)+"sinks"
  + print.sinks(g, asset.[ n4], n2)
   r ="GRAPH:(1 2)(1 4)(2 4)(3 2)(5 1)(5 6)(6 7)(6 8)(7 5)transversal [ 4, 8, 2, 1, 3]Suc [ 4]sinks [ 2]"

function t506 boolean 
 let g = newgraph.[ arc(n1, n2), arc(n3, n2), arc(n2, n4)]
  let closure = [ arc(n1, n2), arc(n1, n4), arc(n2, n4), arc(n3, n2), arc(n3, n4)]
   closure = toseq.arcs.transitiveClosure.g

function print(g:graph.int)seq.word"GRAPH:"+ @(+, print,"", toseq.arcs.g)

function print(a:arc.int)seq.word"("+ toword.tail.a + toword.head.a +")"

_____________

Randomphrase

Function t507 boolean"The umber ant ambles the opal nurse"= getphrase.20



