#!/usr/local/bin/tau testmodules testmodules

Module testmodules

use UTF8

use bits

use otherseq.char

use seq.char

use checking

use seq.arc.int

use set.arc.int

use graph.int

use myseq.int

use set.int

use tree.int

use seq.ordering

use randomphrase

use standard

use test20

use seq.arc.word

use set.arc.word

use graph.word

use set.word

use seq.tree.word

use tree.word

Function testmodules seq.word
let y = [ t501, t502, t503, t504, t505, t506, t507, test20, t044]
 check(y,"testmodules") + checkbits

function print(a:seq.int)seq.word
 "[" + (for(@e ∈ a, acc ="")list(acc,",", [ toword.@e]))
 + "]"

---

Test trees

function tr1 tree.int tree(56, [ tree.200, tree.1, tree(5, [ tree.4])])

function tr2 tree.int tree(37, [ tr1, tr1])

function t501 boolean [ 56, 200, 3] = [ label.tr1, label.tr1_1, nosons.tr1]

function ?(a:tree.int, b:tree.int)ordering
 subx(a, b, 1, label.a ? label.b ∧ nosons.a ? nosons.b)

function subx(a:tree.int, b:tree.int, i:int, o:ordering)ordering
 if o = EQ ∧ i ≤ nosons.a then
 subx(a, b, i + 1, a_i ? b_i)
 else o

function print(t:tree.word)seq.word
 if nosons.t = 0 then [ label.t]
 else
  [ label.t]
  + if nosons.t = 1 then"." + print.t_1
  else
   "(" + (for(@e ∈ sons.t, acc ="")list(acc,",", print.@e))
   + ")"

function t502 boolean [ GT, EQ, EQ]
= [ tr2_1 ? tr2, tr2_1 ? tr2_2, tr1_2 ? tree.1]

function t503 boolean"a" = print.tree."a"_1

function t504 boolean"a.b" = print.tree("a"_1, [ tree."b"_1])

function n1 int 1

function n2 int 2

function n3 int 3

function n4 int 4

function n5 int 5

function n6 int 6

function n7 int 7

function n8 int 8

function t505 boolean
let g = newgraph
.[ arc(n1, n2), arc(n3, n2), arc(n2, n4), arc(n1, n4), arc(n5, n6), arc(n6, n7), arc(n7, n5), arc(n6, n8), arc(n5, n1)]
let r = print.g + "transversal" + print.sinksfirst.g + "Suc"
+ print.toseq.successors(g, n2)
+ "sinks"
+ print.sinks(g, asset.[ n4], n2)
 r
 = "GRAPH:(1 2)(1 4)(2 4)(3 2)(5 1)(5 6)(6 7)(6 8)(7 5)transversal [ 4, 8, 2, 1, 3]Suc [ 4]sinks [ 2]"

function t506 boolean
let g = newgraph.[ arc(n1, n2), arc(n3, n2), arc(n2, n4)]
let closure = [ arc(n1, n2), arc(n1, n4), arc(n2, n4), arc(n3, n2), arc(n3, n4)]
 closure = toseq.arcs.transitiveClosure.g

function print(g:graph.int)seq.word
 "GRAPH:" + ((for(@e ∈ toseq.arcs.g, acc ="")acc + print.@e))

function print(a:arc.int)seq.word"(" + toword.tail.a + toword.head.a + ")"

_____________

Randomphrase

Function t507 boolean"The umber ant ambles the opal nurse" = getphrase.20

function t044 boolean
let s = UTF8.[ 40, 50] + encodeUTF8.char.335 + encodeUTF8.char.50 + encodeUTF8.char.336
let z = myseq.((for(@e ∈ toseqbyte.s, acc = empty:seq.int)acc + toint.@e))
 {((for(@e ∈ z, acc ="")acc + toword.@e)) = "40 50 335 50 336"
 ∧ length.toseq.to:myseq.int(z) ≠ 0
 ∧ length.toseq.to:myseq.int([ 1, 2, 3]) = 0 }

_____________

bits

Function checkbits seq.word 
    let min64integer=toint(0x1 << 63 )
     let max64integer=toint( bits.-1 >> 1)
 check([toint.toword.min64integer=min64integer 
       , toint.toword.max64integer=max64integer  
      , min64integer+1 =-max64integer 
      , 0xD=bits.13, 
 878082210 = toint.rotl32(0xA2345678, 8) ,  
 print(0xD687F000 ∧ 0x0FE00000) = "0000 0000 0680 0000", 
 print(0xD687F001 >> 2) = "0000 0000 35A1 FC00", 
  print(0xD687F001 << 2) = "0000 0003 5A1F C004",
  print(0xD687F000 ∨ 0x0FE00000) = "0000 0000 DFE7 F000", 
  print.xor(0xD687F000, 0x0FE00000) = "0000 0000 D967 F000"]
,"bits")

function rotl32(x:bits, n:int)bits bits.4294967295 ∧ (x << n ∨ x >> (32 - n))