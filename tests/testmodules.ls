Module testmodules

use UTF8

use bits

use checking

use arc.int

use graph.arc.int

use seq1.arc.int

use set.arc.int

use myseq.int

use seq1.int

use set.int

use tree.int

use seq1.tree.int

use seq.ordering

use randomphrase

use standard

use test20

use tree.word

Function testmodules seq.word
let y =
 [
  t501
  , t502
  , t503
  , t504
  , t505
  , t506
  , testrandomphrase
  , t508
  , test20
  , t044
  , "200:1:4:5.4:56 (200, 1, 5.4):" = %(":", postorder.tr1)
 ],
check(y, "testmodules") + checkbits

function print(a:seq.int) seq.word
"[:(for acc = "", @e ∈ a do acc + toword.@e + ",",
acc >> 1)]"

---

Test trees

function tr1 tree.int tree(56, [tree.200, tree.1, tree(5, [tree.4])])

function tr2 tree.int tree(37, [tr1, tr1])

function t501 boolean [56, 200, 3] = [label.tr1, label.tr1 sub 1, nosons.tr1]

function >1(a:tree.int, b:tree.int) ordering
subx(a, b, 1, label.a >1 label.b ∧ nosons.a >1 nosons.b)

function subx(a:tree.int, b:tree.int, i:int, o:ordering) ordering
if o = EQ ∧ i ≤ nosons.a then subx(a, b, i + 1, a sub i >1 b sub i) else o

function t502 boolean
[GT, EQ, EQ] = [tr2 sub 1 >1 tr2, tr2 sub 1 >1 tr2 sub 2, tr1 sub 2 >1 tree.1]

function t503 boolean "a" = %.tree."a" sub 1

function t504 boolean "a.b" = %.tree("a" sub 1, [tree."b" sub 1])

function n1 int 1

function n2 int 2

function n3 int 3

function n4 int 4

function n5 int 5

function n6 int 6

function n7 int 7

function n8 int 8

function t505 boolean
let g =
 newgraph.[
  arc(n1, n2)
  , arc(n3, n2)
  , arc(n2, n4)
  , arc(n1, n4)
  , arc(n5, n6)
  , arc(n6, n7)
  , arc(n7, n5)
  , arc(n6, n8)
  , arc(n5, n1)
 ]
{assert false report" K"+%.sources (g)}
let r = "GRAPH::(toseq.arcs.g) Succ:(toseq.successors(g, n2)) Pred:(toseq.predecessors(g, n4)) sinks:(sinks(g, asset.[n5])) sources:(sources.g)",
r
= "GRAPH:"
 + "(1 2) (1 4) (2 4) (3 2) (5 1) (5 6) (6 7) (6 8) (7 5) Succ 4 Pred 1 2 sinks 4 7 8 sources 3"

function t506 boolean
let g = newgraph.[arc(n1, n2), arc(n3, n2), arc(n2, n4)]
let closure = [arc(n1, n2), arc(n1, n4), arc(n2, n4), arc(n3, n2), arc(n3, n4)],
closure = toseq.arcs.transitiveClosure.g

function =(a:arc.int, b:arc.int) boolean head.a = head.b ∧ tail.a = tail.b

function %(a:arc.int) seq.word "(:(tail.a):(head.a))"

function t508 boolean
for
 s = constantseq(100, 0)
 , i ∈ for acc = empty:seq.int, e ∈ randomseq(3456, 100001)
 do acc + (abs.e mod 100 + 1),
 acc
do replace(s, i, s sub i + 1)
for totalcounts = 0, e ∈ s do totalcounts + e,
n.s = 100 ∧ totalcounts = 100001

-------------------------------

Randomphrase

function testrandomphrase boolean "The short tomato adds the ghastly year" = getphrase.20

function t044 boolean
let s = UTF8.[tobyte.40, tobyte.50] + encodeUTF8.char.335 + encodeUTF8.char.50 + encodeUTF8.char.336
for acc = empty:seq.int, @e ∈ toseqbyte.s
do acc + toint.@e
let z = tomyseq.acc
for acc2 = "", @e ∈ toseq.z do acc2 + toword.@e,
acc2 = "40 50 335 50 336" ∧ n.z = 5 ∧ z sub 4 = 50 ∧ n.tomyseq.[1, 2, 3] = 3

-------------------------------

bits

Function checkbits seq.word
let min64integer = toint(0x1 << 63)
let max64integer = toint(bits.-1 >> 1),
check(
 [
  toint.toword.min64integer = min64integer
  , toint.toword.max64integer = max64integer
  , min64integer + 1 =-max64integer
  , 0xD = bits.13
  , 878082210 = toint.rotl32(0xA2345678, 8)
  , %(0xD687F000 ∧ 0x0FE00000) = "0000 0000 0680 0000"
  , %(0xD687F001 >> 2) = "0000 0000 35A1 FC00"
  , %(0xD687F001 << 2) = "0000 0003 5A1F C004"
  , %(0xD687F000 ∨ 0x0FE00000) = "0000 0000 DFE7 F000"
  , %(0xD687F000 ⊻ 0x0FE00000) = "0000 0000 D967 F000"
 ]
 , "bits"
)

function rotl32(x:bits, n:int) bits bits.4294967295 ∧ (x << n ∨ x >> (32 - n)) 
