Module testDifferentTypes

Types with same name in differnt modules

use seq.word

type bug17 is part1:word, part2:word

use set.bug17

use standard

use otherseq.bug17

function %(a:bug17) seq.word [part1.a, part2.a]

function >1(a:bug17, b:bug17) ordering part1.a >1 part1.b ∧ part2.a >1 part2.b

function >2(a:bug17, b:bug17) ordering part1.a >1 part1.b

use testDifferentTypesB

Function testDiffTypes seq.word
if
 AA."H" + "/p" + BB."HH"
  = "set order: a B, a A, b H, b J, lookup:b H findelement2:b H b J
 /p set order: a B, a A, b J, b HH, lookup:b HH findelement2:b J b HH"
then
"Pass testDifferentTypes"
else "Fail testDifferentTypes"

function AA(w:seq.word) seq.word
let last = bug17(1#"b", 1#w)
let data = asset.[bug17(1#"a", 1#"A"), bug17(1#"a", 1#"B"), bug17(1#"b", 1#"J"), last],
"set order: ^(%(",", toseq.data)) lookup:^(toseq.lookup(data, last)) findelement2:
^(toseq.findelement2(data, last))" 