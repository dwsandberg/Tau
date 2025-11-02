Module testDifferentTypes

Types with same name in differnt modules

use seq.word

type bug17 is part1:word, part2:word

use set.bug17

use standard

use seq1.bug17

function %(a:bug17) seq.word [part1.a, part2.a]

function >1(a:bug17, b:bug17) ordering part1.a >1 part1.b ∧ part2.a >1 part2.b

function >2(a:bug17, b:bug17) ordering part1.a >1 part1.b

use testDifferentTypesB

Function testDiffTypes seq.word
if AA."H" + "/p" + BB."HH"
= "set order: a B, a A, b H, b J, lookup:b H findelement2:b H b J
/p set order: a B, a A, b J, b HH, lookup:b HH findelement2:b J b HH" then "Pass testDifferentTypes"
else "Fail testDifferentTypes"

function AA(w:seq.word) seq.word
let last = bug17("b" sub 1, w sub 1)
let data =
 asset.[
  bug17("a" sub 1, "A" sub 1)
  , bug17("a" sub 1, "B" sub 1)
  , bug17("b" sub 1, "J" sub 1)
  , last
 ],
"set order: :(%(",", toseq.data)) lookup::(toseq.lookup(data, last)) findelement2::(toseq.findelement2(data, last))" 
