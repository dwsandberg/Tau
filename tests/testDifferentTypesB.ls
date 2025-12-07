Module testDifferentTypesB

use file

use seq.file

use seq.word

use seq.filename

type bug17 is part1:word, part2:word

use set.bug17

use standard

use seq1.bug17

function %(a:bug17) seq.word [part1.a, part2.a]

function >1(a:bug17, b:bug17) ordering part1.a >1 part1.b ∧ part2.a >1 part2.b

function >2(a:bug17, b:bug17) ordering part1.a >1 part1.b

Function BB(w:seq.word) seq.word
let last = bug17("b" sub 1, w sub 1)
let data =
 asset.[
  bug17("a" sub 1, "A" sub 1)
  , bug17("a" sub 1, "B" sub 1)
  , bug17("b" sub 1, "J" sub 1)
  , last
 ],
 "set order: :(%(",", toseq.data))lookup::(toseq.lookup(data, last))findelement2::(toseq.findelement2(data, last))" 