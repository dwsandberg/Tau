Module testDifferentTypesB

use file

use seq.file

use seq.word

use seq.filename

type bug17 is part1:word, part2:word

use set.bug17

use standard

use otherseq.bug17

function %(a:bug17) seq.word [part1.a, part2.a]

function >1(a:bug17, b:bug17) ordering part1.a >1 part1.b ∧ part2.a >1 part2.b

function >2(a:bug17, b:bug17) ordering part1.a >1 part1.b

Function BB(w:seq.word) seq.word
let last = bug17(1#"b", 1#w)
let data =
 asset.[
  bug17(1#"a", 1#"A")
  , bug17(1#"a", 1#"B")
  , bug17(1#"b", 1#"J")
  , last
 ],
"set order: ^(%(",", toseq.data)) lookup:^(toseq.lookup(data, last)) findelement2:^(toseq.findelement2(data, last))" 