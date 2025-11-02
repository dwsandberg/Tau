Module textio

use UTF8

use seq.UTF8

use bits

use seq1.byte

use standard

use toWords

Export type:UTF8 {From UTF8}

Export towords(a:UTF8) seq.word {From toWords}

Export breakparagraph(input:seq.byte) seq.seq.word {From toWords}

Function breaklines(a:UTF8) seq.UTF8 breaklines(toseqbyte.a, 2, 1, empty:seq.UTF8)

Function breaklines(a:seq.byte) seq.UTF8 breaklines(a, 2, 1, empty:seq.UTF8)

function breaklines(a:seq.byte, i:int, last:int, result:seq.UTF8) seq.UTF8
if i > n.a then result
else if toint.a sub i = 10 then
 breaklines(
  a
  , i + 1
  , i + 1
  , result + UTF8.subseq(a, last, i - (if toint.a sub (i - 1) = 13 then 2 else 1))
 )
else breaklines(a, i + 1, last, result)

Function breakcommas(a:UTF8) seq.UTF8
for
 acc = empty:seq.UTF8
 , @e ∈ break(tobyte.toint.char1.",", [tobyte.toint.char1.dq], toseqbyte.a)
do acc + UTF8.@e,
acc 
