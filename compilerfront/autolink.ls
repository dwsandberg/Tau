Module autolink

use standard

use set.autolink

use seq1.word

Export type:autolink

Export file(autolink) seq.word

Export id(autolink) seq.word

function %(s:autolink) seq.word id.s + file.s

Function find(links:set.autolink, id:seq.word) set.autolink
findelement2(links, autolink(id, ""))

Export autolink(id:seq.word, file:seq.word) autolink

Function firstT(s:autolink) int findindex(id.s, "T" sub 1)

type autolink is id:seq.word, file:seq.word

Function >2(a:autolink, b:autolink) ordering
let m = min(firstT.a, firstT.b) - 1,
subseq(id.a, 1, m) >1 subseq(id.b, 1, m)

Function >1(a:autolink, b:autolink) ordering
let m = min(firstT.a, firstT.b) - 1,
subseq(id.a, 1, m) >1 subseq(id.b, 1, m) ∧ id.a >1 id.b ∧ file.a >1 file.b 