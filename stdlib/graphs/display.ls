Module display

use UTF8

use standard

use seq.char

use otherseq.int

use seq.int

use sparseseq.int

use otherseq.word

use seq.word

use seq.seq.word

use seq.seq.seq.word

/use words

Export type:characterwidths s

type characterwidths is widths:seq.int

function_(s:seq.int, c:char)int if toint.c = 0 then 0 else s_(toint.c)

Function displaywidth(cw:characterwidths, s:seq.word)int
 \\ does not account for spaces \\ for @e ∈ s, acc = 0 ,,, acc + displaywidth(cw, @e)

Function displaywidth(cw:characterwidths, w:word)int for @e ∈ decodeword.w, acc = 0 ,,, acc + (widths.cw)_@e

Function charwidths characterwidths characterwidths.replaceS(sparseseq.60
, 1
, [ 60, 60, 60, 60, 60, 60, 60, 60, 60, 60
, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60
, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60
, 60, 50, 43, 53, 64, 64, 103, 100, 30, 43
, 43, 64, 72, 33, 43, 33, 36, 64, 60, 64
, 64, 64, 64, 64, 64, 64, 64, 36, 36, 72
, 72, 72, 57, 108, 93, 86, 86, 93, 78, 72
, 93, 93, 43, 50, 92, 78, 114, 93, 93, 72
, 93, 86, 72, 78, 93, 93, 122, 93, 93, 78
, 43, 36, 43, 60, 65, 43, 57, 64, 57, 64
, 58, 40, 64, 64, 36, 36, 64, 36, 100, 64
, 64, 64, 64, 43, 50, 36, 64, 64, 93, 64
, 64, 57, 62, 26, 62, 70])

Function checkwidths seq.word for @e ∈ arithseq(128 - 32, 1, 32), acc ="",,, list(acc," &br", check.@e)

function check(i:int)seq.word
 let a = encodeword.tocharseq.constantseq(100, i)
 let l = displaywidth(charwidths, a)
  [ a] + toword.l + " &br" + merge.constantseq(l / 100,"m"_1)