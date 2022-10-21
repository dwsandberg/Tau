Module testall

use bug7

use checking

use real

use standard

use test11

use test11a

use testencoding

use testmodules

use testopt

use testprocess

use testseq

use wordfreq

use file

use seq.file

use words

function checkhash seq.word
if for l = empty:seq.int
, w ∈ "Xx 0123456789ABCDEFabcdef x X invalid hex digit 0123456789-MMMM out of bounds FAIL >>, ()].:
 $(dq)_^.384 52 3 [2 4 5 a b c d e 1 k+= {} 1 2∪ this is test three four five test11 0 SPACE 2∪ code glyph
 48 49 50 51 53 54 6"
do l + hash.decodeword.w /for (l)
= [1606469939, 3611716215, 3408990482, 2398569529, 1805514831
, 2794507078, 3153899467, 1592536390, 2267580998, 4148795192
, 2029448469, 1396446841, 658738060, 3120177018, 3341416014
, 1266385772, 325494510, 3005281154, 617705625, 2870816891
, 4219009543, 96972925, 714369044, 3819677413, 2870816891
, 1622155845, 1417601429, 1014894877, 2324271868, 3315521267
, 1525021788, 3984862306, 913100485, 1158069397, 3808679991
, 2091334196, 1652413900, 2868552774, 1794352742, 1610307643
, 1580542844, 3320712500, 2023892724, 2868552774, 2452762837
, 163570344, 2277441105, 1523094486, 3839835005, 3432885615
, 1589295501, 3706078705, 1368117822, 3599514040, 2452762837
, 2334702418, 3286754921, 3824978816, 1228719631, 3076839954
, 4069144071, 3003840284, 1334193844, 2353842011] then
 "PASS hash"
else "Fail hash"

Function testall(input:seq.file, o:seq.word, noseq:boolean) seq.file
let out = 
 test11 + checkhash + testencoding + testmodules + testbug7 + randomtest.500
 + testreal
 + if noseq then "" else testseq /if
 + test11a.input
 + testwordfreq
 + testprocess
 + if isempty.input then "no opt test file specified" else testopt.input
[file(filename.o, out)] 