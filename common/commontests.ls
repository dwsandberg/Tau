Module commontests

use UTF8

use file

use matrix

use point

use real

use standard

use timestamp

use graph.word

use set.word

use wordgraph

Function testcommon(input:seq.file) seq.word
{ENTRYPOINT}
let a = point(7.000, 9.000, 11.000) = translate.point(6.0, 7.0, 8.0) * point(1.0, 2.0, 3.0)
let b = point(6.000, 14.000, 24.000) = scale.point(6.0, 7.0, 8.0) * point(1.0, 2.0, 3.0)
let c =
 point(42.000, 63.000, 88.000)
 = scale.point(6.0, 7.0, 8.0) * translate.point(6.0, 7.0, 8.0) * point(1.0, 2.0, 3.0)
let d =
 "[(0.708,-0.540,-0.455,-3.171)
  /br, (0.540, 0.000, 0.841, 9.974)
  /br, (-0.455, 0.841, 0.292, 5.498)
  /br, (0.000, 0.000, 0.000)]"
 = print(
  transpose.transpose.identity
  * rotatez.deg.90.0
  * rotatex.1.0
  * rotatey.1.0
  * translate.point(6.0, 7.0, 8.0)
 )
let p1 = cross(point(6.0, 7.0, 8.0), point(1.0, 0.0, 0.0) + point(0.0, 0.0, 0.0))
let ts = totimestamp(2023, 7, 5, 10, 8, 7)
assert
 toUTF8."2023-7-5.10:8:7" = toUTF8.print.ts
 ∧ dayofyear.ts = 186
 ∧ asseconds.totimestamp.212555268487 = 212555268487
report "^(asseconds.ts)"
assert
 a
 ∧ b
 ∧ c
 ∧ d
 ∧ print(3, length.unit.-(p1 - 3.0 * p1 + p1)) = "1.000"
 ∧ p1 >1 p1 = EQ
report "problem with matrix
 ^(print(
  transpose.transpose.identity
  * rotatez.deg.90.0
  * rotatex.1.0
  * rotatey.1.0
  * translate.point(6.0, 7.0, 8.0)
 ))"
assert testjulian report "problem with julian^(print.currenttime)"
let arcs = [arc(1_"A", 1_"B"), arc(1_"B", 1_"C"), arc(1_"B", 1_"D")],
"test common ok^(drawgraph(arcs, empty:set.word, empty:set.word))" 