Module profile

precedence > for >1 >2

use seq1.addrsym

use seq.addrsym

use seq.seq.addrsym

use set.addrsym

use seq1.parc

use seq.parc

use seq.seq.parc

use standard

use arc.int

use seq.arc.int

use set.arc.int

use graph.profileMeasure.symbol

use arc.symbol

use seq.symbol

use svg

use symbol1

type parc is caller:int, callee:int, counts:int, clocks:int, space:int, unused:int

function measure(arc:parc, measure:seq.word) int
if measure = "time" then clocks.arc
else if measure = "count" then counts.arc
else
 assert measure = "space" report "unknown profile measure",
 space.arc

function >1(a:addrsym, b:addrsym) ordering addr.a >1 addr.b

function %(a:addrsym) seq.word %.addr.a + %.sym.a

builtin addresssymbols seq.seq.addrsym

builtin profiledata seq.seq.parc

Function decode(d:set.addrsym, i:int) symbol sym.lookup(d, addrsym(i, Lit.0)) sub 1

function %(p:parc) seq.word %.caller.p + %.callee.p + %.counts.p + %.clocks.p + %.unused.p

use set.int

use graph.profileMeasure.symbol

use set.profileMeasure.symbol

use seq.profileMeasure.symbol

use set.symbol

use drawGraph.profileMeasure.symbol

use profileMeasure.symbol

Function profileresults(measure:seq.word) seq.word
for d0 = empty:seq.addrsym, a ∈ addresssymbols
do d0 + a
let d = asset.d0
for profileData = empty:seq.parc, e ∈ profiledata
do profileData + e
for acc0 = empty:seq.profileMeasure.symbol, max = 1, arc ∈ profileData
do
 let m = measure(arc, measure),
 if m = 0 ∨ m < max / 100 ∨ caller.arc = callee.arc then next(acc0, max)
 else next(acc0 + profileMeasure(decode(d, caller.arc), decode(d, callee.arc), m), max(max, m))
for acc = empty:seq.profileMeasure.symbol, m ∈ acc0
do
 if measure.m < max / 100 then acc
 else acc + profileMeasure(tail.m, head.m, measure.m * 100 / max)
let g = newgraph.acc,
if n.acc = 0 then "No non-zero arcs" else drawgraph.g

Function arcLabel(arcs:set.profileMeasure.symbol, tail:symbol, head:symbol) seq.seq.word
let lab = lookup(arcs, profileMeasure(tail, head, 0)),
if isempty.lab then empty:seq.seq.word else ["", %.measure.lab sub 1] 
