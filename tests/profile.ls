Module profile

use otherseq.addrsym

use seq.addrsym

use seq.seq.addrsym

use set.addrsym

use otherseq.parc

use seq.parc

use seq.seq.parc

use standard

use seq.arc.int

use set.arc.int

use graph.symbol

use seq.symbol

use newsvg

use symbol2

use seq.m3

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

Function decode(d:set.addrsym, i:int) symbol sym.1#lookup(d, addrsym(i, Lit.0))

function %(p:parc) seq.word %.caller.p + %.callee.p + %.counts.p + %.clocks.p + %.unused.p

type m3 is caller:int, callee:int, measure:int

use set.int

use seq.labeledNode

use seq.labeledarc

use set.labeledarc

use graph.int

Function profileresults(measure:seq.word) seq.word
for d0 = empty:seq.addrsym, a ∈ addresssymbols
do d0 + a
let d = asset.d0
for profileData = empty:seq.parc, e ∈ profiledata
do profileData + e
for acc0 = empty:seq.m3, max = 0, arc ∈ profileData
do
 let m = measure(arc, measure),
 if m = 0 ∨ m < max / 100 ∨ caller.arc = callee.arc then next(acc0, max)
 else next(acc0 + m3(caller.arc, callee.arc, m), max(max, m))
for acc = empty:seq.m3, nodes = empty:set.int, m ∈ acc0
do
 if measure.m < max / 100 then next(acc, nodes)
 else next(acc + m, nodes + caller.m + callee.m)
for nodeinfo = empty:seq.labeledNode, node ∈ toseq.nodes
do
 let sym = decode(d, node),
 nodeinfo + labeledNode("", [name.sym], %.sym)
for labelinfo = empty:seq.labeledarc, finalarcs = empty:set.arc.int, m ∈ acc
do
 let tail = findindex(nodes, caller.m)
 let head = findindex(nodes, callee.m),
 next(
  labelinfo + labeledarc(tail, head, "", [toword(measure.m * 100 / max)])
  , finalarcs + arc(tail, head)
 ),
if n.acc = 0 then "No non-zero arcs"
else drawgraph(newgraph.toseq.finalarcs, nodeinfo, asset.labelinfo) 