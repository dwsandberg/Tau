Module profile

use otherseq.addrsym

use seq.addrsym

use seq.seq.addrsym

use set.addrsym

use graphcode

use otherseq.parc

use seq.parc

use seq.seq.parc

use standard

use seq.arc.symbol

use set.arc.symbol

use graph.symbol

use seq.labeledarc.symbol

use set.labeledarc.symbol

use seq.symbol

use svg2graph.symbol

use symbol2

type parc is caller:int, callee:int, counts:int, clocks:int, space:int, unused:int

function measure(arc:parc, measure:seq.word) int
if measure = "time" then
clocks.arc
else if measure = "count" then
counts.arc
else assert measure = "space" report "unknown profile measure", space.arc

function >1(a:addrsym, b:addrsym) ordering addr.a >1 addr.b

function %(a:addrsym) seq.word %.addr.a + %.sym.a

builtin addresssymbols seq.seq.addrsym

builtin profiledata seq.seq.parc

Function decode(d:set.addrsym, i:int) symbol sym.1_lookup(d, addrsym(i, Lit.0))

function %(p:parc) seq.word
%.caller.p + %.callee.p + %.counts.p + %.clocks.p + %.unused.p

Function profileresults(measure:seq.word) seq.word
for d0 = empty:seq.addrsym, a ∈ addresssymbols do d0 + a
let d = asset.d0
for profileData2 = empty:seq.parc, e ∈ profiledata do profileData2 + e
{, for txt ="", p /in profileData2 do txt+"
 /br"+%.decode (d, caller.p)+%.decode (d, callee.p)+%.counts.p+%.clocks
 .p+%.unused.p, txt}
for acc0 = empty:seq.labeledarc.symbol, max = 0, arc ∈ profileData2
do
 let m = measure(arc, measure),
  if m = 0 ∨ m < max / 100 then
  next(acc0, max)
  else next(acc0 + arc(decode(d, caller.arc), decode(d, callee.arc), [toword.m]), max(max, m))
for acc = empty:seq.labeledarc.symbol, arc2 ∈ acc0
do
 let m = toint.1_label.arc2,
  if m < max / 100 ∨ tail.arc.arc2 = head.arc.arc2 then
  acc
  else acc + arc(tail.arc.arc2, head.arc.arc2, [toword(m * 100 / max)])
for finalarcs = empty:seq.arc.symbol, arc3 ∈ acc do finalarcs + arc.arc3,
if n.acc = 0 then "No non-zero arcs" else drawgraph(newgraph.finalarcs, asset.acc) 