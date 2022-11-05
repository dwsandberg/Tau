Module profile

use graphcode

use impDependent

use standard

use seq.arc.symbol

use graph.symbol

use set.labeledarc.symbol

use seq.symbol

use svg2graph.symbol

use symbol2

function measure(arc:parc, measure:seq.word) int
if measure = "time" then
 clocks.arc
else if measure = "count" then
 counts.arc
else
 assert measure = "space" report "unknown profile measure"
 space.arc

type arcs/max is arcs:seq.labeledarc.symbol, max:int

Function profileresults(measure:seq.word) seq.word
let a = 
 for acc = arcs/max(empty:seq.labeledarc.symbol, 0), lib ∈ loadedLibs do
  for acc0 = arcs.acc, max = max.acc, arc ∈ profiledata.lib do
   let m = measure(arc, measure)
   if m = 0 ∨ m < max / 100 then
    next(acc0, max)
   else
    next(acc0 + arc((symbolrefdecodeX.lib)_(caller.arc), (symbolrefdecodeX.lib)_(callee.arc), [toword.m])
     , max(max, m))
  /for (arcs/max(acc0, max))
 /for (acc)
let b = 
 for acc = empty:seq.labeledarc.symbol, arc ∈ arcs.a do
  let m = toint.first.label.arc
  if m < max.a / 100 then
   acc
  else
   acc + arc(tail.arc.arc, head.arc.arc, [toword(m * 100 / max.a)])
 /for (acc)
drawgraph(for acc = empty:seq.arc.symbol, arc ∈ b do acc + arc.arc /for (newgraph.acc), asset.b) 