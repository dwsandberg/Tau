Module profile

use seq.byte

use bits

use graphcode

use standard

use seq.arc.symbol

use graph.symbol

use set.labeledarc.symbol

use seq.symbol

use svg2graph.symbol

use symbol2

Function profileData seq.parc {OPTION NOINLINE} empty:seq.parc

use seq.parc

type parc is caller:int, callee:int, counts:int, clocks:int, space:int, unused:int

function measure(arc:parc, measure:seq.word) int
if measure = "time" then
 clocks.arc
else if measure = "count" then
 counts.arc
else
 assert measure = "space" report "unknown profile measure"
 space.arc

type addrsym is addr:int,sym:symbol

function >1(a:addrsym, b:addrsym) ordering addr.a >1 addr.b

function %(a:addrsym) seq.word %.addr.a+ %.sym.a

use seq.addrsym

use set.addrsym

builtin vector2 seq.byte

Function  addrsym set.addrsym asset.inbytes:addrsym(vector2)

Function decode(d:set.addrsym,i:int) symbol
sym.lookup(d,addrsym(i,Lit.0))_1

use objectio.addrsym

use otherseq.addrsym

Function profileresults(measure:seq.word) seq.word
let d=addrsym
let b = 
 for acc0 = empty:seq.labeledarc.symbol, max = 0, arc ∈ profileData do
  let m = measure(arc, measure)
  if m = 0 ∨ m < max / 100 then
   next(acc0, max)
  else
   next(acc0 + arc(decode(d,caller.arc), decode(d,callee.arc), [toword.m])
    , max(max, m))
 /for (
  for acc = empty:seq.labeledarc.symbol, arc2 ∈ acc0 do
   let m = toint.first.label.arc2
   if m < max / 100 then
    acc
   else
    acc + arc(tail.arc.arc2, head.arc.arc2, [toword(m * 100 / max)])
  /for (acc)
 )
drawgraph(for acc = empty:seq.arc.symbol, arc ∈ b do acc + arc.arc /for (newgraph.acc), asset.b) 