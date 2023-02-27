Module profile

use graphcode

use standard

use seq.arc.symbol

use graph.symbol

use set.labeledarc.symbol

use seq.symbol

use svg2graph.symbol

use symbol2

use seq.parc

type parc is caller:int, callee:int, counts:int, clocks:int, space:int, unused:int

function measure(arc:parc, measure:seq.word) int
if measure = "time" then
 clocks.arc
else if measure = "count" then
 counts.arc
else
 assert measure = "space" report "unknown profile measure" ,
 space.arc

function >1(a:addrsym, b:addrsym) ordering addr.a >1 addr.b

function %(a:addrsym) seq.word %.addr.a + %.sym.a

use seq.addrsym

use seq.seq.addrsym

use set.addrsym

use seq.seq.parc

use otherseq.addrsym

use otherseq.parc

use set.arc.symbol

builtin addresssymbols seq.seq.addrsym

builtin profiledata seq.seq.parc

Function decode(d:set.addrsym, i:int) symbol sym.lookup(d, addrsym(i, Lit.0))_1

function %(p:parc) seq.word
%.caller.p + %.callee.p + %.counts.p + %.clocks.p + %.unused.p

use seq.labeledarc.symbol

Function profileresults(measure:seq.word) seq.word
let d = for acc = empty:seq.addrsym, a ∈ addresssymbols do acc + a /do    asset.acc  
let profileData2 = for acc = empty:seq.parc, e ∈ profiledata do acc + e /do acc   
{,for txt="",         p /in profileData2 do 
  txt+"/br"+%.decode(d,caller.p) + %.decode(d,callee.p) + %.counts.p + %.clocks.p + %.unused.p
/do txt
}
let b = 
 for acc0 = empty:seq.labeledarc.symbol, max = 0, arc ∈ profileData2 do
  let m = measure(arc, measure) ,
  if m = 0 ∨ m < max / 100 then
   next(acc0, max)
  else
   next(acc0 + arc(decode(d, caller.arc), decode(d, callee.arc), [toword.m]), max(max, m))
 /do  
  for acc = empty:seq.labeledarc.symbol, arc2 ∈ acc0 do
   let m = toint.first.label.arc2 ,
   if m < max / 100 ∨ tail.arc.arc2 = head.arc.arc2 then
    acc
   else
    acc + arc(tail.arc.arc2, head.arc.arc2, [toword(m * 100 / max)])
  /do acc 
let tmp = for acc = empty:seq.arc.symbol, arc ∈ b 
do acc + arc.arc /do newgraph.acc ,
if length.b=0 then "No non-zero arcs"
else drawgraph(tmp, asset.b) 