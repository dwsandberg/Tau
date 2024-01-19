Module graphcode

use seq.arc.int

use set.arc.int

use graph.int

use seq.labeledNode

use set.labeledarc

use newsvg

use standard

use set.arc.symbol

use graph.symbol

use seq.symbol

use set.symbol

use symbol2

use set.arc.symloc

use graph.symloc

use seq.symloc

use set.symloc

use stack.symloc

Function drawgraph(g:graph.symbol) seq.word
for arclist = empty:seq.arc.int, arc ∈ toseq.arcs.g
do arclist + arc(findindex(nodes.g, tail.arc), findindex(nodes.g, head.arc))
for nodeinfo = empty:seq.labeledNode, node ∈ toseq.nodes.g
do nodeinfo + labeledNode("", [name.node], %.node),
drawgraph(newgraph.arclist, nodeinfo, empty:set.labeledarc)

Function drawgraph(g:graph.symloc) seq.word
for arclist = empty:seq.arc.int, arc ∈ toseq.arcs.g
do arclist + arc(findindex(nodes.g, tail.arc), findindex(nodes.g, head.arc))
for nodeinfo = empty:seq.labeledNode, node ∈ toseq.nodes.g
do
 let t = %.sym.node
 let t2 = if 1^t ∈ "/br" then t >> 1 else t,
 nodeinfo + labeledNode("", node2text.node, %.loc.node + t2),
drawgraph(newgraph.arclist, nodeinfo, empty:set.labeledarc)

type symloc is loc:int, sym:symbol

function =(a:symloc, b:symloc) boolean loc.a = loc.b

function >1(a:symloc, b:symloc) ordering loc.a >1 loc.b

Function tograph(s:seq.symbol) seq.word
for acc = empty:seq.arc.symloc, stk = empty:stack.symloc, i ∈ arithseq(n.s, 1, 1)
do
 let sym = i#s
 let sons =
  if sym = EndBlock then
   for stk2 = stk, sons = empty:seq.symloc, k ∈ toseq.stk
   while not.isempty.stk2 ∧ not.isstartorloop.sym.top.stk2
   do next(pop.stk2, sons + top.stk2),
   sons + top.stk2
  else
   for stk2 = stk, sons = empty:seq.symloc, count = nopara.sym, k ∈ toseq.stk
   while count > 0
   do
    let top = top.stk2,
    next(pop.stk2, sons + top, if isdefine.sym.top then count else count - 1),
   sons
 let newstk = pop(stk, n.sons),
 let tail = symloc(i, sym),
 next(
  for arcs = acc, sy ∈ sons do arcs + arc(tail, sy),
  arcs
  , push(newstk, tail)
 ),
drawgraph.newgraph.acc

Function node2text(a:symloc) seq.word
let sy = sym.a,
if isloopblock.sy then "Loop:^(firstvar.sy)"
else if isspecial.sy then
 let t = %.sy,
 if 1^t ∈ "/br" then t >> 1 else t
else if isconst.sy ∨ islocal.sy then %.sy
else [name.sy] 