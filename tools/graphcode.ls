Module graphcode

use standard

use seq.symbol

use symbol1

use arc.symloc

use graph.arc.symloc

use set.arc.symloc

use seq.symloc

use stack.symloc

Function nodeLabel(node:symloc) seq.seq.word
let t = %.sym.node
let t2 = if t sub n.t ∈ "/br" then t >> 1 else t,
["", node2text.node, %.loc.node + t2]

Function %(symloc) seq.word "????"

Export type:symloc

type symloc is loc:int, sym:symbol

function =(a:symloc, b:symloc) boolean loc.a = loc.b

function >1(a:symloc, b:symloc) ordering loc.a >1 loc.b

Function tograph(s:seq.symbol) graph.arc.symloc
for acc = empty:seq.arc.symloc, stk = empty:stack.symloc, i ∈ arithseq(n.s, 1, 1)
do
 let sym = s sub i
 let sons =
  if sym = EndBlock then
   for stk2 = stk, sons = empty:seq.symloc, k ∈ toseq.stk
   while not.isempty.stk2 ∧ kind.sym.top.stk2 ∉ [kloop, kstart]
   do next(pop.stk2, sons + top.stk2),
   sons + top.stk2
  else
   for stk2 = stk, sons = empty:seq.symloc, count = nopara.sym, k ∈ toseq.stk
   while count > 0
   do
    let top = top.stk2,
    next(pop.stk2, sons + top, if kind.sym.top = kdefine then count else count - 1),
   sons
 let newstk = pop(stk, n.sons),
 let tail = symloc(i, sym),
 next(
  for arcs = acc, sy ∈ sons do arcs + arc(tail, sy),
  arcs
  , push(newstk, tail)
 ),
newgraph.acc

Function node2text(a:symloc) seq.word
let sy = sym.a
let kind = kind.sy,
if kind = kloop then "Loop::(firstvar.sy)"
else if isspecial.kind then
 let t = %.sy,
 if t sub n.t ∈ "/br" then t >> 1 else t
else if isconst.kind ∨ kind = klocal then %.sy
else [name.sy] 