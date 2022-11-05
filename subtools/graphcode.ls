Module graphcode

use standard

use symbol

use graph.symbol

use seq.symbol

use set.symbol

use svg2graph.symbol

use seq.arc.symloc

use graph.symloc

use seq.symloc

use set.symloc

use stack.symloc

use svg2graph.symloc

Export drawgraph(graph.symbol) seq.word {From svg2graph.symbol}

type symloc is loc:int, sym:symbol

function =(a:symloc, b:symloc) boolean loc.a = loc.b

function >1(a:symloc, b:symloc) ordering loc.a >1 loc.b

function %(a:symloc) seq.word %.loc.a + %.sym.a

Function tograph(s:seq.symbol) seq.word
for acc = empty:seq.arc.symloc
 , stk = empty:stack.symloc
 , i ∈ arithseq(length.s, 1, 1)
do
 let sym = s_i
 let sons = 
  if sym = EndBlock then
   for stk2 = stk, sons = empty:seq.symloc, k ∈ toseq.stk
   while not.isempty.stk2 ∧ not.isstartorloop.sym.top.stk2
   do
    next(pop.stk2, sons + top.stk2)
   /for (sons + top.stk2)
  else
   for stk2 = stk, sons = empty:seq.symloc, count = nopara.sym, k ∈ toseq.stk
   while count > 0
   do
    let top = top.stk2
    next(pop.stk2, sons + top, if isdefine.sym.top then count else count - 1)
   /for (sons)
 let newstk = pop(stk, length.sons)
 let tail = symloc(i, sym)
 next(for arcs = acc, sy ∈ sons do arcs + arc(tail, sy) /for (arcs), push(newstk, tail))
/for (drawgraph.newgraph.acc)

Function generatenode(a:set.symloc) symloc symloc(cardinality.a, Lit.0)

Function node2text(a:symloc) seq.word
let sy = sym.a
if isloopblock.sy then
 "Loop:$(firstvar.sy)"
else if isconst.sy ∨ islocal.sy ∨ isspecial.sy then %.sy else [name.sy]

Function nodeTitle(a:symloc) seq.word %.sym.a

Function generatenode(a:set.symbol) symbol Lit.cardinality.a

Function node2text(a:symbol) seq.word [name.a]

Function nodeTitle(a:symbol) seq.word %.a 