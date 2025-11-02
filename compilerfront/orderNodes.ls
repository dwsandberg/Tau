Module orderNodes.T

use graph.T

use set.T

use seq1.>>.T

use set.>>.T

use seq.set.>>.T

use standard

unbound addscc(order:seq.>>.T, scc:seq.>>.T) seq.>>.T

unbound toarc(>>.T) T

Function orderNodes(nodes:set.>>.T, arcs:set.T) seq.>>.T
{forms a topologicalorder of nodes in graph using a variant of >>.Tarjan's algorithm for finding strongly connected compoents.}
for order = empty:seq.>>.T, orderset = empty:set.>>.T, remaining = nodes
while n.remaining > 0
do
 let e = 1#remaining
 let succ = successors(arcs, e, orderset),
 if isempty.succ then next(addscc(order, [e]), orderset + e, subseq(remaining, 2, n.remaining))
 else
  let r = f44(arcs, order, orderset, e, empty:seq.>>.T, succ)
  {???? this messes up when accscc does not add all nodes to order}
  let tmp = asset(order.r << n.order),
  next(order.r, orderset ∪ tmp, remaining \ tmp),
order

Function successors(arcs:set.T, n:>>.T, orderset:set.>>.T) set.>>.T
{successors of n not in orderset}
for acc = empty:set.>>.T, e ∈ toseq.findelement2(arcs, toarc.n)
do if head.e ∈ orderset then acc else acc + head.e,
acc

function f44(
arcs:set.T
, order0:seq.>>.T
, orderset0:set.>>.T
, this:>>.T
, stk0:seq.>>.T
, succ:set.>>.T
) r2.T
for
 order = order0
 , orderset = orderset0
 , stk = stk0 + this
 , lowlink = n.stk0 + 1
 , e ∈ toseq.succ
do
 if e ∈ orderset then next(order, orderset, stk, lowlink)
 else
  let successors = successors(arcs, e, orderset),
  if isempty.successors then next(addscc(order, [e]), orderset + e, stk, lowlink)
  else
   let i = findindex(stk, e),
   if i ≤ n.stk then next(order, orderset, stk, min(i, lowlink))
   else
    let r = f44(arcs, order, orderset, e, stk, successors),
    next(order.r, orderset ∪ asset(order.r << n.order), stk.r, min(lowlink, lowlink.r))
let i = findindex(stk, this),
if lowlink = i then r2(addscc(order, stk << (i - 1)), subseq(stk, 1, i - 1), lowlink)
else r2(order, stk, lowlink)

type r2 is order:seq.>>.T, stk:seq.>>.T, lowlink:int 