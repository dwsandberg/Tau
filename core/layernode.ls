Module layernode

/use brandeskopf

use seq1.int

use seq.seq.int

use arc.layernode

use graph.arc.layernode

use set.arc.layernode

use seq1.layernode

use set.layernode

use standard

Export type:layernode

Export layer(a:layernode) int

Export no(a:layernode) int

Export pos(a:layernode) int

Export layernode(int, int, int) layernode

Export type:path

Export path(tailidx:int, headidx:int, startdummy:int, enddummy:int, class:word) path

Export type:rr5

Export g(rr5) graph.arc.layernode

Export orgNodeCount(rr5) int

Export rr5(g:graph.arc.layernode, paths:seq.path, int) rr5

type layernode is no:int, layer:int, pos:int

Function %(a:layernode) seq.word "{:(no.a):(layer.a):(pos.a)}"

Function >1(a:layernode, b:layernode) ordering layer.a >1 layer.b ∧ pos.a >1 pos.b

Function >2(a:layernode, b:layernode) ordering layer.a >1 layer.b

Function >3(a:layernode, b:layernode) ordering no.a >1 no.b

type path is tailidx:int, headidx:int, startdummy:int, enddummy:int, class:word

Function >1(a:path, b:path) ordering tailidx.a >1 tailidx.b

Function %(a:path) seq.word
 ":(tailidx.a):(headidx.a):(startdummy.a):(enddummy.a):(class.a)"

Export class(path) word

Function nodes(p:path) seq.int
if startdummy.p = 0 then [tailidx.p, headidx.p]
else [tailidx.p] + arithseq(enddummy.p - startdummy.p + 1, 1, startdummy.p) + headidx.p

type rr5 is g:graph.arc.layernode, paths:seq.path, orgNodeCount:int

Export paths(rr5) seq.path

Function reduceCrossings(gg1:graph.arc.layernode) graph.arc.layernode
{reduce crossing using barycenter}
if isempty.nodes.gg1 then gg1
else
 let nodes = toseq.nodes.gg1
 for acc5 = empty:seq.layernode, layerno ∈ arithseq(layer.nodes sub n.nodes - 1, 1, 2)
 do
  for
   ord = empty:seq.layernode
   , bset = empty:seq.int
   , e ∈ toseq.findelement2(nodes.gg1, layernode(0, layerno, 0))
  do
   let preds = toseq.predecessors(gg1, e)
   for sum = 0, p ∈ preds do sum + pos.p
   let barycenter = 100 * sum / n.preds,
   let i = abs.binarysearch(bset, barycenter),
   next(
    subseq(ord, 1, i - 1) + [e] + subseq(ord, i, n.ord)
    , subseq(bset, 1, i - 1) + [barycenter] + subseq(bset, i, n.bset)
   )
  {assert n.nodes.gg1 /ne 13 report %.toseq.findelement2(nodes.gg1, layernode(0, 3, 0))+"ord::(ord)bary::(bset)"}
  for acc6 = acc5, idx = 1, e ∈ ord
  do next(if pos.e = idx then acc6 else acc6 + layernode(no.e, layer.e, idx), idx + 1),
  acc6,
 if isempty.acc5 ∨ n.nodes.gg1 ≠ 13 then gg1
 else
  let newnodes = asset.acc5 ∪ nodes.gg1
  for newarcs = empty:seq.arc.layernode, a ∈ toseq.arcs.gg1
  do newarcs + arc(newnodes sub no.tail.a, newnodes sub no.head.a),
  newgraph.newarcs + toseq.newnodes
 