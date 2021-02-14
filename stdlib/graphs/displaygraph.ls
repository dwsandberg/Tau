Module displaygraph.T

use display

use standard

use bandeskopf.T

use graph.T

use layergraph.T

use makeDAG.T

use seq.T

use set.T

use svggraph.T

use seq.arc.T

use set.arc.T

use seq.arcinfo.T

use set.arcinfo.T

use seq.nodeinfo.T

use set.nodeinfo.T

unbound assignwidths(control:characterwidths, p:nodeinfo.T)nodeinfo.T

unbound nodetotext(a:T)seq.word

function restoredirection(orgarc:set.arcinfo.T, org:graph.T, modified:graph.T, a:arc.T)seq.arcinfo.T
 let other = if head.a ∈ nodes.org ∧ not(tail.a ∈ nodes.org)then
 expandback(org, modified, tail.a)
 else tail.a
 let for2 = findelement(arcinfo.arc(other, head.a), orgarc)
 let back = findelement(arcinfo.arc(head.a, other), orgarc)
 let both = if not.isempty.for2 then [ setarc(for2_1, a, false)]else empty:seq.arcinfo.T ;
 + if not.isempty.back then [ setarc(back_1, a, true)]else empty:seq.arcinfo.T
  if isempty.both then [ arcinfo.a]else both

Function restorearcs(orgarc:set.arcinfo.T, org:graph.T, modified:graph.T)seq.arcinfo.T
 for @e ∈ toseq.arcs.modified, acc = empty:seq.arcinfo.T ,,, acc + restoredirection(orgarc, org, modified, @e)

Function displaygraph(control:characterwidths, arci:seq.arcinfo.T)seq.word
 let g = newgraph.for @e ∈ arci, acc = empty:seq.arc.T ,,, acc + a.@e
 let lg = layer.makeDAG.g
 let posistion = assignx(g.lg, nodes.g.lg - nodes.g, layers.lg)
 let p1 = for @e ∈ toseq.posistion, acc = empty:seq.nodeinfo.T ,,, acc + assignwidths(control, @e)
 let p3 = restorearcs(asset.arci, g, g.lg)
  tosvg(p3, toseq.nodes.g, asset.p1)

Function displaygraph(control:characterwidths, g:graph.T)seq.word
 let arci = for @e ∈ toseq.arcs.g, acc = empty:seq.arcinfo.T ,,, acc + arcinfo.@e
 let lg = layer.makeDAG.g
 let posistion = assignx(g.lg, nodes.g.lg - nodes.g, layers.lg)
 let p1 = for @e ∈ toseq.posistion, acc = empty:seq.nodeinfo.T ,,, acc + assignwidths(control, @e)
 let p3 = restorearcs(asset.arci, g, g.lg)
  tosvg(p3, toseq.nodes.g, asset.p1)