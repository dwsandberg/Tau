Module displaygraph.T

use seq.arc.T

use set.arc.T

use seq.arcinfo.T

use set.arcinfo.T

use bandeskopf.T

use graph.T

use layergraph.T

use makeDAG.T

use seq.nodeinfo.T

use set.nodeinfo.T

use seq.T

use set.T

use svggraph.T

use display

use stdlib

function assignwidths(control:prettycontrol, p:nodeinfo.T)nodeinfo.T unbound

Function nodetotext(a:T)seq.word unbound

function restoredirection(orgarc:set.arcinfo.T, org:graph.T, modified:graph.T, a:arc.T)seq.arcinfo.T
 let other = if head.a in nodes.org ∧ not(tail.a in nodes.org)then
 expandback(org, modified, tail.a)
 else tail.a
 let for = findelement(arcinfo.arc(other, head.a), orgarc)
 let back = findelement(arcinfo.arc(head.a, other), orgarc)
 let both =(if not.isempty.for then [ setarc(for_1, a, false)]else empty:seq.arcinfo.T)
 + if not.isempty.back then [ setarc(back_1, a, true)]else empty:seq.arcinfo.T
  if isempty.both then [ arcinfo.a]else both

Function restorearcs(orgarc:set.arcinfo.T, org:graph.T, modified:graph.T)seq.arcinfo.T
 @(+, restoredirection(orgarc, org, modified), empty:seq.arcinfo.T, toseq.arcs.modified)

Function displaygraph(control:prettycontrol, arci:seq.arcinfo.T)seq.word
 let g = newgraph.@(+, a, empty:seq.arc.T, arci)
 let lg = layer.makeDAG.g
 let posistion = assignx(g.lg, nodes.g.lg - nodes.g, layers.lg)
 let p1 = @(+, assignwidths(control), empty:seq.nodeinfo.T, toseq.posistion)
 let p3 = restorearcs(asset.arci, g, g.lg)
  // assert false report @(+, print,"", p3)// tosvg(p3, toseq.nodes.g, asset.p1)

Function displaygraph(control:prettycontrol, g:graph.T)seq.word
 let arci = @(+, arcinfo, empty:seq.arcinfo.T, toseq.arcs.g)
 let lg = layer.makeDAG.g
 let posistion = assignx(g.lg, nodes.g.lg - nodes.g, layers.lg)
 let p1 = @(+, assignwidths(control), empty:seq.nodeinfo.T, toseq.posistion)
 let p3 = restorearcs(asset.arci, g, g.lg)
  // assert false report @(+, print,"", p3)// tosvg(p3, toseq.nodes.g, asset.p1)