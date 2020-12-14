Module tree2.T

use seq.T

use seq.tree2.T

use seq.treenode.T

use standard

type tree2 is record nodes:seq.treenode.T, subtree:int

type treenode is record label:T, nosons:int, nonodes:int

unbound =(T, T)boolean

Function =(a:treenode.T, b:treenode.T)boolean
 label.a = label.b ∧ nosons.a = nosons.b

Function =(a:tree2.T, b:tree2.T)boolean
 let na = nonodes.a
 let nb = nonodes.b
  if na = nb then
  subseq(nodes.a, subtree.a - na + 1, subtree.a)
   = subseq(nodes.b, subtree.b - nb + 1, subtree.b)
  else false

Function tree2(l:T)tree2.T tree2([ treenode(l, 0, 1)], 1)

Function label(t:tree2.T)T label.(nodes.t)_(subtree.t)

Function sons(t:tree2.T)seq.tree2.T level(t, subtree.t, nosons.t)

Function tree2(l:T, s:seq.tree2.T)tree2.T
 let n = s @ +(empty:seq.treenode.T, intreenodes.@e)
  tree2(n + [ treenode(l, length.s, length.n + 1)], length.n + 1)

function intreenodes(t:tree2.T)seq.treenode.T subseq(nodes.t, subtree.t - nonodes.t + 1, subtree.t)

Function_(t:tree2.T, i:int)tree2.T
 assert between(i, 1, nosons.t)report"no such son" + toword.i + toword.nosons.t
  son(t, subtree.t, nosons.t - i + 1)

Function nosons(t:tree2.T)int nosons.(nodes.t)_(subtree.t)

Function nonodes(t:tree2.T)int nonodes.(nodes.t)_(subtree.t)

function level(t:tree2.T, i:int, remainingsons:int)seq.tree2.T
 if remainingsons = 0 then empty:seq.tree2.T
 else
  level(t, i - nonodes.(nodes.t)_(i - 1), remainingsons - 1)
  + [ tree2(nodes.t, i - 1)]

function son(t:tree2.T, i:int, remainingsons:int)tree2.T
 if remainingsons = 1 then tree2(nodes.t, i - 1)
 else son(t, i - nonodes.(nodes.t)_(i - 1), remainingsons - 1)

Function replace(t:tree2.T, with:T, a:T)tree2.T
 tree2(subseq(nodes.t, subtree.t - nonodes.t + 1, subtree.t)
 @ +(empty:seq.treenode.T, replace(with, a, @e)), nonodes.t)

function replace(replacement:T, match:T, a:treenode.T)treenode.T
 if label.a = match then treenode(replacement, nosons.a, nonodes.a)else a

Function postorder(a:tree2.T)seq.tree2.T
 arithseq(nonodes.a, 1, subtree.a - nonodes.a + 1)
 @ +(empty:seq.tree2.T, tree2(nodes.a, @e))