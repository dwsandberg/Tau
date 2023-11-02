Module tree.T

use seq.tree.T

use standard

type tree is label:T, sons:seq.tree.T

Export type:tree.T

unbound =(T, T) boolean

Function =(a:tree.T, b:tree.T) boolean
if label.a = label.b then sons.a = sons.b else false

Export =(a:seq.tree.T, b:seq.tree.T) boolean

Function tree(l:T) tree.T tree(l, empty:seq.tree.T)

Export label(t:tree.T) T

Export sons(t:tree.T) seq.tree.T

Export tree(l:T, s:seq.tree.T) tree.T

Function #(i:int, t:tree.T) tree.T i#sons.t

Function nosons(t:tree.T) int n.sons.t

Function postorder(a:tree.T) seq.tree.T
for acc = empty:seq.tree.T, @e ∈ sons.a do acc + postorder.@e,
acc + a

unbound %(T) seq.word

Function %(t:tree.T) seq.word
if nosons.t = 0 then
%.label.t
else
 %.label.t
  + 
  if nosons.t = 1 then
  ".^(1#t)"
  else "(^(for acc = "", e ∈ sons.t do acc + %.e + ",", acc >> 1 + ")")"
 