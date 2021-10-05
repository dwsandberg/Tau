Module tree.T

use standard

use seq.tree.T

type tree is label:T, sons:seq.tree.T

Export type:tree.T

unbound =(T, T)boolean

Function =(a:tree.T, b:tree.T)boolean if label.a = label.b then sons.a = sons.b else false

Export =(a:seq.tree.T, b:seq.tree.T)boolean

Function tree(l:T)tree.T tree(l, empty:seq.tree.T)

Export label(t:tree.T)T

Export sons(t:tree.T)seq.tree.T

Export tree(l:T, s:seq.tree.T)tree.T

Function_(t:tree.T, i:int)tree.T(sons.t)_i

Function nosons(t:tree.T)int length.sons.t

Function postorder(a:tree.T)seq.tree.T
for acc = empty:seq.tree.T, @e ∈ sons.a do acc + postorder.@e /for(acc) + a

Function replace(with:T, a:T, t:tree.T)tree.T
let newlabel = if label.t = a then with else label.t
tree(newlabel
, for acc = empty:seq.tree.T, @e ∈ sons.t do acc + replace(with, a, @e)/for(acc)
)

------------------ 