Module tree.T

use seq.tree.T

use standard

type tree is record label:T, sons:seq.tree.T

Export type:tree.T

unbound =(T, T)boolean

Function =(a:tree.T, b:tree.T)boolean
 if label.a = label.b then sons.a = sons.b else false

Function tree(l:T)tree.T tree(l, empty:seq.tree.T)

Export label(t:tree.T)T

Export sons(t:tree.T)seq.tree.T

Export tree(l:T, s:seq.tree.T)tree.T

Function_(t:tree.T, i:int)tree.T(sons.t)_i

Function nosons(t:tree.T)int length.sons.t

Function postorder(a:tree.T)seq.tree.T sons.a @ +(empty:seq.tree.T, postorder.@e) + a

Function replace(with:T, a:T, t:tree.T)tree.T
 let newlabel = if label.t = a then with else label.t
  tree(newlabel, sons.t @ +(empty:seq.tree.T, replace(with, a, @e)))

------------------