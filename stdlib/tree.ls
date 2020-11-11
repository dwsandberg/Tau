Module tree.T

use seq.tree.T

use stdlib

type tree is record label:T, sons:seq.tree.T

Export type:tree.T  

unbound =(T, T)boolean 

Function =(a:tree.T, b:tree.T)boolean
 if label.a = label.b then sons.a = sons.b else false

Function tree(l:T)tree.T tree(l, empty:seq.tree.T)

Function label(t:tree.T)T export

Function sons(t:tree.T)seq.tree.T export

Function tree(l:T, s:seq.tree.T)tree.T export

Function_(t:tree.T, i:int)tree.T(sons.t)_i

Function nosons(t:tree.T)int length.sons.t

Function postorder(a:tree.T)seq.tree.T @(+, postorder, empty:seq.tree.T, sons.a) + a

Function replace(with:T, a:T, t:tree.T)tree.T
 let newlabel = if label.t = a then with else label.t
  tree(newlabel, @(+, replace(with, a), empty:seq.tree.T, sons.t))

- - - - - - - - - - - - - - - - - -