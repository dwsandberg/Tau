Module tree.T

use standard

use seq.tree.T

type tree is label:T, sons:seq.tree.T

Export type:tree.T

unbound=(T, T)boolean

Function =(a:tree.T, b:tree.T)boolean if label.a = label.b then sons.a = sons.b else false

Export=(a:seq.tree.T, b:seq.tree.T)boolean

Function tree(l:T)tree.T tree(l, empty:seq.tree.T)

Export label(t:tree.T)T

Export sons(t:tree.T)seq.tree.T

Export tree(l:T, s:seq.tree.T)tree.T

Function _(t:tree.T, i:int)tree.T(sons.t)_i

Function nosons(t:tree.T)int length.sons.t

Function postorder(a:tree.T)seq.tree.T
for acc = empty:seq.tree.T, @e ∈ sons.a do acc + postorder.@e /for(acc) + a

use otherseq.tree.T

unbound %(T) seq.word

Function %(t:tree.T)seq.word
if nosons.t = 0 then %.label.t
else
  %.label.t 
 + if nosons.t = 1 then"." + %.t_1
 else 
  "("+ for acc="",  e /in sons.t   do acc+%.e+"," /for(acc >> 1   + ")")