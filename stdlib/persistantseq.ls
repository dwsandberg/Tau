Module persistantseq.T

use encoding.T

use seq.T

use ipair.linklists2

use llvm

use persistant

use stdlib

function addele(t:trackele, s:T)trackele
 let a = addrecord(l.t, s)
  trackele(value.a, places.t + index.a)

function addrecord(linklists2, s:T)ipair.linklists2 unbound

Function addseq(l:linklists2, s:seq.T)ipair.linklists2
 let x = @(addele, identity, trackele(l, empty:seq.int), s)
 let t = linklists2(a.l.x + C64.0 + C64.length.s)
  ipair(place.l.x, @(addoffset, identity, t, places.x))

function identityf(s:seq.T)seq.T s