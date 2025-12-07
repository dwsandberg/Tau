Module arc.T

use standard

use seq.seq.word

use set.T

Export type:arc.T

Export head(arc.T) T

Export tail(arc.T) T

Export arc(T, T) arc.T

type arc is tail:T, head:T

Function toarc(n:T) arc.T arc(n, n)

Function reverse(a:arc.T) arc.T arc(head.a, tail.a)

Function merge(p:arc.T, s:arc.T) arc.T arc(tail.p, head.s)

Function arcLabel(set.arc.T, T, T) seq.seq.word empty:seq.seq.word 