Module stack.T

use seq.T

use standard

Export type:stack.T

Export toseq(stack.T) seq.T

type stack is toseq:seq.T

Function top(f:stack.T, n:int) seq.T subseq(toseq.f, n.toseq.f - n + 1, n.toseq.f)

Function top(f:stack.T) T (n.toseq.f)#toseq.f

Function push(f:stack.T, t:T) stack.T stack(toseq.f + t)

Function pop(f:stack.T, n:int) stack.T
assert n.toseq.f ≥ n report "stack underflow^(stacktrace)",
stack.subseq(toseq.f, 1, n.toseq.f - n)

Function pop(f:stack.T) stack.T
assert n.toseq.f > 0 report "stack underflow^(stacktrace)",
stack.subseq(toseq.f, 1, n.toseq.f - 1)

Function empty:stack.T stack.T stack.empty:seq.T

Function isempty(f:stack.T) boolean n.toseq.f = 0

Function undertop(f:stack.T, n:int) T (n.toseq.f - n)#toseq.f 