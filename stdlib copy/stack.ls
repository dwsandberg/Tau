Module stack.T

use seq.T

use stacktrace

use stdlib

type stack is record toseq:seq.T

Function top(f:stack.T, n:int)seq.T subseq(toseq.f, length.toseq.f - n + 1, length.toseq.f)

Function top(f:stack.T)T toseq(f)_length.toseq.f

Function push(f:stack.T, t:T)stack.T stack(toseq.f + t)

Function pop(f:stack.T, n:int)stack.T 
 assert length.toseq.f ≥ n report"stack underflow"
  stack.subseq(toseq.f, 1, length.toseq.f - n)

Function pop(f:stack.T)stack.T 
 assert length.toseq.f > 0 report"stack underflow"
  stack.subseq(toseq.f, 1, length.toseq.f - 1)

Function empty stack.T stack.empty:seq.T

Function stack(t:T)stack.T stack.[ t]

Function isempty(f:stack.T)boolean length.toseq.f = 0

Function undertop(f:stack.T, n:int)T toseq(f)_(length.toseq.f - n)

Function toseq(stack.T)seq.T export

___________________

