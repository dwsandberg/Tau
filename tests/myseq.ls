Module myseq.T

All sequences must be in parameterized scopes.

use seq.T

use standard

type myseq is sequence, data:seq.T

Export type:myseq.T

All sequences must have the first element representing the length of the seqence.As with any parameterized scope any type must contain a element that use the parameter so that mutiple instances of the scope do not produce duplicate symbols.

We need some operations on T.T will be an int in this example so all these operations are define on int in Module standard.

unbound >(T, int) boolean

unbound <(T, int) boolean

unbound -(T, int) T

unbound *(T, int) T

unbound +(T, T) T

We need to helper functions to calculate the length and find the ith element of the seq for this example.

Export to:myseq.T(s:seq.T) myseq.T

Export toseq(myseq.T) seq.T

Function clength(s:seq.T, i:int) int
if i > n.s then 0
else
 assert i#s > 0 report "invalid",
 if i#s < 128 then 1 + clength(s, i + 1)
 else
  assert i#s < 128 + 64 + 32 report "invalid",
  1 + clength(s, i + 2)

Function cindex(s:seq.T, i:int, idx:int) T
if idx = 1 then if i#s < 128 then i#s else (i + 1)#s - 128 + (i#s - 128 - 64) * 64
else cindex(s, i + (if i#s < 128 then 1 else 2), idx - 1)

We need a constructor of our sequence.Note the use of a toseq function.This is defined implicitly by the sequence type definition to change the type from myseq (T) to seq (T).

Function myseq(d:seq.T) seq.T toseq.myseq(clength(d, 1), d)

Every sequence must have a _ function defined on it which is below for mseq.T

Function sequenceIndex(a:myseq.T, idx:int) T cindex(data.a, 1, idx) 