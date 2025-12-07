Module dawsextensions

use pretty

use standard

use stack.seq.word

Function dawsextensions(op:word, argstk:stack.seq.word) stack.seq.word
{return empty:stack.seq.word if not defined}
if op ∈ "/pretty" then push(pop.argstk, pretty.top.argstk) else empty:stack.seq.word 