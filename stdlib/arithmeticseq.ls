Module arithmeticseq(T)

type arithmeticseq is sequence length:int, step:T, start:T

use seq.T

use stdlib

Function +(T, T)T unbound

Function *(int, T)T unbound

Function length(s:arithmeticseq.T)int export

Function_(s:arithmeticseq.T, i:int)T start.s +(i - 1)* step.s

Function arithseq(length:int, step:T, start:T)seq.T toseq.arithmeticseq(length, step, start)

/Module aseq(T)

