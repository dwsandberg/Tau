Module seq8.T

for testing not standard sequence optimization. new ([1, 128]) should be reduce to constant and if
non standard sequence is not detected will give new 2#([1, 128]) instead of 128. 

use seq.T

use standard

type seq8 is sequence, flda:seq.T, fldb:int

function sequenceIndex(a:seq8.T, i:int) T i#flda.a

Function newseq8(a:seq.T) seq.T toseq.seq8(n.a, a, 15) 