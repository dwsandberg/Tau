Module seq8.T

for testing not standard sequence optimization. new ([1, 128]) should be reduce to constant and if
non standard sequence is not detected will give new ([1, 128])_2 instead of 128. 

use seq.T

use standard

type seq8 is sequence, flda:seq.T, fldb:int

function _(a:seq8.T, i:int) T (flda.a)_i

Function newseq8(a:seq.T) seq.T toseq.seq8(length.a, a, 15) 