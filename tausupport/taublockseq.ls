Module taublockseq.T

use seq.T

use bitcast.seq.T

use bitcast.int

use ptr

use bitcast.ptr

use standard

builtin getfld(address:blockseq.T, offset:int) seq.T {load value of type T at address}

Export type:blockseq.T

Export type:seq.T {From seq.T}

unbound set2(ptr, T) ptr

type blockseq is sequence, dummy:seq.T

Function blocksize:T int 8160

Function blockseqtype:T int getseqtype.toseq.blockseq(1, empty:seq.T)

function sequenceIndex(a:blockseq.T, i:int) T
assert between(i, 1, n.toseq.a) report "out of bounds"
let blksz = n.dummy.a
let blk = getfld(a, (i - 1) / blksz + 2),
((i - 1) mod blksz + 1)#blk

Function _(a:blockseq.T, i:int) T
assert between(i, 1, n.toseq.a) report "out of bounds"
let blksz = n.dummy.a
let blk = getfld(a, (i - 1) / blksz + 2),
((i - 1) mod blksz + 1)#blk

Function blockit3(s:seq.T) seq.T
let blksz = blocksize:T,
if n.s ≤ blksz then
 let newseq = allocatespace(n.s + 2)
 for acc = set(set(newseq, 0), n.s), @e ∈ s do set2(acc, @e),
 bitcast:seq.T(newseq)
else
 let noblks = (n.s + blksz - 1) / blksz
 let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
 let blkseq = allocatespace(noblks + 2)
 for acc = set(set(blkseq, blockseqtype), n.s), @e ∈ arithseq(noblks, blksz, 1)
 do
  let newseq = allocatespace(blksz + 2)
  let k = subseq(s, @e, @e + blksz - 1)
  let d = for acc2 = set(set(newseq, 0), n.k), e ∈ k do set2(acc2, e), acc2,
  set(acc, newseq),
 bitcast:seq.T(blkseq)

Function blockit2(s:seq.T, ds:int) seq.T
assert ds > 1 report "blockit problem"
let blksz = blocksize:T / ds,
if n.s ≤ blksz then
 let newseq = allocatespace(n.s * ds + 2)
 for acc = set(set(newseq, 1), n.s), @e ∈ s do set2(acc, @e),
 bitcast:seq.T(newseq)
else
 let noblks = (n.s + blksz - 1) / blksz
 let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
 let blkseq = allocatespace(noblks + 2)
 for acc = set(set(blkseq, blockseqtype), n.s), @e ∈ arithseq(noblks, blksz, 1)
 do
  let s2 = subseq(s, @e, @e + blksz - 1)
  let newseq = allocatespace(n.s2 * ds + 2)
  let d = for acc2 = set(set(newseq, 1), n.s2), e ∈ s2 do set2(acc2, e), acc2,
  set(acc, newseq),
 bitcast:seq.T(blkseq)
 