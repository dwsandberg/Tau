Module taublockseq.T

use ptr

use standard

use seq.T

use bitcast.seq.T

Export type:seq.T

Export type:blockseq.T

builtin getfld(address:blockseq.T, offset:int)seq.T{load value of type T at address}

unbound set(ptr, T)ptr

type blockseq is sequence, dummy:seq.T

function blocksize:T int 8160

Function blockseqtype:T int getseqtype.toseq.blockseq(1, empty:seq.T)

Function _(a:blockseq.T, i:int)T
assert between(i, 1, length.toseq.a)report"out of bounds"
let blksz = length.dummy.a
let blk = getfld(a, (i - 1) / blksz + 2)
blk_(toindex((i - 1) mod blksz + 1))

Function blockit3(s:seq.T)seq.T
let blksz = blocksize:T
if length.s ≤ blksz then
 let newseq = allocatespace(length.s + 2)
 let d = for acc = set(set(newseq, 0), length.s), @e ∈ s do set(acc, @e)/for(acc)
 bitcast:seq.T(newseq)
else
 let noblks = (length.s + blksz - 1) / blksz
 let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
 let blkseq = allocatespace(noblks + 2)
 let discard = 
  for acc = set(set(blkseq, blockseqtype), length.s), @e ∈ arithseq(noblks, blksz, 1)do
   let newseq = allocatespace(blksz + 2)
   let d = 
    for acc2 = set(set(newseq, 0), blksz), e ∈ subseq(s, @e, @e + blksz - 1)do set(acc2, e)/for(acc2)
   let x = bitcast:seq.T(newseq)
   set(acc, newseq)
  /for(acc)
 bitcast:seq.T(blkseq)

Function blockit2(s:seq.T, ds:int)seq.T
assert ds > 1 report"blockit problem"
let blksz = blocksize:T / ds
if length.s ≤ blksz then
 let newseq = allocatespace(length.s * ds + 2)
 let d = for acc = set(set(newseq, 1), length.s), @e ∈ s do set(acc, @e)/for(acc)
 bitcast:seq.T(newseq)
else
 let noblks = (length.s + blksz - 1) / blksz
 let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
 let blkseq = allocatespace(noblks + 2)
 let discard = 
  for acc = set(set(blkseq, blockseqtype), length.s), @e ∈ arithseq(noblks, blksz, 1)do
   let s2 = subseq(s, @e, @e + blksz - 1)
   let newseq = allocatespace(length.s2 * ds + 2)
   let d = for acc2 = set(set(newseq, 1), length.s2), e ∈ s2 do set(acc2, e)/for(acc2)
   set(acc, newseq)
  /for(acc)
 bitcast:seq.T(blkseq) 