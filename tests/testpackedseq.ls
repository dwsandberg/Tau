module testpackedseq.T

use standard

use testseq

use otherseq.T

use process.T

use seq.T

unbound get:T T

unbound =(T, T) boolean

Function check:seq.T(size:int, depth:int) seq.word
let unpack = random:seq.T(depth)
let pack = packed.unpack
let typ = getseqtype.pack
let blksize = 8160 * 8
if pack ≠ unpack then "FAIL seq not equal"
else if length.pack ≤ blksize ∧ typ = 0 ∧ size = 8 then
 "PASS std" + toword.length.pack
else if length.pack ≤ blksize / size ∧ typ = 1 then
 "PASS packed" + toword.length.pack
else if length.pack > blksize / size ∧ typ ∉ [0, 1] then
 "PASS block" + toword.length.pack
else "FAIL" + toword.length.pack + toword.typ

Function random:seq.T(depth:int) seq.T
if depth ≤ 0 then base:seq.T
else
 random:seq.T(depth - 1 - getint.2)
 + random:seq.T(depth - 1 - getint.2)

Function base:seq.T seq.T
let i = getint.6
if i = 0 then empty:seq.T
else if i = 1 then [get:T]
else if i = 2 then [get:T, get:T]
else if i = 4 then [get:T, get:T, get:T, get:T, get:T]
else if i = 5 then [get:T, get:T, get:T, get:T, get:T, get:T]
else constantseq(getint.7, get:T)

function seqkind(a:seq.T) seq.word
let t = getseqtype.a
if t = 0 then [toword.length.a]
else if t = 1 then "packed" + toword.length.a
else if t = getseqtype.constantseq(1, get:T) then "const"
else if ispseq.a then "pseq" else "unknown"

Function seqstruct(a:seq.T) seq.word
let kind = seqkind.a
if kind = "pseq" then
 let p = to:pseq.T(a)
 "($(seqstruct.a.p) $(seqstruct.b.p))"
else kind 