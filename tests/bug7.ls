module bug7

use standard

use seq8.int

use encoding.llvmtypeele2

use seq.llvmtypeele2

use encoding.slot2

use seq.slot2

type slot2 is type:int, rec:seq.int, name:seq.word

function =(a:slot2, b:slot2)boolean rec.a = rec.b ∧ type.a = type.b ∧ name.a = name.b

function hash(a:slot2)int hash.rec.a

Function c32(i:int)encoding.slot2 encode.slot2(i32, [45, i], "")

Function testbug7 seq.word
{since encodings have side effects it is not safe to use simple inline expansion of functions since the order of
  evaluation becomes important. Function c32 is the candiate for inline expansion. }
let discard0 = [i64, i32]
let z = c32.0
if[i64, i32] = [1, 2] ∧ 128 = (newseq8.[1, 128])_2 then"PASS bug7"
else"FAIL bug7"

type llvmtypeele2 is toseq:seq.int

function hash(a:llvmtypeele2)int hash.toseq.a

function =(a:llvmtypeele2, b:llvmtypeele2)boolean toseq.a = toseq.b

Function i64 int addorder.llvmtypeele2.[7, 64]

Function i32 int addorder.llvmtypeele2.[7, 32]

Module seq8.T

for testing not standard sequence optimization. new([1, 128])should be reduce to constant and if non standard sequence 
is not detected will give new([1, 128])_2 instead of 128. 

use standard

use seq.T

type seq8 is sequence, flda:seq.T, fldb:int

function _(a:seq8.T, i:int)T(flda.a)_i

Function newseq8(a:seq.T)seq.T toseq.seq8(length.a, a, 15) 