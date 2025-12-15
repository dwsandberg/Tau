Module bug7

use seq8.int

use encoding.llvmtypeele2

use encoding.slot2

use standard

type slot2 is type:int, rec:seq.int, name:seq.word

function =(a:slot2, b:slot2) boolean
rec.a = rec.b ∧ type.a = type.b ∧ name.a = name.b

function hash(a:slot2) int hash.rec.a

Function c32(i:int) encoding.slot2 encode.slot2(i32, [45, i], "")

Function testbug7 seq.word
{since encodings have side effects it is not safe to use simple inline expansion of functions since the order of evaluation becomes important. Function c32 is the candiate for inline expansion. }
let discard0 = [i64, i32]
let z = c32.0,
if [i64, i32] = [1, 2] ∧ 128 = (newseq8.[1, 128]) sub 2 then "PASS bug7"
else "// FAILED bug7 /literal"

type llvmtypeele2 is toseq:seq.int

function hash(a:llvmtypeele2) int hash.toseq.a

function =(a:llvmtypeele2, b:llvmtypeele2) boolean toseq.a = toseq.b

Function i64 int addorder.llvmtypeele2.[7, 64]

Function i32 int addorder.llvmtypeele2.[7, 32] 