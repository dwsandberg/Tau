Module testseq

use bits

use testpackedseq.byte

use seq.seq.int

use sparseseq.int

use real

use encoding.seedtrack

use seq.seedtrack

use standard

use testpackedseq.typereal

use testpackedseq.typerec2

use otherseq.word

use testpackedseq.seq.word

use testpackedseq.word

type seedtrack is key:int, val:int

function =(a:seedtrack, b:seedtrack) boolean key.a = key.b

function hash(a:seedtrack) int key.a

Function getint(size:int) int
let p = last.encodingdata:seedtrack
let d = pseudorandom.val.p
let c = encode.seedtrack(key.p + 1, d)
d mod size

type typerec2 is a:int, b:int

function get:typerec2 typerec2 typerec2(getint.1000, getint.1000)

function =(x:typerec2, y:typerec2) boolean a.x = a.y ∧ b.x = b.y

type typereal is a:real

function get:typereal typereal typereal.toreal.getint.1000

function =(a:typereal, b:typereal) boolean a.a = a.b

function get:word word toword.getint.1000

function get:seq.word seq.word constantseq(getint.10, get:word)

function get:byte byte tobyte.getint.256

Function testseq seq.word
let EOL = "/br"
let a = encode.seedtrack(1, 987)
let all = 
 check:seq.byte(1, 22) + check:seq.byte(1, 8) + EOL + check:seq.typereal(8, 17)
 + check:seq.typereal(8, 8)
 + EOL
 + check:seq.seq.word(8, 17)
 + check:seq.seq.word(8, 8)
 + EOL
 + check:seq.word(8, 17)
 + check:seq.word(8, 8)
 + EOL
 + check:seq.typerec2(16, 17)
 + check:seq.typerec2(16, 8)
 + EOL
 + sparsecheck
if "FAIL"_1 ∉ all then "PASS testseq" else "FAIL testseq $(all)"

Function sparsecheck seq.word
let b = 
 for acc = sparseseq.101
  , @e ∈ subseq(random(randomseq(567, 54), 1, empty:seq.seq.int), 1, 1200)
 do
  check(acc, @e)
 /for (acc)
"Pass Sparse Sequence"

function check(s:seq.int, r:seq.int) seq.int
let i = r_1 mod 30 + 1
let c = replaceS(s, i, r)
assert subseq(s, 1, i - 1) = subseq(c, 1, min(i - 1, length.s)) report "FAIL1"
assert subseq(s, i + length.r, length.r) = subseq(c, i + length.r, length.r)
report "FAIL2"
assert subseq(c, i, i + length.r - 1) = r report "FAIL3"
c

function random(s:seq.int, i:int, result:seq.seq.int) seq.seq.int
if i > length.s then
 result
else
 let len = s_i mod 5 + 2
 random(s, i + len, result + subseq(s, i, i + len - 1)) 