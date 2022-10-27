Module testencoding

Testing encodings

use checking

use set.int

use process.set.int

use standard

use process.testdeep

use encoding.testrecord

use seq.testrecord

use process.seq.testrecord

use seq.seq.word

use tree.seq.word

function deepcopytest(a:testdeep) testdeep result.process.identity.a

function deepcopytest(a:set.int) set.int result.process.identity.a

function identity(a:set.int) set.int a

function identity(a:testdeep) testdeep a

function deepcopytest(a:int) int a

Export +(i:int, b:int) int

function =(a:testrecord, b:testrecord) boolean key.a = key.b

function hash(a:testrecord) int key.a

Export type:testrecord

function add(b:seq.word) int
let x = encode.testrecord(length.encodingdata:testrecord + 1, b)
1

type testrecord is key:int, body:seq.word

function list(a:seq.testrecord) seq.seq.word
for acc = empty:seq.seq.word, @e ∈ a do acc + body.@e /for (acc)

Function testencoding seq.word
{must export this module so encoding type can be figured out}
let p = process.process1
if aborted.p then "Failed encoding $(message.p)"
else
 let s1 = list.result.p
 let z = for acc = 0, @e ∈ ["firstadd", "secondadd"] do acc + add.@e /for (acc)
 let s2 = list.result.process.process1
 let s3 = list.encodingdata:testrecord
 check([3 = deepcopytest.3
 , asset.[3, 7, 9] = deepcopytest.asset.[3, 7, 9]
 , deepcopytest.testdeep1 = testdeep1
 , s1 = ["A1", "B2", "C3", "D4", "E5"]
 , s2 = ["firstadd", "secondadd"] + s1
 , s3 = s2
 ]
 , "encoding"
 )

Function process1 seq.testrecord
let discard = 
 for acc = 0, @e ∈ ["A1", "B2", "C3", "D4", "E5"] do acc + add.@e /for (acc)
encodingdata:testrecord

type testdeep is fld1:seq.word, fld2:tree.seq.word, fld3:seq.char

function testdeep1 testdeep
testdeep("A BC DEF", tree("LIT 1", [tree."PARAM 1"]), decodeword."TEST"_1)

function =(a:testdeep, b:testdeep) boolean
fld1.a = fld1.b ∧ fld2.a = fld2.b ∧ fld3.a = fld3.b 