Module testfileio

use IO2

use UTF8

use bits

use checking

use standard

use textio

use otherseq.byte

use seq.byte

use otherseq.int

use seq.int

use seq.word

use seq.seq.word

use process.seq.seq.word

Function testfileio seq.word
let y = 
 [t5501
 , t5502
 , t522
 , message.process.getfile:seq.seq.word("..") = "Error opening file:.."
 ]
check(y, "testfileio")

function t5502 boolean
{OPTION INLINE}
let data = arithseq(30044, 2, 7)
let f = createfile("tmp/testi.dat", data)
let r = getfile:int("tmp/testi.dat")
data = r

function t5501 boolean
{OPTION INLINE}
let text = ["this is a test", "line 2"]
let f = createfile("tmp/testw.txt", text_1 + encodeword.[char.10, char.10] + text_2)
getfile:seq.seq.word("tmp/testw.txt") = text

function *(i:int, b:byte)byte tobyte(i * toint.b)

function +(i:byte, b:byte)byte tobyte(toint.i + toint.b)

function filetest(i:int)boolean
{OPTION INLINE}
let data = arithseq(i, tobyte.1, tobyte.48)
let a = createfile("tmp/test.txt", data)
data =  getfile:byte("tmp/test.txt")

function t522 boolean
for acc = true, @e ∈ arithseq(9, 1, 4)do acc ∧ filetest.@e /for(acc) 