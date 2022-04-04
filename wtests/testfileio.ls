Module testfileio

use IO2

use UTF8

use bits

use checking

use standard

use textio

use IO2

use otherseq.byte

use seq.byte

use otherseq.int

use seq.int

use seq.word

use seq.seq.word

use process.seq.seq.word

Function testfileio seq.word
{OPTION INLINE :INLINE is used in this module so that wasm code will be intepreted}
let y = 
 [t5501
 , t522
, {message.process.gettext("..")="Error opening file:.."}true]
check(y, "testfileio")


Function createfile(filename:seq.word, s:seq.word)int  
createfile(filename, toseqbyte.toUTF8.s)

function t5501 boolean
{OPTION INLINE}
let text = ["this is a test", "line 2"]
let f = createfile("tmp/testw.txt", text_1 + encodeword.[char.10, char.10] + text_2)
breakparagraph.getfile:byte("tmp/testw.txt") = text

function *(i:int, b:byte)byte tobyte(i * toint.b)

function +(i:byte, b:byte)byte tobyte(toint.i + toint.b)

function filetest(i:int)boolean
{OPTION INLINE}
let data = arithseq(i, tobyte.1, tobyte.48)
let a = createfile("tmp/test.txt", data)
data =  getfile:byte("tmp/test.txt")

function t522 boolean
{OPTION INLINE}
for acc = true, @e ∈ arithseq(9, 1, 4)do acc ∧ filetest.@e /for(acc) 