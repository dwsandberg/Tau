Module testfileio

use UTF8

use bits

use checking

use fileio

use standard

use textio

use otherseq.byte

use seq.byte

use otherseq.int

use seq.int

use seq.word

use seq.seq.word

Function testfileio seq.word
let y = [ t5501, t5502, t522]
check(y,"testfileio")

function t5502 boolean
let data = arithseq(30044, 2, 7)
let f = createfile("testi.dat", data)
let r = getfile:int("testi.dat")
length.r = length.data ∧ data = r

function t5501 boolean
let text = ["this is a test","line 2"]
let f = createfile("testw.txt", text)
gettext."testw.txt" = text

function *(i:int, b:byte)byte tobyte(i * toint.b)

function +(i:byte, b:byte)byte tobyte(toint.i + toint.b)

function filetest(i:int)boolean
let name ="test" + toword.i + ".txt"
let a = createfile(name, arithseq(i, tobyte.1, tobyte.48))
fileexists.name ∧ i = length.getfile:byte(name)

Function t522 boolean for acc = true, @e ∈ arithseq(9, 1, 4)do acc ∧ filetest.@e /for(acc) 