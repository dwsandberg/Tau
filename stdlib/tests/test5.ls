#!/usr/local/bin/tau

run test5 test5

Module test5

use UTF8

use checking

use fileio

use otherseq.int

use seq.int

use standard

use textio

use seq.seq.word

use seq.word

Function test5 seq.word
let y = [ t5501, t5502, t522, t509]
 check(y,"test5")

function t5502 boolean
let data = arithseq(30044, 2, 7)
let f = createfile("testi.dat", data)
let r = getfile:int("testi.dat")
 length.r = length.data
 ∧ data = r

function t5501 boolean
let text = ["this is a test","line 2"]
let f = createfile("testw.txt", text)
 gettext."testw.txt" = text

use bits

use seq.byte

function filetest(i:int)boolean
 let name ="test" + toword.i + ".txt"
 let a = createbytefile(name, arithseq(i, 1, 48))
  fileexists.name ∧ i = length.getfile:byte(name)

Function t522 boolean arithseq(9, 1, 4) @ ∧(true, filetest.@e)

function modr(a:int, b:int)int b mod a + 1

function incrementcount(s:seq.int, i:int)seq.int replace(s, i, s_i + 1)

function t509 boolean
let s = randomseq(3456, 100001) @ +(empty:seq.int, modr(100, @e))
@ incrementcount(constantseq(100, 0), @e)
let totalcounts = s @ +(0, @e)
 length.s = 100 ∧ totalcounts = 100001