#!/usr/local/bin/tau

run test5 test5

Module test5

use UTF8

use bits

use checking

use fileio

use standard

use textio

use seq.byte

use otherseq.int

use seq.int

use seq.word

use seq.seq.word

Function test5 seq.word
let y = [ t5501, t5502, t522, t509]
 check(y,"test5")

function t5502 boolean
let data = arithseq(30044, 2, 7)
let f = createfile("testi.dat", data)
let r = getfile:int("testi.dat")
 length.r = length.data ∧ data = r

function t5501 boolean
let text = ["this is a test","line 2"]
let f = createfile("testw.txt", text)
 gettext."testw.txt" = text

function filetest(i:int)boolean
 let name ="test" + toword.i + ".txt"
 let a = createfile(name, for @e ∈ arithseq(i, 1, 48), acc = empty:seq.byte ,,, acc + tobyte.@e)
  fileexists.name ∧ i = length.getfile:byte(name)

Function t522 boolean for @e ∈ arithseq(9, 1, 4), acc = true ,,, acc ∧ filetest.@e

function modr(a:int, b:int)int b mod a + 1

function incrementcount(s:seq.int, i:int)seq.int replace(s, i, s_i + 1)

function t509 boolean
let s = for @e ∈ for @e ∈ randomseq(3456, 100001), acc = empty:seq.int ,,, acc + modr(100, @e), acc = constantseq(100, 0),,,
 incrementcount(acc, @e)
let totalcounts = for @e ∈ s, acc = 0 ,,, acc + @e
 length.s = 100 ∧ totalcounts = 100001