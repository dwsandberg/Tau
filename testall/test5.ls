#!/usr/local/bin/tau

run test5 standalonechars

Module test5

use UTF8

use checking

use fileio


use seq.word


use otherseq.int

use stdlib

use textio



use ipair.word

Function test5 seq.word
let y = [   t522,t509]
 check(y,"test5")



function filetest(i:int)boolean
 let name ="test" + toword.i + ".txt"
 let a = createbytefile(name, arithseq(i, 1, 48))
  fileexists.name ∧ i = length.getfile.name

Function t522 boolean @(∧, filetest, true, arithseq(9, 1, 4))

function modr(a:int, b:int)int b mod a + 1

function incrementcount(s:seq.int, i:int)seq.int replace(s, i, s_i + 1)

function print(i:ipair.word)seq.word [ toword.index.i] + ":" + value.i

function t509 boolean
let s = @(incrementcount, identity, constantseq(100, 0), @(+, modr(100), empty:seq.int, randomseq(3456, 100001)))
let totalcounts = @(+, identity, 0, s)
 length.s = 100 ∧ totalcounts = 100001