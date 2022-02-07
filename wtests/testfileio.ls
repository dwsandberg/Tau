#!/bin/bash  tau    webassembly  wmytests mytests Bquadratic .

Module testfileio

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

use IO2

Function testfileio seq.word 
{OPTION INLINE :INLINE is used in this module so that wasm code will be intepreted}
let y = [t5501, t5502, t522, {message.process.gettext("..")="Error opening file:.."}true]
check(y,"testfileio")

function t5502 boolean 
{OPTION INLINE}
let data = arithseq(30044, 2,7)
let f = createfile("testi.dat", data)
let r = getfile:int("testi.dat")
 data = r 

function t5501 boolean 
{OPTION INLINE}
let text = ["this is a test","line 2"]
let f = createfile("testw.txt", text_1 + encodeword.[ char.10, char.10] + text_2)
 gettext."testw.txt"=text 

function *(i:int, b:byte)byte tobyte(i * toint.b)

function +(i:byte, b:byte)byte tobyte(toint.i + toint.b)

function filetest(i:int)boolean 
{OPTION INLINE}
let data=arithseq(i, tobyte.1, tobyte.48)
let a = createfile("test.txt", data)
data =  getfile:byte("test.txt")

function t522 boolean
{OPTION INLINE}
{acc is using integer instead of boolean to work with wasm  }
for acc = 1, @e ∈ arithseq(9, 1, 4)do  acc * if filetest.@e then 1 else 0 /for( acc=1 ) 