#!/usr/local/bin/tau ; use testseq ; testseq

module testseq

use encoding.ccc

use seq.encodingpair.ccc

use seq.ccc

use seq.seq.int

use seq.int

use set.int

use sparseseq.int

use real

use standard

use seq.typereal

use testpackedseq.typereal

use seq.typerec2

use testpackedseq.typerec2

use otherseq.word

use otherseq.seq.word

use seq.seq.word

use testpackedseq.seq.word


use testpackedseq.word

type ccc is record key:int, val:int

function assignencoding(a:int, b:ccc)int assignrandom(a, b)

function =(a:ccc, b:ccc)boolean key.a = key.b

function hash(a:ccc)int key.a

Function getint(size:int)int
 let p = data.last.encoding:seq.encodingpair.ccc
 let d = pseudorandom.val.p
 let c = encode.ccc(key.p + 1, d)
  d mod size

type typerec2 is record a:int, b:int

function get:typerec2 typerec2 typerec2(getint.1000, getint.1000)

function =(x:typerec2, y:typerec2)boolean a.x = a.y ∧ b.x = b.y

type typereal is record a:real

function get:typereal typereal typereal.toreal.getint.1000

function =(a:typereal, b:typereal)boolean a.a = a.b

function get:word word toword.getint.1000

function get:seq.word seq.word constantseq(getint.10, get:word)

function xx(i:int) typerec2  typerec2( i,i * 2 )

Function testseq seq.word
let a = encode.ccc(1, 987)
  let w = check:seq.typereal  
 let x = check:seq.seq.word
 let y = check:seq.word
    let z = check:seq.typerec2  
 sparsecheck
 + if not("FAIL"_1 ∈ (w + x + y + z))then"PASS testseq"
 else"FAIL testseq" + w + x + y + z

Function sparsecheck seq.word 
let b =(for(@e ∈ subseq(random(randomseq(567, 54), 1, empty:seq.seq.int), 1, 1200), acc = sparseseq.101)check(acc, @e))
"Pass Sparse Sequence"

function  check(s:seq.int,r:seq.int) seq.int
     let i=r_1 mod 30+1 
      let c=replaceS(s,i,r)
  assert subseq(s, 1, i - 1) = subseq(c, 1, min(i - 1, length.s))report"FAIL1" 
   assert  subseq(s, i+length.r,length.r) =subseq(c, i+length.r,length.r) report "FAIL2"
    assert subseq(c, i, i + length.r - 1) = r report"FAIL3" 
      c
      
 function random (s:seq.int,i:int,result:seq.seq.int) seq.seq.int
    if i > length.s then result
 else
  let len = s_i mod 5 + 2
       random( s, i+len, result+subseq(s,i,i+len-1)) 

module testpackedseq.T

use otherseq.T

use process.T

use seq.T


use standard

use testseq

use tausupport


unbound get:T T

unbound =(T,T) boolean

Function check:seq.T seq.word
let unpack = random:seq.T(16)
let pack = packed.unpack
let x = if  getseqtype.pack = 1 then"packed"else""
 if(length.pack > 9999 ∨ seqkind.pack = x + toword.length.unpack) ∧ pack = unpack then
 "PASS" + toword.length.pack
  else "FAIL"+toword.length.pack
  
Function random:seq.T(depth:int)seq.T
 if depth ≤ 0 then base:seq.T
 else
 random:seq.T(depth - 1 - getint.2)
  + random:seq.T(depth - 1 - getint.2)
   

Function base:seq.T seq.T
let i = getint.6
 if i = 0 then empty:seq.T
 else if i = 1 then [ get:T]
 else if i = 2 then [ get:T, get:T]
 else if i = 4 then [ get:T, get:T, get:T, get:T, get:T]
 else if i = 5 then [ get:T, get:T, get:T, get:T, get:T, get:T]
 else constantseq(getint.7, get:T)

function seqkind(a:seq.T)seq.word
 let t = getseqtype.a
  if t = 0 then [ toword.length.a]
  else if t =1 then "packed" + toword.length.a
  else if t = getseqtype.constantseq(1, get:T)then"const"
  else if ispseq.a then"pseq"
  else if t = getseqtype.packed.constantseq(1, get:T)then"packed" + toword.length.a
  else 
   "unknown" 
   
   + decodeaddress.getseqtype.a + "//"
   + decodeaddress.getseqtype(constantseq(1, get:T) + constantseq(1, get:T))

Function seqstruct(a:seq.T)seq.word
 let kind = seqkind.a
  if kind = "pseq"then
  let p = to:pseq.T(a)
    "(" + seqstruct.a.p + seqstruct.b.p + ")"
  else  kind 