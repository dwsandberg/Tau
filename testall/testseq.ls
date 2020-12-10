#!/usr/local/bin/tau ; use testseq ; testseq


module testseq

use encoding.ccc

use seq.encodingpair.ccc

use seq.ccc

use seq.seq.int

use seq.int

use set.int

use real

use stdlib

use seq.typereal

use testpackedseq.typereal

use seq.typerec2

use testpackedseq.typerec2

use otherseq.word

use otherseq.seq.word

use seq.seq.word

use testpackedseq.seq.word

use seq.word

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
 if not ("FAIL"_1 in (w+x+y+z)) then "PASS testseq" else "FAIL testseq"+w+x+y+z

  



module testpackedseq.T

use otherseq.T

use process.T

use seq.T

use stacktrace

use stdlib

use testseq

unbound get:T T

unbound =(T,T) boolean

 
Function check:seq.T seq.word
let unpack = random:seq.T(18)
let pack = packed.unpack
let x = if sizeoftype:T = 1 then""else"packed"
  if (length.pack > 9999 ∨ seqkind.pack = x + toword.length.unpack) &and pack=unpack then "PASS"+toword.length.pack
  else "FAIL"+toword.length.pack
  
Function random:seq.T(depth:int)seq.T
 if depth ≤ 0 then base:seq.T
 else
  let r = random:seq.T(depth - 1 - getint.2)
  + random:seq.T(depth - 1 - getint.2)
   if length.r < 50 ∨ getint.10 ≠ 2 then r
   else fastsubseq(r, 2, length.r - 1)

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
  else if t = getseqtype.constantseq(1, get:T)then"const"
  else if ispseq.a then"pseq"
  else if t = getseqtype.packed.constantseq(1, get:T)then"packed" + toword.length.a
  else if t = getseqtype.fastsubseq(constantseq(100, get:T), 3, 800)then"fastsub"
  else
   "unknown" + decodeaddress.getseqtype.a + "//"
   + decodeaddress.getseqtype(constantseq(1, get:T) + constantseq(1, get:T))

Function seqstruct(a:seq.T)seq.word
 let kind = seqkind.a
  if kind = "pseq"then
  let p = to:pseq.T(a)
    "(" + seqstruct.a.p + seqstruct.b.p + ")"
  else if kind = "fastsub"then
  let p = to:fastsubseq.T(a)
    "(" + "fastsub" + seqstruct.data.p + ")"
  else kind 