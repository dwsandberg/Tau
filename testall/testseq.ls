#!/usr/local/bin/tau

run testseq testseq

module testseq 


use stdlib

use seq.seq.int

use seq.int

use set.int

use seq.ccc

use encoding.ccc

use real


use seq.typereal

use seq.typerec2 

use seq.seq.word

use seq.word


use testpackedseq.typereal

use testpackedseq.seq.word

use testpackedseq.typerec2 

use testpackedseq.word

use otherseq.seq.word

use otherseq.word

use encoding.ccc

type ccc is record key:int ,val:int


function assignencoding(a:int, b:ccc) int assignrandom(a,b)

function =(a:ccc, b:ccc) boolean key.a=key.b

function hash(a:ccc) int key.a

use seq.encodingpair.ccc




Function getint(size:int) int  
let p=data.last.encoding:seq.encodingpair.ccc 
let d=pseudorandom( val.p) 
let c=encode(ccc(key.p+1,d))
d mod size
  
type typerec2 is record a:int,b:int

function get:typerec2  typerec2    typerec2(getint.1000,getint.1000)

function =(x:typerec2,y:typerec2) boolean a.x=a.y &and b.x=b.y

type typereal is record a:real

function get:typereal typereal    typereal.toreal.getint.1000 

function =(a:typereal,b:typereal)  boolean a.a=a.b  

function get:word  word toword.getint.1000 

function get:seq.word seq.word  constantseq(getint.10,get:word)


 Function testseq seq.word   
     let a=encode(ccc(1,987))
      // @(+,toword,"",[getint(10000),getint(10000)]) //
    let z=check:seq.typerec2 
    let y=check:seq.word 
    let w=check:seq.typereal
    let x=check:seq.seq.word
    [toword.length.z,toword.length.y,toword.length.w,toword.length.x] 

  

module testpackedseq.T

use stdlib

use seq.T

use otherseq.T

use stacktrace

unbound get:T T 

use process.T

use testseq

Function check:seq.T seq.T
 let unpack=random:seq.T(17)
 let pack=packed.unpack
 let x=if sizeoftype:T=1 then "" else "packed"  
 assert length.unpack=length.pack &and (length.pack > 9999 &or seqkind.pack=x+toword.length.unpack) report "ERROR"
 unpack

Function  random:seq.T(depth:int)  seq.T   
 if depth &le 0 then base:seq.T
 else 
 let r= random:seq.T(depth-1-getint.2) +  random:seq.T(depth-1-getint.2)
 if length.r < 50 &or getint.10 &ne 2 then r else
     fastsubseq(r,2,length.r-1)
 
getint(depth / 3)

Function base:seq.T  seq.T
   let i=getint.6
   if i=0 then empty:seq.T
   else if i=1 then [get:T]
   else if i=2 then [get:T,get:T]
   else if i=4 then [get:T,get:T,get:T,get:T,get:T ]
   else if i=5 then [get:T,get:T,get:T,get:T,get:T,get:T]
   else  constantseq(getint.7,get:T)


function  seqkind(a:seq.T) seq.word
   let t=getseqtype.a
   if t=0 then [toword.length.a] else
   if t=getseqtype.constantseq(1,get:T) then "const"
   else if ispseq.a then "pseq"
   else if t=getseqtype.packed.constantseq(1,get:T) then "packed"+toword.length.a
   else if t=getseqtype.fastsubseq(constantseq(100,get:T),3,800) then "fastsub"
   else "unknown"+decodeaddress.getseqtype.a+"//"+decodeaddress.getseqtype.(constantseq(1,get:T)+constantseq(1,get:T))
   
Function seqstruct(a:seq.T) seq.word
 let kind= seqkind.a
 if kind="pseq" then
   let p= to:pseq.T(a) 
    "("+seqstruct(a.p)+seqstruct(b.p)+")"
 else if kind="fastsub" then
   let p= to:fastsubseq.T(a) 
    "("+"fastsub"+seqstruct(data.p)+")"
 else kind