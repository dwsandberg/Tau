#!/usr/local/bin/tau

Module basewords



use stdlib


use seq.encodingrep.seq.int

use seq.seq.encodingrep.seq.int

use seq.int

use seq.seq.int

use encoding.seq.int

use fileio

use reconstructseq.encodingrep.seq.int

use packedseq.int 

type place is record this:seq.int,offset:int, data:seq.int

function addseq(p:place,c:seq.int) place   place(this.p+next.p,offset.p,data.p+[0,length.c]+c)

function addint(p:place,c:int) place place(this.p+c,offset.p,data.p)

function add(p:place,e:encodingrep.seq.int) place
     addint(addseq(addint(p,code.e),data.e),hash.e)
     
function add(p:place,s:seq.encodingrep.seq.int) place
  let  q=place([0,length.s ],next.p+length.s * 3+2,empty:seq.int)
  let r=@(add,identity,q,s)
        place(this.p+next.p,offset.p,this.r+data.r)
    



function next(p:place) int offset.p+length.data.p

function index(a:xx.encodingrep.seq.int,i:int)   encodingrep.seq.int
   let index=  (data.a)_( 3 * i +1)
   let len= (data.a)_(index+2)
   let s= subseq(data.a,index+3,index+3+len-1)
  encodingrep((data.a)_(3 * i),s,(data.a)_(3 * i +2))

Function createbasewords seq.word  
  let l=all.getinstance.wordencoding
  let i=createbase("wordbase.data",l)
   let x = all.getwordbase(getfile2("wordbase.data"))
  if l =x  then "OK" else "DIFF"
    
  
 
   
Function createbase(filename:seq.word,l:seq.encodingrep.seq.int) int
let  b=data.add(place(empty:seq.int,0,empty:seq.int),l)
 createfile(filename,[0,0]+b)
 

Function getwordbase(g:fileresult) encodingstate.seq.int
        add(getinstance.wordencoding,newxx(data.g,encodingrep(0,[0],0)))
        

module reconstructseq.T
  
  use stdlib
  
  use seq.int
 
type xx is sequence length:int,data:seq.int, k:T

Function data(s:xx.T) seq.int export

Function length(s:xx.T)int export

Function index(s:xx.T, i:int)T  unbound


Function_(s:xx.T, i:int)T  index(s,i)

  Function newxx(data:seq.int,a:T) seq.T
  toseq.xx(data_2, data,a) 

    
 

