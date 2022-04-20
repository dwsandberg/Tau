Module object01 

use standard

use bits

use seq.byte 

use set.tableentry

use ptr

use seq.seq.int

use seq.int

use bitcast.seq.int

use bitcast.word

use bitcast.int

use bitcast.ptr


type   tableentry  is  key:seq.int,new:int
  
 type  finished/this is finished:seq.seq.int,this:int,table:set.tableentry
 
function  ?(a:tableentry,b:tableentry) ordering 
   key.a ? key.b
   
   use otherseq.int
   
   use seq.seq.byte
   
    use file


    

 
 
  Function %(i:int) seq.word [toword.i]
     
 function  %(i:byte) seq.word [toword.toint.i]
 
Function %(a:mytype) seq.word print.a

use set.mytype


Function fix5(a0:seq.seq.mytype)seq.seq.mytype
 let root=first.a0
let a = [[typeword], [typeint], [typereal]] + 
   if length.root=2 /and isseq.root_2 then  [[root_2,parameter.root_2]]+a0 else  a0
 let singlerow=for singlerow = empty:seq.seq.mytype, row ∈ a do
  if length.row = 2 then {∧ not.isseq.last.row ∧ not.isseq.first.row then} singlerow + row else singlerow
 /for(singlerow)
let x= if isempty.singlerow then 
 a
 else
  {remove types not represented by a record}
  for result = empty:seq.seq.mytype,  row2 ∈ a do
    result+for acc = [first.row2], t ∈ row2 << 1 do acc + sub(t, singlerow)/for(acc)
   /for( for acc=empty:seq.seq.mytype, row /in result do if length.row=2 /and not.isseq.row_1 then acc
   else acc+row /for(acc))
   { add types used but not defined}
  for defs=empty:seq.mytype,used=empty:seq.mytype, def /in x do
   next(defs+first.def,used+def << 1)
   /for(  
   for acc=x, new /in toseq(asset.used \ asset.defs)  do acc+[new] /for(acc))

function sub(t:mytype, singlerow:seq.seq.mytype)mytype
if t ∈ [typeint, typeword, typereal]then t
else if isseq.t then seqof.sub(parameter.t, singlerow)
else
 for acc = t, row ∈ singlerow do if t = first.row then last.row else acc /for(acc)


use bitcast.seq.word

Function outrec(inobj:ptr,allpatterns:seq.seq.int) seq.seq.int
   allpatterns+finished.outrec(empty:seq.seq.int,inobj,prepare2.allpatterns,4,empty:set.tableentry)
   
   
function figuretype(packedsize:int,pattern:seq.int) word
if packedsize=1 then 
       if pattern_2 < 4 then "int int real"_(pattern_2) else  "ptr"_1 
else   "packed2 packed3 packed4 packed5 packed6"_(packedsize-1) 

function outrec(finished0:seq.seq.int,inobj:ptr,allpatterns:seq.seq.int,patternidx:int
,table0:set.tableentry) finished/this
   let pattern=allpatterns_patternidx
 { assert %.pattern /in ["5 5 2","0 1"]  report "herexx"+ %.pattern +%.length.finished0
 } let isseq=first.pattern=0 
   let packedsize= if isseq /and between(length.pattern,3,6+1)  then length.pattern - 1 else 1
   let obj= if not.isseq then inobj else  packobject(figuretype(packedsize,pattern),inobj)
     let fldtypes=if isseq then  
        let obj0=bitcast:seq.int(obj) 
        constantseq(length.obj0 * packedsize,pattern << 1) 
   else pattern 
   {assert %.pattern /in ["5 5 2"]  report "hereyy"+ %.pattern +%.length.finished0
   }for   acc=if first.pattern=0 then [patternidx,length.bitcast:seq.int(obj)] else [patternidx]
      , idx=if first.pattern=0 then 2 else 0,stkcount=0,finished=finished0,table=table0
      ,typ /in fldtypes do
           { assert  cardinality.table < 0 report "xxx"+toword.cardinality.table+%.typ
            }  if typ /in {int real} [2,3] then 
              next(acc+  fld:int(obj,idx),idx+1,stkcount,finished,table)
           else if typ={word} 1  then
              {assert cardinality.table < 0 report "here"}
              let e= lookup(table,tableentry([0,fld:int(obj,idx)],0))
               if isempty.e then
                 next (acc+ (cardinality.table+1)
                 ,idx+1,stkcount
                 ,finished+vector([char(1)]+decodeword.fld:word(obj,idx))
                 ,table+ tableentry([0,fld:int(obj,idx)],cardinality.table+1)
                 )
              else 
               next(acc+ new.e_1 ,idx+1,stkcount,finished,table)
           else 
               {assert stkcount /in [0,1] report "XX"+toword.stkcount}
              let t=outrec(finished,fld:ptr(obj,idx),allpatterns,typ,table)
             next(acc+(stkcount+1),idx+1,stkcount+1,finished.t,table.t)
           /for( finished/this (finished+vector.(acc+stkcount),0,table))
           
use stack.ptr

use seq.ptr

use otherseq.int
                      
Function  inrec(inrecs:seq.seq.int) ptr
     let allpatterns=prepare2.inrecs
     for stk=empty:stack.ptr,map=empty:seq.int,  rec /in  inrecs << length.allpatterns do 
       if first.rec=1 then 
        { add word entry to map }
         next(stk,map+hash.encodeword.for acc=empty:seq.char ,i /in rec << 1 do acc+char.i /for(acc))
     else 
      let flds=top(stk,last.rec)
      let pattern=allpatterns_first.rec
      let isseq=pattern_1=0
      let packedsize= if isseq then length.pattern - 1 else 1
      let fldtypes=if isseq then  
        constantseq(rec_2 * packedsize,pattern << 1) 
       else pattern
       let blksize=  20
       let myblksz = if length.fldtypes+3 /le  blksize then blksize
           else   blksize / packedsize * packedsize
       assert length.fldtypes < 8151 report "object too big"+toword.length.fldtypes
       assert  length.rec=length.fldtypes+if isseq then 3 else 2  report "record format error" 
    let obj=allocatespace(min(length.fldtypes,myblksz)+if isseq then 2 else 0)
    let finalobj=for p=if isseq then set(set(obj,if packedsize=1 then 0 else 1),
    min(rec_2,myblksz / packedsize)) else obj
         , i=if isseq then 3 else 2
         , objs=empty:seq.ptr
         , typ /in fldtypes do  
         if i-3=myblksz *(length.objs+1) then 
           let   newblksize=  min(length.fldtypes - myblksz *(length.objs+1),myblksz)
             {assert i /in  [12,21] report %.i+%.newblksize+%.length.fldtypes }
           let newobj=allocatespace( newblksize+  2  )
            let newp=set(set(newobj,if packedsize=1 then 0 else 1),newblksize)
            next(if typ /in {int real} [2,3] then set(newp,  rec_i) 
             else if typ={word} 1  then set(newp,map_(rec_i)) 
             else    set(newp,flds_(rec_i)),i+1,objs+newobj)
         else 
        next(if typ /in {int real} [2,3] then set(p,  rec_i) 
             else if typ={word} 1  then set(p,map_(rec_i)) 
             else    set(p,flds_(rec_i)),i+1,objs)
    /for(  for acc=obj , o /in objs do cat(acc,o,figuretype(packedsize,pattern)) /for(acc))
    next(push(pop(stk,last.rec),finalobj),map)
    /for(top.stk)
       
    use LEBencoding   
       
 Function encode2(data:seq.seq.int) seq.byte       
  for  all=empty:seq.byte,     rec /in data do            
  all+for pos=true,   j /in rec while pos do  j /ge 0 /for(
   if pos then  for acc= empty:seq.byte , i /in rec do
       acc+ LEBu.i /for(LEBu(length.acc * 2)+acc)
   else for acc= empty:seq.byte , i /in rec do
       acc+ LEBs.i /for(LEBu(length.acc * 2+1) +acc))
  /for(LEBu.length.all+all) 
  
  Function decode2(b:seq.byte) seq.seq.int
 let  len=decodeLEBu(b,1)
 let  end=next.len+value.len
 {assert false report %.end+%.length.b}
 for  all=empty:seq.seq.int,next=next.len,t /in constantseq(value.len,0) 
   while next < end do
   let  r= decodeLEBu(b,next) 
   let val=value.r
    let endplace=next.r+ val / 2
   let pos=(val mod 2 = 0) 
    next(     for acc=empty:seq.int, place=next.r, t2 /in constantseq(val ,0) 
    while place < endplace do 
           let x= if pos then  decodeLEBu(b,place) else decodeLEBs(b,place) 
          { assert value.x /in [45,46,47] report "Z"+%.value.x+%.next.x+%.endplace}
          next(acc+value.x,next.x)
        /for(all+acc),endplace)
  /for(all) 
        
     
   


 function vector(a:seq.char) seq.int for acc=empty:seq.int,c /in a do acc+  toint.c /for(acc)
 
 /function vector(seq.byte) seq.byte empty:seq.byte

 function  vector(a:seq.int) seq.int  a 
    
     let t= LEB.a
     LEB.length.t+t
     

 ____________________________________
 
 
 use symbol2
 
 use seq.seq.mytype
 
 use seq.mytype
 
 use seq.seq.int
 

Function   formatTypeDef(defs:seq.seq.mytype) seq.seq.int
  prepare.for  acc=  empty:seq.seq.int , def /in defs do
       if isseq.first.def then  
          let idx=for idx=1,  d  /in defs  while first.d /ne parameter.first.def do idx+1
         /for(idx)
           acc+[0,idx]
      else  
        for  coded=empty:seq.int, t /in  def << 1 do
         let idx=for idx=1,  d  /in defs  while first.d /ne t do idx+1 /for(idx)
          coded+idx
         /for(acc+ for acc2= if isempty.coded then [length.acc+1,0] else  coded+0,c /in decodeword.first.print.first.def do acc2+toint.c /for(acc2)
       )
      /for( acc)
        
      
      
Function prepare2(patterns:seq.seq.int) seq.seq.int
      for acc=empty:seq.seq.int,   pat /in patterns   while  first.pat =0 do
            acc+removelabel(pat << 1)
    /for(acc)
  
  function removelabel(pat0:seq.int) seq.int
                for  acc2=[first.pat0], i /in pat0 << 1 while i /ne 0 do acc2+i /for(acc2)
  
      
function prepare(patterns:seq.seq.int) seq.seq.int
  for acc=empty:seq.seq.int,   pat /in patterns  do 
    acc+([0]+if first.pat=0 then
     let seqelementpat=  removelabel.patterns_(pat_2)
     if  not.between(length.seqelementpat,2 , {must match packed seqs in implementation}6 )
       /or first.seqelementpat=0 then pat 
     else 
       [ 0]+seqelementpat 
    else
     pat)
 /for(acc)
 

 
 use packit
      
     
module packit


use tausupport

use standard

use bitcast.seq.int

use seq.real

use seq.ptr

use seq.packed3


use bitcast.seq.real


use bitcast.seq.ptr

use bitcast.seq.packed3

Function cat(obj1:ptr,obj2:ptr,typ:word) ptr
   if typ /in "int" then toptr(bitcast:seq.int(obj1)+bitcast:seq.int(obj2))
 else if typ /in "real" then toptr(bitcast:seq.real(obj1)+bitcast:seq.real(obj2))
 else if typ /in "ptr" then 
  toptr(bitcast:seq.ptr(obj1)+bitcast:seq.ptr(obj2))
 else assert typ /in "packed3" report "packing cat not found"+typ
  toptr(bitcast:seq.packed3(obj1)+bitcast:seq.packed3(obj2))



Function packobject(typ:word,obj:ptr) ptr
 if typ /in "int" then toptr.blockIt.bitcast:seq.int(obj)
 else if typ /in "real" then toptr.blockIt.bitcast:seq.real(obj)
 else if typ /in "ptr" then toptr.blockIt.bitcast:seq.ptr(obj)
 else assert typ /in "packed3" report "packing not found"+typ
  toptr.blockIt.bitcast:seq.packed3(obj)
  

module objectio.T

use object01 

use standard

use bitcast.T

use seq.mytype

use symbol2


use seq.seq.int

use seq.byte

use bits



Builtin typestructure:T seq.seq.mytype


unbound =(T,T) boolean

Function outbytes:T(try:T) seq.byte 
let pat=formatTypeDef.fix5.typestructure:T
 encode2.outrec(toptr.try,pat)

Function inbytes:T(in:seq.byte) T 
 bitcast:T(inrec.decode2.in) 





 