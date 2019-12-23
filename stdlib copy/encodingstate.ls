       
module invertedseq.T

    type encodingrep is record data:T,hash:int,code:int
   
   type invertedseq is record encodetable:seq.seq.encodingrep.T, 
             count:int,
               decodetable:seq.seq.encodingrep.T,
               all:seq.encodingrep.T
               
            

Function data(encodingrep.T) T export

Function code(encodingrep.T) int export

Function all(invertedseq.T ) seq.encodingrep.T export

               


use stdlib
              
use seq.T
 
use seq.encodingrep.T
 
use seq.seq.encodingrep.T
 
use seq.int
 
               
Function hash(T)int unbound

Function =(T, T)boolean unbound

 Function add(h:invertedseq.T,a:T) invertedseq.T  add(h,1,a)


Function add(h:invertedseq.T,dummy:int, data:T)invertedseq.T
 let hashsize=length.encodetable.h
 if 3 * count.h > 2 * hashsize 
  then 
   let e4=encodetable.h+encodetable.h
   let d4=decodetable.h+decodetable.h
  add(invertedseq(e4,count.h,d4,all.h),dummy,data)
   else 
    let hashval=hash.data mod hashsize + 1
    let l1=(encodetable.h)_hashval
     if @(max,subfindcode.data,0,l1)> 0 then // already present // h
     else  
      let code=// uid //  count.h+1 
     let codehash=hash.code mod hashsize + 1
     let newele=encodingrep(data,hashval,code)
     let l2=@(addcode(hash.code, hashsize), identity,[ newele], (decodetable.h)_codehash)
     if (length.l2=0) then 
      // code was already used. Try new code //
     add(h,dummy,data)
     else  
    invertedseq(replace(encodetable.h, hashval, @(+, cleanlist(newele, hashsize), [ newele], l1)),
       count.h+1,replace(decodetable.h, codehash, l2),
       all.h+newele)


Function mapping(h:invertedseq.T) seq.T
    @(+, data,empty:seq.T,     all.h)

Function lookup(data:T,h:invertedseq.T ) int
@(max,subfindcode.data,0,encodetable(h)_(hash.data  mod length.encodetable.h + 1)  )

function subfindcode(v:T, a: encodingrep.T ) int 
 if v = data.a then code.a else 0

 
/Function decode( h:invertedseq.T,code:int) seq.T 
 @(+, ele4.code, empty:seq.T, decodetable(h)_(hash.code mod length.decodetable.h + 1))

function ele4(v:int, a: encodingrep.T ) seq.T if v =code.a then [data.a] else empty:seq.T
 
 

function cleanlist(e:encodingrep.T, hashsize:int, a:encodingrep.T)seq.encodingrep.T 
 if  not(hash.e mod hashsize = hash.a mod hashsize)then empty:seq.encodingrep.T else [ a]


 Function invertedseq(v:T)invertedseq.T 
 let x=constantseq(256, empty:seq.encodingrep.T)
 invertedseq(x,0,x, empty:seq.encodingrep.T)
 
 Function invertedseq(size:int,v:T)invertedseq.T 
 let x=constantseq(size, empty:seq.encodingrep.T)
 invertedseq(x, 0,x,empty:seq.encodingrep.T)

function addcode(code:int, hashsize:int,x:seq.encodingrep.T,e:encodingrep.T) seq.encodingrep.T
       if length.x=0  &or code.e=code then empty:seq.encodingrep.T
       else if not (hash.code mod hashsize=hash.code.e mod hashsize ) then x
       else x+e 
         
         
Function analyze(t:invertedseq.T)   seq.word
   "numele=" +toword.length.all.t +"encodecounts"+ counts(encodetable.t,1,0,0,0)
   +"decodeconuts"+ counts(decodetable.t,1,0,0,0)
      
function counts(s:seq.seq.encodingrep.T,i:int,one:int,two:int,big:int) seq.word
  if i > length.s then
   @(+,toword,"",[length.s,one,two,big])
  else
    let t=length(s_i)
    if t=0 then counts(s,i+1,one,two,big)
    else if t=1 then counts(s,i+1,one+1,two,big)
      else if t=1 then counts(s,i+1,one,two+1,big)
      else  counts(s,i+1,one,two,big+1)
      
Function reconstruct(all:seq.encodingrep.T) invertedseq.T
let x=constantseq(2 * length.all, empty:seq.encodingrep.T)
 let t=invertedseq(x, length.all,x,all)
    @( XX(2 * length.all),identity,t,all)

function XX(hashsize:int,h:invertedseq.T,a:encodingrep.T) invertedseq.T
    let codehash=code.a mod hashsize+1
       let datahash=hash.a mod hashsize+1
    invertedseq(replace(encodetable.h, datahash, (encodetable.h)_datahash+a),count.h,
   replace(decodetable.h, codehash, (decodetable.h)_codehash+a),all.h)
  
Function getinstance(erec:erecord.T)invertedseq.T builtin.STATE.usemangle 


Function mapping2(erec:erecord.T)seq.T  mapping.getinstance.erec

Function decode(t:encoding.T, erec:erecord.T)T (mapping.getinstance.erec)_(encoding.t)

Function findencode(t:T, erec:erecord.T)seq.T
    let inst= getinstance.erec
    let x=lookup(t,inst) 
    if x = 0 then empty:seq.T else  [(mapping.inst)_x]

