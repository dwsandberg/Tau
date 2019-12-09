Module encoding.T

use seq.encodingrep.T

use seq.seq.encodingrep.T

use stdlib

use seq.T


type encodingstate is record encodingtable:seq.seq.encodingrep.T, elecount:int,mapping:seq.T,
   decodetable:seq.seq.encodingrep.T


   type encodingrep is record code:int,data: T ,hash:int 
 


Function hash(T)int unbound

Function =(T, T)boolean unbound

function ele(v:T, a:encodingrep.T)int if v = data.a then code.a else 0

function ele2(eletoadd:encodingrep.T, tablesize:int, a:encodingrep.T)seq.encodingrep.T 
 if data.a = data.eletoadd ∨ not(hash.eletoadd mod tablesize = hash.a mod tablesize)
 then empty:seq.encodingrep.T else [ a]
 
function ele4(eletoadd:encodingrep.T, tablesize:int, a:encodingrep.T)seq.encodingrep.T 
 if code.a = code.eletoadd ∨ not(hash.code.eletoadd mod tablesize = hash.code.a mod tablesize)
 then empty:seq.encodingrep.T else [ a]




Function lookup(data:T, h:encodingstate.T)int 
 @(max, ele.data, 0, encodingtable(h)_(hash.data mod length.encodingtable.h + 1))



Function add(h:encodingstate.T, i:int, v:T)encodingstate.T add(h,v )


Function add(h:encodingstate.T, v:T)encodingstate.T 
 if 3 * elecount.h > 2 * length.encodingtable.h 
  then 
   let t=encodingtable.h
   add(encodingstate(t+t+t+t, elecount.h,mapping.h,decodetable.h), v)
  else 
   let code=length.mapping.h+1
   let tablesize=length.encodingtable.h
   let p=encodingrep(code, v,hash.v)
   let hashofdata=hash.p mod tablesize + 1 
    encodingstate(replace(encodingtable.h, hashofdata, @(+, ele2(p, tablesize), [ p], 
 encodingtable(h)_hashofdata)), 
 elecount.h + 1,mapping.h+data.p,decodetable.h
 )
 
 
 replace(decodetable.h, hashofdata, @(+, ele2(p, tablesize), [ p], 
 decodetable(h)_hashofdata)))

 
 function getinstance(erec:erecord.T)encodingstate.T builtin.STATE.usemangle 


Function mapping2(erec:erecord.T)seq.T  mapping.getinstance.erec

Function decode(t:encoding.T, erec:erecord.T)T (mapping.getinstance.erec)_(encoding.t)



Function findencode(t:T, erec:erecord.T)seq.T
    let inst= getinstance.erec
    let x=lookup(t,inst) 
    if x = 0 then empty:seq.T else  [(mapping.inst)_x]




