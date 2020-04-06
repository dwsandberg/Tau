Module persistantseq.T

/use encoding.T

use seq.T

use ipair.linklists2

use seq.ipair.linklists2

use llvm

use persistant

use stdlib


function addrecord(ipair.linklists2, s:T)ipair.linklists2 unbound



Function addseq(l:ipair.linklists2,s:seq.T) ipair.linklists2
     let t=   @(xxx,identity,[l],s)
     ipair(addobject(@(+,  objectref,[C64.0 , C64.length.s],subseq(t,2,length.s+1))),value.l)
  
  
function     xxx(l:seq.ipair.linklists2, s:T) seq.ipair.linklists2
      l+  addrecord( last.l,s) 
     
   