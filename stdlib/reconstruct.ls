Module reconstruct

use stdlib

use packedseq.int

use persistant

Decode Functions

Function relocate(ws:seq.word, d2:seq.int) address.int 
 // d2 format is [ wordthread start, offsetthread start, unused]+ actual data]// 
  // initwordset is called before relocate // 
  // new version // 
  let discard = wordthread(d2, ws, d2_1)
  let discard2 = offsetthread(d2, d2_2)
   setfld(setfld(setfld(getaddress(d2,2),0),0),0)

function wordthread(a:seq.int, ws:seq.word, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
  let discard = setfld(getaddress(a,i+1), encoding(ws_getb.d))
  wordthread(a, ws, getlink.d)

function offsetthread(a:seq.int, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
  let discard = setfld(getaddress(a,(i+1)), toT.getaddress(a,1+getb.d))
  offsetthread(a, getlink.d)


/function cast2int(address.int)int builtin






