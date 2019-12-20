Module reconstruct

use bits

use packedseq.int

use stdlib

use encoding.seq.int

Function add2(h:encodingstate.seq.int,v:seq.encodingrep.seq.int) encodingstate.seq.int
// so add is included in stdlib //
 add(h,v)
 
 
Three Functions to pack two ints into 64 bits

function halfsize int // 2^31 // 2147483648

Function getlink(a:int)int toint(bits.a >> 31) - halfsize

Function packit(link:int, b:int)int toint(bits(halfsize + link)<< 31 ∨ bits.b)

Function getb(a:int)int toint(bits.a ∧ bits(halfsize - 1))

type xxx is record a:address.int, t:int

function valueofencoding (word)int builtin.NOOP 
 
Function print(a:address.int)int 
 // added so typedesc of address.int is processed correctly by declaring in type xxx // 
  let x = xxx(a, 100)
  3

Function relocate(ws:seq.word, d2:seq.int)address.int 
 // d2 format is [ wordthread start, offsetthread start, unused]+ actual data]// 
  // new version // 
  let discard = wordthread(d2, ws, d2_1)
  let discard2 = offsetthread(d2, d2_2)
  let discard3 = wordseqthread(d2, ws, d2_3)
  setfld(setfld(setfld(getaddress(d2, 2), 0), 0), 0)
  
Function relocateoffset(d2:seq.int) address.int
   let discard2 = offsetthread(d2, d2_2)
   setfld(setfld(getaddress(d2, 2),d2_1), 0)

function wordthread(a:seq.int, ws:seq.word, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
  let discard = setfld(getaddress(a, i + 1), valueofencoding(ws_getb.d))
  wordthread(a, ws, getlink.d)

function offsetthread(a:seq.int, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
  let discard = setfld(getaddress(a, i + 1), toT.getaddress(a, 1 + getb.d))
  offsetthread(a, getlink.d)

function wordseqthread(a:seq.int, ws:seq.word, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
  let discard = setfld(getaddress(a, i + 1), 0)
  let len = a_(i + 1)
  let discard2 = @(+, fixword(a, ws), 0, arithseq(len, 1, i + 2))
  wordseqthread(a, ws, d)

function fixword(a:seq.int, ws:seq.word, i:int)int 
 let discard = setfld(getaddress(a, i + 1), valueofencoding(ws_(a_i)))
  0

_______________




