Module reconstruct

use packedseq.int

use bits




use stdlib


Three Functions to pack two ints into 64 bits

function halfsize int // 2^31 // 2147483648

Function getlink(a:int)int toint(bits.a >> 31) - halfsize

Function packit(link:int, b:int)int toint(bits(halfsize + link)<< 31 ∨ bits.b)

Function getb(a:int)int toint(bits.a ∧ bits(halfsize - 1))

type xxx is record a:address.int, t:int 

Function print(a:address.int) seq.word    
// added so typedesc of address.int is processed correctly  by declaring in type xxx  //
let x=xxx(a,100) "HELLO"

Function relocate(ws:seq.word, d2:seq.int)address.int 
 // d2 format is [ wordthread start, offsetthread start, unused]+ actual data]// 
  // initwordset is called before relocate // 
  // new version // 
  let discard = wordthread(d2, ws, d2_1)
  let discard2 = offsetthread(d2, d2_2)
  let discard3 = wordseqthread(d2, ws, d2_3)
  setfld(setfld(setfld(getaddress(d2, 2), 0), 0), 0)

function wordthread(a:seq.int, ws:seq.word, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
  let discard = setfld(getaddress(a, i + 1), encoding(ws_getb.d))
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
 let discard = setfld(getaddress(a, i + 1), encoding(ws_(a_i)))
  0

_______________

The linklists2 type contains a seq of integers that represents the memory.Any memory locations that store the type word are linked into a linked list begining with wordthread. Two values are packed into the integer is store in the seq. One is the word3 encoding and the other the next value in the linked list. Any memory locations that store an address of another memory are linked into a linked list beginning with offsetthread. In this case the element in the seq is represents two interger values. One is the next value in the linked list and the other is the index of the refrenced memory location.

type linklists2 is record a:seq.int, wordthread:int, offsetthread:int, wordseqthread:int

Function createlinkedlists linklists2 linklists2(empty:seq.int, 0, 0, 0)

Function a(linklists2)seq.int export

Function wordthread(linklists2)int export

Function offsetthread(linklists2)int export

Function wordseqthread(linklists2)int export

Function linklists2(a:seq.int, wordthread:int, offsetthread:int, wordseqthread:int) linklists2 export