Module reconstruct

use stdlib

Decode Functions

Function relocate(ws:seq.word, d2:seq.int)int 
 // d2 format is [ wordthread start, offsetthread start, unused]+ actual data]// 
  // initwordset is called before relocate // 
  // new version // 
  let discard = wordthread(d2, ws, d2_1)
  let discard2 = offsetthread(d2, d2_2)
  let discard3 = setfld5(d2, 0, 2)
  let discard4 = setfld5(d2, 0, 3)
  cast2int.d2 + 16 + 3 * 8

function wordthread(a:seq.int, ws:seq.word, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
  let discard = setfld5(a, ws_getb.d, i + 1)
  wordthread(a, ws, getlink.d)

function offsetthread(a:seq.int, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
  let discard = setfld5(a, cast2int.a + getb.d * 8 + 8, i + 1)
  offsetthread(a, getlink.d)

function cast2int(seq.int)int builtin

function setfld5(a:seq.int, x:word, i:int)int builtin.SETFLD3

function setfld5(a:seq.int, x:int, i:int)int builtin.SETFLD3

function setfld5(a:int, x:int, i:int)int builtin.SETFLD3

Function IDXUC(int, int)int builtin.IDXUC

Function cast2wordseq(int)seq.word builtin

Function cast2int(s:seq.word)int builtin

_______________________________

Three Functions to pack two ints into 64 bits

function halfsize int // 2^31 // 2147483648

Function packit(link:int, b:int)int {(halfsize + link)* halfsize + b }

Function getb(a:int)int a mod halfsize

Function getlink(a:int)int a / halfsize - halfsize

