Module reconstruct

use bits

use stdlib

use unsafe.int

Three Functions to pack two ints into 64 bits

function halfsize int // 2^31 // 2147483648

Function getlink(a:int)int toint(bits.a >> 31) - halfsize

Function packit(link:int, b:int)int toint(bits(halfsize + link)<< 31 ∨ bits.b)

Function getb(a:int)int toint(bits.a ∧ bits(halfsize - 1))

Function relocateoffset(d2:seq.int)seq.int 
 let discard2 = offsetthread(d2, d2_2)
   setfld(setfld(d2,2,d2_1),3,0)
 
function offsetthread(a:seq.int, i:int)int 
 if i = 0 
  then 0 
  else let d = a_i 
    let discard= setfld(a,i+1,cast(a, 1 + getb.d,1))  
  offsetthread(a, getlink.d)

