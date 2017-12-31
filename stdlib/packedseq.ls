Module packedseq(T)

use internals.T

use seq.T

use stdlib

x is included in packedseq so the procedure to access the type with be different between instances of the scope.

type packedseq is sequence length:int, x:seq.T

Function length(packedseq.T)int export

Function_(a:packedseq.T, i:int)T 
 let ds = sizeoftype:T 
  toT(address.toseq.a +(2 + ds *(i - 1)))

Function sizeoftype T builtin.TYPESIZE

Function packed(s:seq.T)seq.T 
 let ds = sizeoftype:T 
  let p = packedseq(length.s, empty:seq.T)
  let b = allocatespace(ds * length.s + 2)
  let c = setfld3(address.b, length.s, 1)
  let d = if ds = 1 
   then let e = setfld3(address.b, 0, 0)
    let g = @(setfldx, identity, address.b + 2, s)
    0 
   else let e = setfld3T(address.b, valueat(address.toseq.p, 0), 0)
   @(+, setelement(ds, s, b), 0, arithseq(length.s, 1, 1))
  b

function setfldx(a:address.T, value:T)address.T 
 let x = setfld4(a, value, 0)
  a + 1

Function setfld4(a:address.T, x:T, i:int)int builtin.SETFLD3



function setelement(ds:int, s:seq.T, a:seq.T, i:int)int 
 let d = @(setfldx, valueat.ggg(s_i), address.a +(2 + ds *(i - 1)), arithseq(ds, 1, 0))
  0

function ggg(T)address.T builtin

