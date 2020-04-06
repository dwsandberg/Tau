Module packedseq.T

use seq.T

use unsafe.T

use stdlib

x is included in packedseq so the procedure to access the type with be different between instances of the scope.

Function type:packedseq.T internaltype export

type packedseq is sequence length:int, x:seq.T

Function length(packedseq.T)int export

Function_(a:packedseq.T, i:int)T
 let ds = sizeoftype:T
  cast(toseq.a, 2 + ds * (i - 1), ds)

Function packed(s:seq.T)seq.T
 let ds = sizeoftype:T
 let typ = if ds = 1 then 0 else getseqtype.toseq.packedseq(length.s, empty:seq.T)
 let b = setfld(allocatespace:seq.T(ds * length.s + 2), 0, inttoT:T(typ))
  if ds = 1 then @(append, identity, setfld(b, 1, inttoT:T(0)), s)
  else
   let g = @(append(ds), identity, setfld(b, 1, inttoT:T(0)), s)
    setfld(g, 1, inttoT:T(length.s))

Module unsafe.T

use seq.T

use stdlib

Function cast(s:seq.T, offset:int, typ:int)T builtin.usemangle

Function allocatespace:seq.T(i:int)seq.T builtin."PARAM 1 allocatespaceZbuiltinZint"


function setfld2(s:seq.T, i:int, val:T)seq.T builtin.STATE.usemangle

Function setfld(s:seq.T, i:int, val:T)seq.T   setfld2(s,i,val)
 
 
Function append(s:seq.T, val:T)seq.T
 let len = length.s + 1
  setfld(setfld(s, 1, inttoT:T(len)), len + 1, val)

Function append(ds:int, s:seq.T, val:T)seq.T @(append, fldof(val), s, arithseq(ds, 1, 0))

Function relocate(a:seq.T, idx:int, relloc:int)seq.T setfld(a, idx, cast(a, relloc, 1))

Function inttoT:T(int)T builtin."PARAM 1"

Function fldof(T, offset:int)T builtin."PARAM 1 PARAM 2 IDXUC"