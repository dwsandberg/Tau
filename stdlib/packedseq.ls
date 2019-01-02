Module packedseq.T

use seq.T

use stdlib

setfld set value at a to x and return next address

Function setfld(a:address.T, x:T)address.T builtin.STATE.usemangle


function allocatespace(i:int)seq.T builtin." PARAM 1 allocatespaceZbuiltinZint"

type address is record toseq:seq.T

Function getaddress(s:seq.T, i:int)address.T 
 builtin."PARAM 1 PARAM 2 getaddressZbuiltinZTzseqZint"

Function toT(a:address.T)T builtin." PARAM 1 "

function inttoT(int)T builtin." PARAM 1 "

function fldof(T, offset:int)T builtin.IDXUC

function getfld(packedseq.T, i:int)int builtin.IDXUC

x is included in packedseq so the procedure to access the type with be different between instances of the scope.

type packedseq is sequence length:int, x:seq.T

Function length(packedseq.T)int export

Function_(a:packedseq.T, i:int)T 
 let ds = sizeoftype:T 
  toT.getaddress(toseq.a, 2 + ds *(i - 1))


Function packed(s:seq.T)seq.T 
 let ds = sizeoftype:T 
  let typ = if ds = 1 then 0 else getfld(packedseq(length.s, empty:seq.T), 0)
  let b = allocatespace(ds * length.s + 2)
  let address1stelement = setfld(setfld(getaddress(b, 0), inttoT.typ), inttoT.length.s)
  let d = if ds = 1 
   then let g = @(setfld, identity, address1stelement, s)
    0 
   else @(+, setelement(ds, s, b), 0, arithseq(length.s, 1, 1))
  b

function setelement(ds:int, s:seq.T, a:seq.T, i:int)int 
 let d = @(setfld, fldof(s_i), getaddress(a, 2 + ds *(i - 1)), arithseq(ds, 1, 0))
  0

