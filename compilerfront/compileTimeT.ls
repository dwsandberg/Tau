Module compileTimeT.T

use bitcast.seq.char

use bitcast.int

use seq.int

use bitcast.seq.int

use stack.int

use seq1.mytype

use seq.mytype

use bitcast.packed3

use seq.packed3

use bitcast.seq.packed3

use ptr

use bitcast.ptr

use real

use standard

use seq.symbol

use symbol1

use tausupport

use typedict

use word

use bitcast.word

use bitcast.seq.word

unbound callfunc:T(ctsym:symbol, typedict:typedict, stk:seq.int) seq.int

Function interpretCompileTime:T(
librarymap:seq.word
, args:seq.symbol
, ctsym:symbol
, typedict:typedict
) seq.symbol
let stk = if nopara.ctsym = 0 then empty:seq.int else buildargs:T(args),
if nopara.ctsym ≠ n.stk then empty:seq.symbol
else if name.ctsym ∈ "sub" then
 let ptypes = paratypes.ctsym,
 if isseq.ptypes sub 1 ∧ %.parameter.ptypes sub 1 ∈ ["int", "word", "char"] then
  let s = bitcast:seq.int(stk sub 1)
  let idx = if ptypes sub 2 = typeint then stk sub 2 else 0,
  if between(idx, 1, n.s) then tocode:T(s sub idx, resulttype.ctsym, typedict)
  else empty:seq.symbol
 else empty:seq.symbol
else if module.ctsym = moduleref."* word" ∧ name.ctsym ∈ "merge encodeword decodeword" then
 if name.ctsym ∈ "merge" then [Word.merge.bitcast:seq.word(stk sub 1)]
 else if name.ctsym ∈ "encodeword" then [Word.encodeword.bitcast:seq.char(stk sub 1)]
 else
  {999 decodeword}
  let charseq = decodeword.bitcast:word(stk sub 1),
  tocode:T(bitcast:int(toptr.charseq), resulttype.ctsym, typedict)
else if module.ctsym = moduleref."* UTF8" ∧ name.ctsym ∈ "toword" then [Word.toword.stk sub 1]
else
 let ctsym2 = changelibrary(ctsym, librarymap)
 let t = callfunc:T(ctsym2, typedict, stk),
 if isempty.t then empty:seq.symbol
 else tocode:T(t sub 1, resulttype.ctsym2, typedict)

function tocode:T(r:int, typ:mytype, typedict:typedict) seq.symbol
if typ = typeword then [Word.wordencodingtoword.r]
else if typ = typeint ∨ typ = typebits then [Lit.r]
else if typ = typeboolean then [if r = 1 then Littrue else Litfalse]
else if typ = seqof.typeword then
 for acc = "", @e ∈ bitcast:seq.int(r)
 do acc + wordencodingtoword.@e,
 [Words.acc]
else if typ = typereal then [Reallit.r]
else if %.typ = "char" then [Lit.r]
else if isseq.typ then
 let s = bitcast:seq.int(r)
 let seqtype = getseqtype.s
 let pb = parameter.basetype(typ, typedict)
 let maybepacked = pb ∈ [typebyte, typepacked2, typepacked3, typepacked4, typepacked5, typepacked6],
 let cc1 = not.maybepacked ∨ seqtype = 0,
 if not.maybepacked ∨ seqtype = 0 then
  for acc = empty:seq.symbol, e ∈ s
  do acc + tocode:T(e, parameter.typ, typedict),
  acc + Sequence(parameter.typ, n.s)
 else if seqtype ≠ 1 then empty:seq.symbol
 else
  assert pb = typepacked3 report "???? tocode in compiletime NOT handled"
  let s3 = bitcast:seq.packed3(r),
  for acc = empty:seq.symbol, e ∈ s3
  do acc + tocode:T(bitcast:int(toptr.e), parameter.typ, typedict),
  acc + Sequence(parameter.typ, n.s3)
else
 let types = flatflds(typedict, typ),
 if n.types = 1 then tocode:T(r, types sub 1, typedict)
 else
  let p = bitcast:ptr(r)
  for acc = empty:seq.symbol, idx = 0, e ∈ types
  do next(acc + tocode:T(fld:int(p, idx), e, typedict), idx + 1),
  acc + Record.types

function buildargs:T(codein:seq.symbol) seq.int
if for ok = true, sym ∈ subseq(codein, 1, 20)
do
 let kind = kind.sym,
 isconst.kind ∨ kind ∈ [krecord, ksequence],
not.ok then empty:seq.int
else
 for ok = true, stk = empty:stack.int, sym ∈ codein
 while ok
 do
  let kind = kind.sym,
  if kind = kwords then
   let a =
    for acc = empty:seq.int, @e ∈ worddata.sym
    do acc + hash.@e,
    acc,
   next(ok, push(stk, bitcast:int(toptr.a)))
  else if kind = kword then next(ok, push(stk, hash.wordname.sym))
  else if kind = kint ∨ kind = kreal then next(ok, push(stk, value.sym))
  else if kind = ktrue then next(ok, push(stk, 1))
  else if kind = kfalse then next(ok, push(stk, 0))
  else if kind = kconstantrecord then
   let t = buildargs:T(fullconstantcode.sym),
   next(not.isempty.t, if isempty.t then push(stk, 0) else push(stk, t sub 1))
  else if kind = ksequence then
   let nopara = nopara.sym,
   if n.toseq.stk < nopara.sym then next(false, stk)
   else next(ok, push(pop(stk, nopara), bitcast:int(toptr.packed.top(stk, nopara))))
  else if kind = krecord then
   let nopara = nopara.sym,
   if n.toseq.stk < nopara.sym then next(false, stk)
   else
    {set is used below just to skip the first two fields of the sequence and treat the rest as a record}
    let p2 = set(set(toptr.packed.top(stk, nopara), 0), 0),
    next(ok, push(pop(stk, nopara), bitcast:int(p2)))
  else next(false, stk),
 if ok then toseq.stk else empty:seq.int
 
