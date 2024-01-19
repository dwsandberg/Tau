Module compileTimeT.T

use bitcast.seq.char

use bitcast.int

use seq.int

use bitcast.seq.int

use stack.int

use seq.mytype

use real

use standard

use symbol

use seq.symbol

use symbol2

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
let tmp =
 if not.isInternal.ctsym then empty:seq.symbol
 else
  let name = name.ctsym,
  if name ∈ "*" ∧ resulttype.ctsym = typeint then [Lit(value.1^args * value.2^args)]
  else if name ∈ "+" ∧ resulttype.ctsym = typeint then [Lit(value.1^args + value.2^args)]
  else if name ∈ "-" ∧ resulttype.ctsym = typeint then [Lit(value.2^args - value.1^args)]
  else if name ∈ "getseqlength" then
   if iswords.1^args then [Lit.n.worddata.1^args]
   else
    let x = 1^fullconstantcode.1^args,
    if isSequence.x then [Lit.nopara.x] else empty:seq.symbol
  else if name ∈ "getseqtype" then
   if iswords.1^args then [Lit.0]
   else
    let x = 1^fullconstantcode.1^args,
    if isSequence.x then [Lit.0] else empty:seq.symbol
  else empty:seq.symbol,
if not.isempty.tmp then tmp
else
 let stk = if nopara.ctsym = 0 then empty:seq.int else buildargs:T(args),
 if nopara.ctsym ≠ n.stk then empty:seq.symbol
 else if name.ctsym ∈ "idxNB" then
  let ptypes = paratypes.ctsym,
  if isseq.1#ptypes ∧ parameter.1#ptypes ∈ [typeint, typeword, typechar] then
   let s = bitcast:seq.int(1#stk)
   let idx = if 2#ptypes = typeint then 2#stk else 0,
   if between(idx, 1, n.s) then tocode:T(idx#s, parameter.1#ptypes, typedict)
   else empty:seq.symbol
  else empty:seq.symbol
 else if name.ctsym ∈ "#" then
  let ptypes = paratypes.ctsym,
  if isseq.2#ptypes ∧ parameter.2#ptypes ∈ [typeint, typeword, typechar] then
   let s = bitcast:seq.int(2#stk)
   let idx = if 1#ptypes = typeint then 1#stk else 0,
   if between(idx, 1, n.s) then tocode:T(idx#s, resulttype.ctsym, typedict)
   else empty:seq.symbol
  else empty:seq.symbol
 else if module.ctsym = moduleref."* word" ∧ name.ctsym ∈ "merge encodeword decodeword" then
  if name.ctsym ∈ "merge" then [Word.merge.bitcast:seq.word(1#stk)]
  else if name.ctsym ∈ "encodeword" then [Word.encodeword.bitcast:seq.char(1#stk)]
  else
   {999 decodeword}
   let charseq = decodeword.bitcast:word(1#stk),
   tocode:T(bitcast:int(toptr.charseq), resulttype.ctsym, typedict)
 else if name.ctsym ∈ "makereal" ∧ paratypes.ctsym = [seqof.typeword] then [Reallit.representation.makereal.bitcast:seq.word(1#stk)]
 else if module.ctsym = moduleref."* UTF8" ∧ name.ctsym ∈ "toword" then [Word.toword.1#stk]
 else
  let ctsym2 = changelibrary(ctsym, librarymap)
  let t = callfunc:T(ctsym2, typedict, stk),
  if isempty.t then empty:seq.symbol else tocode:T(1#t, resulttype.ctsym2, typedict)

function tocode:T(r:int, typ:mytype, typedict:typedict) seq.symbol
if typ = typeword then [Word.wordencodingtoword.r]
else if typ = typeint ∨ typ = typebits ∨ typ = typechar then [Lit.r]
else if typ = typeboolean then [if r = 1 then Littrue else Litfalse]
else if typ = seqof.typeword then
 for acc = "", @e ∈ bitcast:seq.int(r)
 do acc + wordencodingtoword.@e,
 [Words.acc]
else if typ = typereal then [Reallit.r]
else
 assert isseq.typ report "resulttype not handled^(typ)"
 let s = bitcast:seq.int(r),
 for acc = empty:seq.symbol, @e ∈ s
 do acc + tocode:T(@e, parameter.typ, typedict),
 acc + Sequence(parameter.typ, n.s)

function buildargs:T(codein:seq.symbol) seq.int
if for ok = true, sym ∈ subseq(codein, 1, 20)
do isconst.sym ∨ isSequence.sym ∨ isRecord.sym,
not.ok then empty:seq.int
else
 for ok = true, stk = empty:stack.int, sym ∈ codein
 while ok
 do
  if iswordseq.sym then
   let a =
    for acc = empty:seq.int, @e ∈ worddata.sym
    do acc + hash.@e,
    acc,
   next(ok, push(stk, bitcast:int(toptr.a)))
  else if isword.sym then next(ok, push(stk, hash.wordname.sym))
  else if isIntLit.sym ∨ isRealLit.sym then next(ok, push(stk, value.sym))
  else if sym = Littrue then next(ok, push(stk, 1))
  else if sym = Litfalse then next(ok, push(stk, 0))
  else if isrecordconstant.sym then
   let t = buildargs:T(fullconstantcode.sym),
   next(not.isempty.t, if isempty.t then push(stk, 0) else push(stk, 1#t))
  else if isSequence.sym then
   let nopara = nopara.sym,
   if n.toseq.stk < nopara.sym then next(false, stk)
   else next(ok, push(pop(stk, nopara), bitcast:int(toptr.packed.top(stk, nopara))))
  else next(false, stk),
 if ok then toseq.stk else empty:seq.int
 