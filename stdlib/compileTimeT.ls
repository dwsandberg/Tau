module compileTimeT.T

use real

use standard

use symbol

use symbolconstant

use typedict

use words

use process.int

use seq.int

use stack.int

use bitcast:int

use seq.mytype

use otherseq.symbol

use seq.symbol

use bitcast:word

use bitcast:seq.char

use seq.seq.int

use bitcast:seq.int

use bitcast:seq.word

unbound callfunc:T(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int

Function interpretCompileTime:T(args:seq.symbol, ctsym:symbol, typedict:typedict)seq.symbol
let stk = if nopara.ctsym = 0 then empty:seq.int else buildargs:T(args)
if nopara.ctsym > 0 ∧ isempty.stk then empty:seq.symbol
else if name.ctsym ∈ "_"then
 let ptypes = paratypes.ctsym
 if isseq.ptypes_1 ∧ parameter.ptypes_1 ∈ [typeint, typeword, typechar]then
  let s = bitcast:seq.int(stk_1)
  let idx = 
   if ptypes_2 = typeint then stk_2
   else if ptypes_2 = typeref."index standard"then stk_2 + 1 else 0
  if between(idx, 1, length.s)then tocode:T(s_idx, resulttype.ctsym, typedict)
  else empty:seq.symbol
 else empty:seq.symbol
else if module.ctsym = moduleref."words" ∧ name.ctsym ∈ "merge encodeword decodeword"then
 if name.ctsym ∈ "merge"then[Word.merge.bitcast:seq.word(first.stk)]
 else if name.ctsym ∈ "encodeword"then[Word.encodeword.bitcast:seq.char(first.stk)]
 else
  {decodeword}
  let charseq = decodeword.bitcast:word(first.stk)
  tocode:T(bitcast:int(toptr.charseq), resulttype.ctsym, typedict)
else if name.ctsym ∈ "makereal" ∧ paratypes.ctsym = [seqof.typeword]then
 [Reallit.representation.makereal.bitcast:seq.word(first.stk)]
else if module.ctsym = moduleref."UTF8" ∧ name.ctsym ∈ "toword"then
 [Word.toword.first.stk]
else
 let t = callfunc:T(ctsym, typedict, stk)
 if isempty.t then empty:seq.symbol else tocode:T(first.t, resulttype.ctsym, typedict)

function tocode:T(r:int, typ:mytype, typedict:typedict)seq.symbol
if typ = typeword then[Word.wordencodingtoword.r]
else if typ = typeint ∨ typ = typebits ∨ typ = typechar then[Lit.r]
else if typ = typeboolean then[if r = 1 then Littrue else Litfalse]
else if typ = seqof.typeword then
 for acc = "", @e ∈ bitcast:seq.int(toptr.r)do acc + wordencodingtoword.@e /for([Words.acc])
else if typ = typereal then[Reallit.r]
else
 assert isseq.typ report"resulttype not handled" + print.typ
 let s = bitcast:seq.int(toptr.r)
 for acc = empty:seq.symbol, @e ∈ s do acc + tocode:T(@e, parameter.typ, typedict)/for(acc + Sequence(parameter.typ, length.s))

Function buildargs:T(codein:seq.symbol)seq.int
if not.for ok = true, sym ∈ subseq(codein, 1, 20)do isconst.sym ∨ isSequence.sym ∨ isRecord.sym /for(ok)then
 empty:seq.int
else
 for ok = true, stk = empty:stack.int, sym ∈ codein
 while ok
 do if iswordseq.sym then
  let a = for acc = empty:seq.int, @e ∈ worddata.sym do acc + hash.@e /for(acc)
  next(ok, push(stk, bitcast:int(toptr.a)))
 else if isword.sym then next(ok, push(stk, hash.wordname.sym))
 else if isIntLit.sym ∨ isRealLit.sym then next(ok, push(stk, value.sym))
 else if sym = Littrue then next(ok, push(stk, 1))
 else if sym = Litfalse then next(ok, push(stk, 0))
 else if isrecordconstant.sym then
  let t = buildargs:T(fullconstantcode.sym)
  next(not.isempty.t, if isempty.t then push(stk, 0)else push(stk, first.t))
 else if isSequence.sym then
  let nopara = nopara.sym
  if length.toseq.stk < nopara.sym then next(false, stk)
  else next(ok, push(pop(stk, nopara), bitcast:int(toptr.packed.top(stk, nopara))))
 else
  {if isRecord.sym then let nopara=nopara.sym if length.toseq.stk < nopara.sym then next(false, stk)else next(ok, push 
(pop(stk, nopara), bitcast:int(set(set(toptr.packed.top(stk, nopara), 0), nopara))))else}
  next(false, stk)
 /for(if ok then toseq.stk else empty:seq.int /if) 