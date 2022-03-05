module compileTime.T

use real

use standard

use symbol

use tausupport

use typedict

use words

use process.int

use seq.int

use stack.int

use bitcast:int

use seq.mytype

use otherseq.symbol

use seq.symbol

use seq.seq.int

use bitcast:seq.int

unbound funcaddress:T(sym:symbol)int

unbound buildargcode:T(sym:symbol, typedict:typedict)int

Function interpretCompileTime:T(code:seq.symbol, typedict:typedict)seq.symbol
let ctsym = last.code
let t = funcaddress:T(ctsym)
if t = 0 then empty:seq.symbol
else
 for stk = empty:stack.int, sym ∈ code >> 1 do
  let nopara = nopara.sym
  if isword.sym then push(stk, hash.wordname.sym)
  else if iswordseq.sym then
   let a = for acc = empty:seq.int, @e ∈ worddata.sym do acc + hash.@e /for(acc)
   push(stk, bitcast:int(toptr.a))
  else if isIntLit.sym ∨ isRealLit.sym then push(stk, value.sym)
  else if sym = Littrue then push(stk, 1)
  else if sym = Litfalse then push(stk, 0)
  else if isSequence.sym then push(pop(stk, nopara), bitcast:int(toptr.packed.top(stk, nopara)))
  else
   assert isRecord.sym report"interpret not expecting" + print.sym
   push(pop(stk, nopara), bitcast:int(set(set(toptr.packed.top(stk, nopara), 0), nopara)))
 /for(let adcret = funcaddress:T(deepcopySym.resulttype.ctsym)
 let adc = funcaddress:T(deepcopySym.seqof.typeword)
 let p = createthread(adcret, adc, t, top(stk, nopara.ctsym), buildargcode:T(ctsym, typedict))
 assert not.aborted.p report message.p
 tocode:T(result.p, resulttype.ctsym, typedict))

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
 for acc = [Lit.0, Lit.length.s], @e ∈ s do acc + tocode:T(@e, parameter.typ, typedict)/for(acc) 