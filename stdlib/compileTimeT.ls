module compileTimeT.T

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

use symbolconstant

use bitcast:seq.char

use bitcast:word

use bitcast:seq.word

use bitcast:int

use real

Function interpretCompileTime:T(args:seq.symbol,ctsym:symbol, typedict:typedict)seq.symbol
let stk=  buildargs2(args )
if  isempty.stk /and nopara.ctsym /ne length.stk  then empty:seq.symbol
else if name.ctsym /in "_" then
  let ptypes=paratypes.ctsym
  {assert false report "here"+print.ctsym+print.ptypes_1}
   if  isseq.ptypes_1 /and ptypes_2=typeint /and parameter.ptypes_1 /in [typeint,typeword,typechar] then
     let s=bitcast:seq.int(toptr.stk_1)
     if  between(stk_2,1,length.s) then
        tocode:T(s_(stk_2), resulttype.ctsym, typedict)
     else empty:seq.symbol
   else empty:seq.symbol
else if module.ctsym=moduleref("words") /and name.ctsym /in "merge encodeword decodeword" then 
if name.ctsym /in "merge" then
      [Word.merge(bitcast:seq.word(first.stk))]
else if name.ctsym /in "encodeword" then
      [Word.encodeword(bitcast:seq.char(first.stk))]
else {decodeword}  
     let charseq=decodeword.bitcast:word(first.stk)
      tocode:T(bitcast:int(toptr.charseq), resulttype.ctsym, typedict)
else  if name.ctsym /in "makereal" /and paratypes.ctsym=[seqof.typeword] then
      [Reallit.representation.makereal(bitcast:seq.word(first.stk))]
else  if module.ctsym=moduleref("UTF8") /and name.ctsym /in "toword" then
          [Word.toword.first.stk ]
else 
let t = funcaddress:T(ctsym)
if t = 0 then empty:seq.symbol
else
 let adcret = funcaddress:T(deepcopySym.resulttype.ctsym)
 let adc = funcaddress:T(deepcopySym.seqof.typeword)
 let p = createthread(adcret, adc, t, stk, buildargcode:T(ctsym, typedict))
 assert not.aborted.p report message.p
 tocode:T(result.p, resulttype.ctsym, typedict)

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
 for acc = empty:seq.symbol, @e ∈ s do acc + tocode:T(@e, parameter.typ, typedict)/for(acc
 +Sequence(parameter.typ,length.s) )