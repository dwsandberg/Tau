module interpreter

use UTF8

use real

use standard

use symbol

use typedict

use words

use process.int

use seq.int

use stack.int

use seq.mytype

use seq.symbol

use process.seq.int

use seq.seq.int

use libraryModule

use seq.liblib

use symref

use otherseq.symbol

Builtin bitcast(int)seq.int

Builtin GEP(seq.int, int)int

Builtin createthreadI(int, int, int, seq.int, int)process.int

Export  deepcopySym(mytype) symbol

Function interpretCompileTime(code:seq.symbol)seq.symbol
let z = code
assert for acc = true, sym ∈ z while acc do not.isFref.sym /for(acc)
report"has Fref" + print.z
let r = interpret( z >> 1, 1, empty:stack.int)
 callsymbol(last.code,r)
  

function tocode(r:int, typ:mytype)seq.symbol
if typ = typeword then [ Word.wordencodingtoword.r]
else if typ = typeint ∨ typ = typebits ∨ typ = typechar then [ Lit.r]
else if typ = typeboolean then [ if r = 1 then Littrue else Litfalse]
else if typ = seqof.typeword then [ Words.aswords.bitcast.r]
else if typ = typereal then [ Reallit.r]
else
 assert isseq.typ report"resulttype not handled" + print.typ
 let s = bitcast.r
 for acc = [ Lit.0, Lit.length.s], @e ∈ s do acc + tocode(@e, parameter.typ)/for(acc)

function aswords(s:seq.int)seq.word
for acc = "", @e ∈ s do acc + wordencodingtoword.@e /for(acc)

 
Function buildargcodeI(sym:symbol)int
{ needed because the call interface implementation for reals is different than other types is some implementations }
for acc = 1, typ ∈ paratypes.sym + resulttype.sym do
 acc * 2 + if { getbasetype(alltypes, typ)} typ = typereal then 1 else 0
/for(acc)

function interpret(code:seq.symbol, i:int, stk:stack.int)stack.int
if i > length.code then  stk
else
 let sym = code_i
 let nopara = nopara.sym
 if isword.sym then interpret(code, i + 1, push(stk, hash.wordname.sym))
 else if iswordseq.sym then
  let a = for acc = empty:seq.int, @e ∈ worddata.sym do acc + hash.@e /for(acc)
  interpret(code, i + 1, push(stk, GEP(a, 0)))
 else if isIntLit.sym ∨ isRealLit.sym then interpret(code, i + 1, push(stk, value.sym))
 else if sym = Littrue then interpret(code, i + 1, push(stk, 1))
 else if sym = Litfalse then interpret(code, i + 1, push(stk, 0))
 else if isSequence.sym then interpret(code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara), 0)))
 else if isRecord.sym then
  if subseq(top(stk, nopara), 1, 2) = [ 0, nopara - 2]then
   interpret(code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara - 2), 0)))
  else interpret(code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara), 2)))
 else assert wordname.sym = "makereal"_1 ∧ name.module.sym ∈ "UTF8"
  report "interpret not expecting"+print.sym
  interpret(code, i + 1, push(pop(stk, nopara), representation.makereal.aswords.bitcast.top.stk))

function callsymbol(sym:symbol,stk:stack.int) seq.symbol
  let t = funcaddress.sym
  if t=0 then empty:seq.symbol
  else 
  let nopara=nopara.sym
  assert print.resulttype.sym ≠ "?"report"INTER" + print.sym  
  let dcret = deepcopySym.resulttype.sym
  let adcret = funcaddress.dcret
  assert adcret > 0 report"Not handle by interperter" + print.sym + "can not find" + print.dcret
  assert t > 0 report"Not handle by interperter" + print.sym
  let dc = deepcopySym.seqof.typeword
  let adc = funcaddress.dc
  assert adc > 0 report"interpreter ?"+print.dc+"sym:"+print.sym
  let p = createthreadI(adcret, adc, t, packed.top(stk, nopara), buildargcodeI.sym)
  assert not.aborted.p report message.p
  tocode(result.p,resulttype.sym)
  
  Function funcaddress(sym:symbol)int
     let addrs=symboladdress.first.loadedLibs
   let i= findindex(sym,subseq(symbolrefdecode.libinfo.first.loadedLibs,1,length.addrs))
   if i /le length.addrs then addrs_i  else 0  

Builtin createthreadI(int, int, int, seq.UTF8, int)process.int

Function callentrypoint(arg:UTF8) seq.word
let t=entrypointaddress.last.loadedLibs
let typeUTF8=typeref("UTF8 UTF8")
let dcret = deepcopySym.typeUTF8
  let adcret = funcaddress.dcret
    let dc = deepcopySym.seqof.typeword
  let adc = funcaddress.dc
   if not( t > 0  /and adcret > 0 /and adc > 0) then
    "ERROR"+[toword.t,toword.adcret,toword.adc]
  else
    let p = createthreadI(adcret, adc, t, [arg], {buildargcodeI.sym} 4)
    if aborted.p then message.p
   else "OK"
