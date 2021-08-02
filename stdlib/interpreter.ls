module interpreter

use UTF8

use fileio

use mangle

use pass1

use real

use standard

use symbol

use tausupport

use words

use process.int

use seq.int

use stack.int


use seq.mytype

use seq.symbol

use process.seq.int

use seq.seq.int

use program

Builtin bitcast(int)seq.int

Builtin GEP(seq.int, int)int

Function interpretCompileTime(code:seq.symbol)seq.symbol
let z=removeconstant.code
assert for acc=true ,sym=z while acc do not.isFref.sym /for(acc) report
   "has Fref"+print.z
let r = interpret(z, 1, empty:stack.int)
 tocode(r, resulttype.last.code)

function tocode(r:int, typ:mytype)seq.symbol
 if typ = typeword then [ Word.wordencodingtoword.r]
 else if typ = typeint ∨ typ = typebits ∨ typ = typeref."char UTF8."then
  [ Lit.r]
 else if typ = typeboolean then [ if r = 1 then Littrue else Litfalse]
 else if typ = seqof.typeword then [ Words.aswords.bitcast.r]
 else if typ = typereal then [ Reallit.r]
 else
  assert isseq.typ report"resulttype not handled" + print.typ
  let s = bitcast.r
   for acc = [ Lit.0, Lit.length.s], @e = s do acc + tocode(@e, parameter.typ)/for(acc)

function aswords(s:seq.int)seq.word for acc ="", @e = s do acc + wordencodingtoword.@e /for(acc)

Function interpret(alltypes:type2dict, code:seq.symbol)seq.word aswords.bitcast.interpret(code, 1, empty:stack.int)

let p = process.interpret(code, 1, empty:stack.int)if aborted.p then message.p else aswords.bitcast.result.p

function interpret(code:seq.symbol, i:int, stk:stack.int)int
 if i > length.code then top.stk
 else
  let sym = code_i
  let nopara = nopara.sym
   if isword.sym then interpret(code, i + 1, push(stk, hash.wordname.sym))
   else if iswordseq.sym then
   let a = for acc = empty:seq.int, @e = worddata.sym do acc + hash.@e /for(acc)
   interpret(code, i + 1, push(stk, GEP(a, 0)))
   else if inmodule(sym,"$int") ∨ inmodule(sym,"$real")then
    interpret(code, i + 1, push(stk, value.sym))
   else if sym = Littrue then interpret(code, i + 1, push(stk, 1))
   else if sym = Litfalse then interpret(code, i + 1, push(stk, 0))
   else if inmodule(sym,"$sequence")then
    interpret(code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara), 0)))
   else if inmodule(sym,"$record")then
    if subseq(top(stk, nopara), 1, 2) = [ 0, nopara - 2]then
     interpret(code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara - 2), 0)))
    else interpret(code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara), 2)))
   else if wordname.sym = "makereal"_1 ∧ inmodule(sym,"UTF8")then
    interpret(code, i + 1, push(pop(stk, nopara), representation.makereal.aswords.bitcast.top.stk))
   else {if isFref.sym then
interpret(code, i + 1, push(stk,dlsymbol.mangledname.basesym.sym ))
   else}
    let t = dlsymbol.mangledname.sym
     assert print.resulttype.sym ≠ "?"report"INTER" + print.sym + print.code
    let dcret = deepcopysymI.resulttype.sym
    let adcret = dlsymbol.mangledname.dcret
     assert adcret > 0 report"Not handle by interperter" + print.sym + "can not find" + print.dcret
      assert t > 0 report"Not handle by interperter" + print.sym + "mangle:" + mangledname.sym
      let dc = deepcopysymI.seqof.typeword
      let adc = dlsymbol.mangledname.dc
       assert adc > 0 report"?"
       let p = createthread(adcret, adc, t, packed.top(stk, nopara), buildargcodeI.sym)
       assert not.aborted.p report message.p
         interpret(code, i + 1, push(pop(stk, nopara), result.p)) 