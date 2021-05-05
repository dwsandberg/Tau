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

use seq.myinternaltype

use seq.mytype

use seq.symbol

use process.seq.int

use seq.seq.int

Builtin bitcast(int)seq.int

Builtin GEP(seq.int, int)int

Function interpretCompileTime(alltypes:typedict, code:seq.symbol)seq.symbol
let r = interpret(alltypes, removeconstant.code, 1, empty:stack.int)
 tocode(r, resulttype.last.code)

function tocode(r:int, typ:mytype)seq.symbol
 if typ = typeword then [ Word.wordencodingtoword.r]
 else if typ=typeint /or typ=typebits /or typ=typeref(moduleref."UTF8","char")  then [ Lit.r]
 else if  typ =  typeboolean then [ if r = 1 then Littrue else Litfalse]
 else if typ = seqof.typeword  then [ Words.aswords.bitcast.r]
 else if typ =  typereal then [ Reallit.r]
 else
  assert isseq.typ  report"resulttype not handled" + print.typ
  let s = bitcast.r
   for acc = [ Lit.0, Lit.length.s], @e = s do acc + tocode(@e, parameter.typ)/for(acc)

function aswords(s:seq.int)seq.word for acc ="", @e = s do acc + wordencodingtoword.@e /for(acc)

Function interpret(alltypes:typedict, code:seq.symbol)seq.word aswords.bitcast.interpret(alltypes, code, 1, empty:stack.int)

let p = process.interpret(alltypes, code, 1, empty:stack.int)if aborted.p then message.p else aswords.bitcast.result.p

function interpret(alltypes:typedict, code:seq.symbol, i:int, stk:stack.int)int
 if i > length.code then top.stk
 else
  let sym = code_i
  let nopara = nopara.sym
   if isword.sym  then
    interpret(alltypes, code, i + 1, push(stk, hash.first.fsig.sym))
   else if  iswordseq.sym  then
   let a = for acc = empty:seq.int, @e = fsig.sym do acc + hash.@e /for(acc)
    interpret(alltypes, code, i + 1, push(stk, GEP(a, 0)))
   else if module.sym = "$int" ∨ module.sym = "$real" ∨ module.sym = "$boolean"then
    interpret(alltypes, code, i + 1, push(stk, toint.(fsig.sym)_1))
   else if last.module.sym = "$sequence"_1 then
    interpret(alltypes, code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara), 0)))
   else if module.sym = "$record"then
    if subseq(top(stk, nopara), 1, 2) = [ 0, nopara - 2]then
     interpret(alltypes, code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara - 2), 0)))
    else interpret(alltypes, code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara), 2)))
   else if fsig.sym = "makereal(word seq)"then
    interpret(alltypes, code, i + 1, push(pop(stk, nopara), representation.makereal.aswords.bitcast.top.stk))
   else
    let t = dlsymbol.mangle(fsig.sym, module.sym)
    let dcret = deepcopysym(alltypes, resulttype.sym)
    let adcret = dlsymbol.mangle(fsig.dcret, module.dcret)
     assert adcret > 0 report"Not handle by interperter" + print.sym + "can not find" + print.dcret
      assert t > 0 report"Not handle by interperter" + print.sym + "mangle:"
      + mangle(fsig.sym, module.sym)
      let dc = deepcopysym(alltypes, seqof.typeword  )
      let adc = dlsymbol.mangle(fsig.dc, module.dc)
       assert adc > 0 report"?"
       let p = createthread(adcret, adc, t, packed.top(stk, nopara), buildargcode(alltypes, sym))
        assert not.aborted.p report message.p
         interpret(alltypes, code, i + 1, push(pop(stk, nopara), result.p))