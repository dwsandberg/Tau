module interpreter

use UTF8

use seq.encoding.seq.char

use encoding.seq.char

use fileio

use process.int

use process.seq.int

use seq.seq.int

use seq.int

use stack.int

use mangle

use seq.mytype

use pass1

use real

use stdlib

use seq.symbol

use symbol

use words

Builtin bitcast(seq.int)int

Builtin bitcast(int)seq.int

Builtin dlsymbol(seq.bits)int

Builtin createthread(int, int, int, seq.int)process.int

Function dlsymbol(name:word)int dlsymbol.toCformat.[ name]

function aswords(s:seq.int)seq.word s @@ +("", word.to:encoding.seq.char(@e))

Function interpret(alltypes:typedict, code:seq.symbol)seq.word interpret(alltypes, code, 1, empty:stack.int)

function interpret(alltypes:typedict, code:seq.symbol, i:int, stk:stack.int)seq.word
 if i > length.code then aswords.bitcast.top.stk
 else
  let sym = code_i
  let nopara = nopara.sym
   if module.sym = "$words"then
   let a = fsig.sym @@ +(empty:seq.int, hash.@e)
     interpret(alltypes, code, i + 1, push(stk, bitcast.a))
   else if module.sym = "$int"then
   interpret(alltypes, code, i + 1, push(stk, toint.(fsig.sym)_1))
   else if module.sym = "$record" ∧ subseq(top(stk, nopara), 1, 2) = [ 0, nopara - 2]then
   interpret(alltypes, code, i + 1, push(pop(stk, nopara), bitcast.top(stk, nopara - 2)))
   else if fsig.sym = "makereal(word seq)"then
   interpret(alltypes, code, i + 1, push(pop(stk, nopara), representation.makereal.aswords.bitcast.top.stk))
   else
    let t = dlsymbol.mangle(fsig.sym, module.sym)
    let dcret = deepcopysym(alltypes, resulttype.sym)
    let adcret = dlsymbol.mangle(fsig.dcret, module.dcret)
     assert adcret > 0 report"Not handle by interperter" + print.sym + "can not find" + print.dcret
      assert t > 0 report"Not handle by interperter" + print.sym
      let dc = deepcopysym(alltypes, mytype."word seq")
      let adc = dlsymbol.mangle(fsig.dc, module.dc)
       assert adc > 0 report"?"
       let p = createthread(adcret, adc, t, packed.top(stk, nopara))
        if aborted.p then message.p else interpret(alltypes, code, i + 1, push(pop(stk, nopara), result.p))