module interpreter

use UTF8

use fileio

use process.int

use process.seq.int

use seq.int

use seq.seq.int

use stack.int

use mangle

use seq.mytype

use pass1

use real

use standard

use seq.symbol

use symbol

use words

Builtin bitcast(seq.int)int

Builtin bitcast(int)seq.int

Builtin dlsymbol(cstr)int

 
Builtin createthread(int, int, int, seq.int,int)process.int


Function dlsymbol(name:word)int dlsymbol.tocstr.[ name]

         
use seq.myinternaltype
          
 Function interpret(code:seq.symbol) seq.symbol
    let t=[myinternaltype(first."x", "seq"_1, mytype."word seq", empty:seq.mytype)
    ,myinternaltype(first."x", "seq"_1, mytype."char seq", empty:seq.mytype)
    ,myinternaltype(first."x", "seq"_1, mytype."int seq", empty:seq.mytype)
   , myinternaltype(first."x", "word"_1, mytype."words", empty:seq.mytype)
    , myinternaltype(first."x", "boolean"_1, mytype."standard", empty:seq.mytype)
   ]
             let r=interpret(typedict.t,removeconstant.code,1,empty:stack.int)
        tocode(r,resulttype.last.code)
                            
  function    tocode( r:int, typ:mytype) seq.symbol     
          if typ=mytype."word" then 
               [ Word.wordencodingtoword(r) ]
               else if abstracttype.typ &in "int bits char boolean" then [ Lit.r]
               else if typ =mytype."word seq" then [ Words.aswords.bitcast.r ]
               else if typ = mytype."real" then   [ Reallit.r ]
               else assert abstracttype.typ &in "seq" report  "resulttype not handled"+print.typ
                let s=bitcast.r
                 s @ +([Lit.0,Lit.length.s],tocode(@e,parameter.typ))

        
  function buildcode(acc:int,typ:mytype,alltypes:typedict) int     
   acc * 2 +if kind.gettypeinfo(alltypes, typ)=first."real" then 1 else 0 
  

function aswords(s:seq.int)seq.word s @ +("", wordencodingtoword(@e))

use process.int

Function interpret(alltypes:typedict, code:seq.symbol)seq.word 
  aswords.bitcast.interpret(alltypes, code, 1, empty:stack.int)

 let p=process.interpret(alltypes, code, 1, empty:stack.int)
 if aborted.p then message.p else 
aswords.bitcast.result.p

function interpret(alltypes:typedict, code:seq.symbol, i:int, stk:stack.int) int
 if i > length.code then  top.stk
 else
  let sym = code_i
  let nopara = nopara.sym
   if module.sym= "$word" then
      interpret(alltypes, code, i + 1, push(stk,  hash.first.fsig.sym))
   else if module.sym = "$words"then
   let a = fsig.sym @ +(empty:seq.int, hash.@e)
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
       let p = createthread(adcret, adc, t, packed.top(stk, nopara), (paratypes.sym+ resulttype.sym  ) 
       @ buildcode(1,@e,alltypes))
        assert not.aborted.p   report message.p
         interpret(alltypes, code, i + 1, push(pop(stk, nopara), result.p))