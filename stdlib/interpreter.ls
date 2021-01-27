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

use tausupport

Builtin bitcast(int)seq.int

Builtin GEP(seq.int,int) int 

         
use seq.myinternaltype
          
 Function interpret(code:seq.symbol) seq.symbol
    let t=[myinternaltype(first."x", "seq"_1, mytype."word seq", empty:seq.mytype)
    ,myinternaltype(first."x", "seq"_1, mytype."char seq", empty:seq.mytype)
    ,myinternaltype(first."x", "seq"_1, mytype."int seq", empty:seq.mytype)
    ,myinternaltype(first."x", "seq"_1, mytype."char seq encoding", empty:seq.mytype)
   , myinternaltype(first."x", "word"_1, mytype."words", [typeint ])
    , myinternaltype(first."x", "boolean"_1, mytype."standard", [typeint])
      , myinternaltype(first."x", "bits"_1, mytype."bits", [typeint])
      , myinternaltype(first."x", "ptr"_1, mytype."ptr", [typeint])
   ]
             let r=interpret(typedict.t,removeconstant.code,1,empty:stack.int)
        tocode(r,resulttype.last.code)
        
        encoding.seq.char
                            
  function    tocode( r:int, typ:mytype) seq.symbol     
          if typ=mytype."word" then 
               [ Word.wordencodingtoword(r) ]
               else if abstracttype.typ &in "int bits char" then [ Lit.r]
               else if abstracttype.typ ="boolean"_1 then [if r=1 then Littrue else Litfalse]
               else if typ =mytype."word seq" then [ Words.aswords.bitcast.r ]
               else if typ = mytype."real" then   [ Reallit.r ]
               else assert abstracttype.typ &in "seq" report  "resulttype not handled"+print.typ
                let s=bitcast.r
                 s @ +([Lit.0,Lit.length.s],tocode(@e,parameter.typ))

        
  function buildcode(acc:int,typ:mytype,alltypes:typedict) int  
      let xx=gettypeinfo(alltypes, typ)
        assert not.isempty.subflds.xx report "XXX"+typerep.typ
     acc * 2 +if kind.xx=first."real" then 1 else 0 
  

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
     interpret(alltypes, code, i + 1, push(stk, GEP(a,0)))
   else if module.sym = "$int" &or module.sym = "$real" &or module.sym = "$boolean" then
   interpret(alltypes, code, i + 1, push(stk, toint.(fsig.sym)_1))
   else if module.sym = "$record"  then
     if  subseq(top(stk, nopara), 1, 2) = [ 0, nopara - 2]then
      interpret(alltypes, code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara - 2),0)))
     else 
      interpret(alltypes, code, i + 1, push(pop(stk, nopara), GEP(top(stk, nopara ),2)))
   else if fsig.sym = "makereal(word seq)"then
   interpret(alltypes, code, i + 1, push(pop(stk, nopara), representation.makereal.aswords.bitcast.top.stk))
   else
    let t = dlsymbol.mangle(fsig.sym, module.sym)
    let dcret = deepcopysym(alltypes, resulttype.sym)
    let adcret = dlsymbol.mangle(fsig.dcret, module.dcret)
     assert adcret > 0 report"Not handle by interperter" + print.sym + "can not find" + print.dcret
      assert t > 0 report"Not handle by interperter" + print.sym+"mangle:"+mangle(fsig.sym, module.sym)
      let dc = deepcopysym(alltypes, mytype."word seq")
      let adc = dlsymbol.mangle(fsig.dc, module.dc)
       assert adc > 0 report"?"
       let p = createthread(adcret, adc, t, packed.top(stk, nopara), (paratypes.sym+ resulttype.sym  ) 
       @ buildcode(1,@e,alltypes))
        assert not.aborted.p   report message.p
         interpret(alltypes, code, i + 1, push(pop(stk, nopara), result.p))