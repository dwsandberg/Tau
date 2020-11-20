 module interpreter

use stdlib

use words

use fileio

use symbol

use seq.symbol

use mangle

use seq.int

use seq.seq.int

use pass1

use encoding.seq.char

use seq.encoding.seq.char

use process.int

use stack.int

use process.seq.int
   
Builtin bitcast(seq.int)int

Builtin bitcast(int)seq.int


Builtin dlsymbol(seq.bits) int

Builtin process5(seq.int) process.int 

Function dlsymbol(name:word)int  dlsymbol(toCformat.[ name])


function aswords(s:seq.int) seq.word
 @(+,word,"",@(+,to:encoding.seq.char,empty:seq.encoding.seq.char,s))

use seq.mytype

use real

use UTF8

Function interpret(alltypes:typedict,code:seq.symbol)  seq.word interpret(alltypes,code ,1,empty:stack.int)

function interpret(alltypes:typedict,code:seq.symbol,i:int,stk:stack.int)  seq.word
 if i > length.code then 
    aswords.bitcast.top.stk
 else 
 let sym=code_i
 let nopara=nopara.sym
 if module.sym="$words" then 
   let a =  @(+,hash,empty:seq.int,fsig.sym)
      interpret(alltypes,code,i+1,push(stk,bitcast.a))
   else   if module.sym="$int" then
       interpret(alltypes,code,i+1,push(stk,toint.(fsig.sym)_1)) 
     else   if module.sym="$record" &and subseq(top(stk,nopara),1,2)=[0,nopara-2] then
         interpret(alltypes,code,i+1,push(pop(stk,nopara),bitcast.top(stk,nopara-2)))
    else if fsig.sym="makereal(word seq)" then
          interpret(alltypes,code,i+1,push(pop(stk,nopara), representation.makereal(aswords.bitcast.top.stk)))  
  else  
    let t=dlsymbol.mangle(fsig.sym,module.sym)
    let dcret= deepcopysym(alltypes,resulttype.sym)
    let adcret=dlsymbol.mangle(fsig.dcret,module.dcret)
    assert adcret > 0 report "Not handle by interperter"+ print.sym+"can not find"+print.dcret
     assert t > 0 report "Not handle by interperter"+ print.sym
     let dc=deepcopysym(alltypes,mytype."word seq")
     let adc=dlsymbol.mangle(fsig.dc,module.dc)
     assert adc > 0 report "?"
        let x=packed([adcret,adc,t,nopara]+ top(stk,nopara)   )
      let p=process5.x 
        if aborted.p then message.p else 
       interpret(alltypes,code,i+1, push(pop(stk,nopara),result.p))
       
 