Module program


use symbol

use seq.symbol

use seq.symdef

use standard

use seq.set.symdef

use set.symdef

use seq.mytype

use seq.symdef

use set.symbol

use mytype

use typedict

type program is dataX:set.symdef

Export   dataX(a:program) set.symdef 

Export program(set.symdef) program

Export type:program

Function /cup(a:program,b:program) program 
  program (dataX.a /cup dataX.b )
    
Function getCode(theprg:program,s:symbol) seq.symbol 
 let f=findelement(symdef(s,empty:seq.symbol),dataX.theprg)
 if isempty.f then empty:seq.symbol else code.f_1
 
Function isdefined(theprg:program,s:symbol) boolean
 not.isempty.findelement(symdef(s,empty:seq.symbol),dataX.theprg)
  
Function  tosymdefs(p:program)seq.symdef   toseq.dataX.p

Function emptyprogram program program.empty:set.symdef

Function /cup ( a:symdef,p:program )  program
  program( a /cup dataX.p)




Export type:typedict

Export coretype(mytype, typedict) mytype
  
 

 
  

 ----
 
use encoding.symbol

use seq.symbolref

use seq.encodingpair.symbol

use seq.seq.mytype

use set.symbolref

use seq.seq.symbolref

use seq.seq.word

use seq.libraryModule



Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

Function assignencoding(l:seq.encodingpair.symbol  , symbol) int  length.l+1

Function decode(s:symbolref) symbol decode(to:encoding.symbol(toint.s))

Function symbolrefdecode seq.symbol
  for acc=empty:seq.symbol , p=encoding:seq.encodingpair.symbol do
              acc+data.p
        /for(acc)


use libraryModule

Export libraryModule( modname:modref, exports:seq.symbolref,types:seq.seq.mytype)libraryModule


Export type:libraryModule

Export   exports(libraryModule)  seq.symbolref

Export modname(libraryModule) modref

Export types(libraryModule) seq.seq.mytype

Export alltypes(compileinfo)typedict

Export type:compileinfo 

type compileinfo is typedict:typedict  
,code:seq.seq.symbolref,src:seq.seq.word
,symbolrefdecode:seq.symbol,mods:seq.libraryModule
,Xroots:seq.symbolref


   Function roots(s:compileinfo) set.symbol
   for acc= empty:set.symbol, r=Xroots.s do 
      acc+(symbolrefdecode.s)_toint.r 
    /for(acc)
    
    

Export code(compileinfo) seq.seq.symbolref

Export mods(compileinfo) seq.libraryModule


Export src(compileinfo) seq.seq.word

Function prg(s:compileinfo) seq.symdef 
let symdecode=symbolrefdecode.s
  for acc4=empty:seq.symdef, c=code.s do
       let sym=symdecode_toint.first.c
      acc4+symdef(sym,
          for   acc=empty:seq.symbol, r= c << 2 do   acc+ symdecode_toint.r 
          /for(  acc ))
/for(acc4)



Export typedict(compileinfo) typedict

Export symbolrefdecode(compileinfo) seq.symbol

Function alltypes(s:compileinfo) typedict typedict.s

 
Function  compileinfo(prg:seq.symdef, alltypes:typedict ,mods:seq.libraryModule
,src:seq.seq.word,roots:set.symbol) compileinfo
let roots2=for acc=empty:seq.symbolref , sym=toseq.roots do acc+symbolref.sym /for(acc)
compileinfo(alltypes, cvtL3(program.asset.prg,1,empty:seq.seq.symbolref),src,symbolrefdecode,mods,roots2)

 function cvtL3(prg:program,i:int, in: seq.seq.symbolref) seq.seq.symbolref
 let x=encoding:seq.encodingpair.symbol
 if i > length.x then in 
 else 
    cvtL3(prg,length.x+1, 
       for acc=in , p=subseq(x,i,length.x)   do
         let f=findelement(symdef(data.p,empty:seq.symbol),dataX.prg)
         if isempty.f /or isempty.code.f_1 then  acc   
         else 
               acc+for acc2 = [ symbolref.data.p,symbolref.Lit.paragraphno.f_1], sym = code.f_1  do 
                       acc2+if isFref.sym then
                        let  discard=symbolref.basesym.sym
                        symbolref.sym 
                       else if  isrecordconstant.sym then
                        let discard= for acc3=symbolref.Lit.0 ,  sym2=removeconstantcode.[sym] do symbolref.sym2 /for(acc3)
                        symbolref.sym
                       else 
                        symbolref.sym /for(acc2)
                    /for(acc))
  


use set.word
  
Function addoption(p:program, s:symbol, option:seq.word)program
{ must maintain library of symbol in p}
 let f=findelement(symdef(s,empty:seq.symbol),dataX.p)
 let code= if isempty.f then empty:seq.symbol else code.f_1
 let current = asset.getoption.code
 if current = asset.option then p
 else
  let newcode = removeoptions.code + Words.toseq(current ∪ asset.option) + Optionsym
   symdef( if isempty.f then s else sym.f_1, newcode) /cup p 
   
Function addoption(code:seq.symbol,option:seq.word) seq.symbol
  let current = asset.getoption.code
  let new= current ∪ asset.option
  if cardinality.new=cardinality.current then code
  else  removeoptions.code + Words.toseq(new) + Optionsym
   
