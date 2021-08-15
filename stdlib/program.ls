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

type program is data:set.symdef

Export data(a:program) set.symdef 

Export program(set.symdef) program

Export type:program

Function /cup(a:program,b:program) program 
  program (data.a /cup data.b )
    
Function getCode(theprg:program,s:symbol) seq.symbol 
 let f=findelement(symdef(s,empty:seq.symbol),data.theprg)
 if isempty.f then empty:seq.symbol else code.f_1
 
Function isdefined(theprg:program,s:symbol) boolean
 not.isempty.findelement(symdef(s,empty:seq.symbol),data.theprg)
  

Function print(p:program, i:symbol)seq.word  
  print.i + for acc ="", @e = getCode(p,i) do acc + print.@e /for(acc)

Function  tosymdefs(p:program)seq.symdef   toseq.data.p

Function emptyprogram program program.empty:set.symdef

Function map(p:program, s:symbol, code:seq.symbol)program 
program.replace(data.p,symdef(s,code)  )    






Export type:type2dict

Export coretype(mytype, type2dict) mytype
  
 Function packedtypes seq.mytype [
typeref(  "packed2 tausupport .")
,typeref(  "packed3 tausupport .")
,typeref(  "packed4 tausupport .")
,typeref(  "packed5 tausupport .")
,typeref(  "packed6 tausupport .")
 ]

 
Function buildargcodeI(  sym:symbol)int
 { needed because the call interface implementation for reals is different than other types is some implementations }
 for acc = 1, typ = paratypes.sym + resulttype.sym do
  acc * 2
  + if  {getbasetype(alltypes, typ)} typ  = typereal then 1 else 0
 /for(acc)  

 ----
 
use encoding.symbol

use seq.symbolref

use seq.encodingpair.symbol

use seq.seq.mytype

use set.symbolref

use seq.seq.symbolref

use seq.seq.word

use seq.libraryModule


 type symbolref is toint:int

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

Function assignencoding(l:seq.encodingpair.symbol  , symbol) int  length.l+1

Function symbolrefdecode seq.symbol
  for acc=empty:seq.symbol , p=encoding:seq.encodingpair.symbol do
              acc+data.p
        /for(acc)



type libraryModule is modname:modref, exports:seq.symbolref,
uses:seq.mytype,defines:seq.symbolref,types:seq.seq.mytype

Export libraryModule( modname:modref, exports:seq.symbolref,
uses:seq.mytype,defines:seq.symbolref,types:seq.seq.mytype)libraryModule

/Function libraryModule(modname:modref, exports:seq.symbolref,defines:seq.symbolref,types:seq.seq.mytype)libraryModule
 libraryModule(modname,exports,defines,types)

Export type:libraryModule


Export   exports(libraryModule)  seq.symbolref

Export modname(libraryModule) modref

Export uses(libraryModule) seq.mytype

Export defines(libraryModule)  seq.symbolref

Export types(libraryModule) seq.seq.mytype


Export alltypes(compileinfo)type2dict

Export type:compileinfo 

type compileinfo is typedict:type2dict  
,code:seq.seq.symbolref,src:seq.seq.word
,symbolrefdecode:seq.symbol,mods:seq.libraryModule


   Function roots(s:compileinfo) set.symbol
   for acc= empty:set.symbol, m =mods.s do 
     if issimple.modname.m then  
     for acc2=acc, r=exports.m do  
     acc2+(symbolrefdecode.s)_toint.r 
     /for(acc2)
     else acc
    /for(acc)

Export code(compileinfo) seq.seq.symbolref

Export mods(compileinfo) seq.libraryModule


Export src(compileinfo) seq.seq.word

Function prg(s:compileinfo) seq.symdef 
let symdecode=symbolrefdecode.s
  for acc4=empty:seq.symdef, c=code.s do
      acc4+symdef(symdecode_toint.first.c,
          for   acc=empty:seq.symbol, r= c << 2 do   acc+ symdecode_toint.r /for(acc))
/for(acc4)

Export typedict(compileinfo) type2dict

Export symbolrefdecode(compileinfo) seq.symbol

Function alltypes(s:compileinfo) type2dict typedict.s

 
Function  compileinfo(prg:seq.symdef, alltypes:type2dict ,mods:seq.libraryModule
,src:seq.seq.word) compileinfo
compileinfo(alltypes, cvtL3(program.asset.prg,1,empty:seq.seq.symbolref),src,symbolrefdecode,mods)


 function cvtL3(prg:program,i:int, in: seq.seq.symbolref) seq.seq.symbolref
 let x=encoding:seq.encodingpair.symbol
 if i > length.x then in 
 else 
    cvtL3(prg,length.x+1, 
       for acc=in , p=subseq(x,i,length.x)   do
         let f=findelement(symdef(data.p,empty:seq.symbol),data.prg)
         if isempty.f /or isempty.code.f_1 then  acc   
         else 
               acc+for acc2 = [ symbolref.data.p,symbolref.Lit.paragraphno.f_1], sym = code.f_1  do 
                       acc2+if isFref.sym then
                        let  discard=symbolref.basesym.sym
                        symbolref.sym 
                       else if  isrecordconstant.sym then
                        let discard= for acc3=symbolref.Lit.0 ,  sym2=removeconstant.[sym] do symbolref.sym2 /for(acc3)
                        symbolref.sym
                       else 
                        symbolref.sym /for(acc2)
                    /for(acc))
  


use set.word
  
Function addoption(p:program, s:symbol, option:seq.word)program
{ must maintain library of symbol in p}
 let f=findelement(symdef(s,empty:seq.symbol),data.p)
  let code= if isempty.f then empty:seq.symbol else code.f_1
let current = asset.getoption.code
 if current = asset.option then p
 else
  let newcode = removeoptions.code + Words.toseq(current ∪ asset.option) + Optionsym
   map(p, if isempty.f then s else sym.f_1, newcode)

