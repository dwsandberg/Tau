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

Export libraryModule ( modname:modref, exports:seq.symbolref,
uses:seq.mytype,defines:seq.symbolref,types:seq.seq.mytype)libraryModule

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

Module firstpass

    
use program

use symbol 

use seq.symbol

use set.symbol

use words

use seq.mytype
 
use standard

use set.word

use set.symdef

use mytype

use parse

use symboldict
     
use seq.seq.mytype

use seq.passsymbols

use seq.symtextpair


type symtextpair is sym:symbol, text:seq.word,paragraphno:int

Export symtextpair(sym:symbol, text:seq.word,paragraphno:int)symtextpair

Export text(symtextpair)seq.word

Export type:symtextpair

Export paragraphno(symtextpair) int 

Export sym(symtextpair)symbol



Export type:passsymbols


Function module(f:passsymbols) modref modname.f

Export modname(f:passsymbols) modref  

Export typedict(passsymbols) set.mytype

Export defines(passsymbols)set.symbol

Export exports(passsymbols)set.symbol

Export uses(passsymbols)set.modref

Export unresolvedexports(passsymbols)set.symbol


Export types(passsymbols)seq.seq.mytype

Function prg(passsymbols)program emptyprogram

Export text(passsymbols) seq.symtextpair


use set.modref

use set.mytype

type passsymbols is modname:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol
, typedict:set.mytype, text:seq.symtextpair , types:seq.seq.mytype, unused:program

Export passsymbols(modname:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol
, typedict:set.mytype, text:seq.symtextpair , types:seq.seq.mytype, prg:program
) passsymbols


Function passsymbols(modname:modref, uses:set.modref) passsymbols
passsymbols(modname,uses,empty:set.symbol, empty:set.symbol, empty:set.symbol
, empty:set.mytype, empty:seq.symtextpair , empty: seq.seq.mytype, emptyprogram) 




Function passsymbols(modname:modref) passsymbols
passsymbols( modname, empty:set.modref, empty:set.symbol, empty:set.symbol, empty:set.symbol
, empty:set.mytype, empty:seq.symtextpair , empty: seq.seq.mytype, emptyprogram)
 

    
Function addtype(dict:seq.seq.mytype,name:word, module:modref,subflds:seq.mytype) seq.seq.mytype
  dict+([if not.issimple.module then 
addabstract(typeref3(module , name ),para.module)
 else typeref3(module , name )]+subflds) 
      
Function replaceTmyinternaltype(with:mytype, s:seq.seq.mytype) seq.seq.mytype
for acc = empty:seq.seq.mytype , it = s do 
  acc +  replaceT(with,it)
    /for(acc)

function replaceT(with:mytype,s:seq.mytype) seq.mytype
  for acc=empty:seq.mytype , t=s do acc+replaceT(with,t) /for(acc)
  
  ---------
  
 type loadedresult is mods:seq.passsymbols,types:seq.seq.mytype ,prg:seq.symdef
 
 Export  mods(loadedresult ) seq.passsymbols
 
 Export  types(loadedresult ) seq.seq.mytype
 
 Export prg(loadedresult )seq.symdef
 
 Export type:loadedresult
 
 Function libmodules2(dependentlibs:seq.word) loadedresult
 for mods = empty:seq.passsymbols,types=empty:seq.seq.mytype,prg=empty:seq.symdef, l = loadedLibs do  
  if(libname.l)_1 ∈ dependentlibs then  
     let t= toloadedresult.l
      next(mods+mods.t, types+types.t,prg+prg.t)
  else  next(mods,types,prg)
  /for(loadedresult(mods,types,prg))
 
 function  toloadedresult(ll:liblib) loadedresult
  let  prg=        for acc=empty:seq.symdef, c=code.ll do
              let sym= (decoderef.ll)_(toint.c_1)
              let code=for acc2=empty:seq.symbol,r=c << 1 do
                   acc2+(decoderef.ll)_(toint.r)
                   /for(acc2)
                acc+symdef(sym,code)
                /for(acc)
 for   mods=empty:seq.passsymbols, types1=empty:seq.seq.mytype, m=newmods.ll do
    let defines=for defines=empty:set.symbol,r=defines.m do defines+( decoderef.ll)_toint.r
            /for(defines)
      let modx=for exports=empty:seq.symbol,types=empty:seq.mytype,r=exports.m do  
          let sym=( decoderef.ll)_toint.r  
          next(exports+sym,if name.sym="type"_1 then types+resulttype.sym else types)
      /for( passsymbols5(modname.m,cvttomodrefs.uses.m,defines,asset.exports,asset.types,types.m))
      next( mods+modx, types1+types.m)
   /for(loadedresult(mods,types1,prg))  
   
   use libdesc
   
   use seq.symdef
   
   use seq.symbolref
   
   function  cvttomodrefs(in:seq.mytype)    set.modref
  for acc=empty:set.modref,   m=in do acc+tomodref.m /for(acc)
   
   function passsymbols5(modname:modref,uses:set.modref,defines:set.symbol,exports:set.symbol, typedict:set.mytype,types:seq.seq.mytype) passsymbols
 passsymbols(modname, uses,defines, exports , empty:set.symbol  
 , typedict, empty:seq.symtextpair,types,emptyprogram)
 
 use seq.modref
 
  Function ?(a:passsymbols, b:passsymbols)ordering   module.a ? module.b

   
