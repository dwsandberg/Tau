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


Export type:passsymbols

/Export  firstpass(module:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol,  types:seq.seq.mytype, p:program
,seq.symtextpair)passsymbols

Function module(f:passsymbols) modref modname.f

Export modname(f:passsymbols) modref  

Export typedict(passsymbols) set.mytype

Export defines(passsymbols)set.symbol

Export exports(passsymbols)set.symbol

Export uses(passsymbols)set.modref

Export unresolvedexports(passsymbols)set.symbol


Export types(passsymbols)seq.seq.mytype

Export prg(passsymbols)program

Export text(passsymbols) seq.symtextpair

type symtextpair is sym:symbol, text:seq.word,paragraphno:int

Export symtextpair(sym:symbol, text:seq.word,paragraphno:int)symtextpair

Export text(symtextpair)seq.word

Export type:symtextpair

Export paragraphno(symtextpair) int 

Export sym(symtextpair)symbol

use set.modref

use set.mytype

type passsymbols is modname:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol
, typedict:set.mytype, text:seq.symtextpair , types:seq.seq.mytype, prg:program

Export passsymbols(modname:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol
, typedict:set.mytype, text:seq.symtextpair , types:seq.seq.mytype, prg:program
) passsymbols

modname , uses , defines , exports, unresolvedexports, typedict , text  , types , prg 

Function firstpass(modname:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol
, typedict:set.mytype, types:seq.seq.mytype, prg:program,text:seq.symtextpair) passsymbols
passsymbols(modname,uses,defines,exports,unresolvedexports,
 typedict ,text,types,prg) 

/Function  passsymbols(modname:modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol
, uses:set.modref, typedict:set.mytype, text:seq.symtextpair 
) passsymbols
passsymbols(modname, uses ,defines , exports , unresolvedexports 
,  typedict , text,empty:seq.seq.mytype,emptyprogram )

/Function ?(a:passsymbols, b:passsymbols)ordering toalphaseq.print.module.a ? toalphaseq.print.module.b

Function  firstpass(modname1:modref, uses:set.modref, defines:set.symbol, exports:set.symbol  , types:seq.seq.mytype )passsymbols
passsymbols(modname1 , uses , defines , exports , empty:set.symbol
, empty:set.mytype, empty:seq.symtextpair , types, emptyprogram)


Function firstpass(modname:modref) passsymbols
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

   
