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

Export  firstpass(module:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol,  types:seq.seq.mytype, p:program
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


function firstpass(modname:modref, uses:set.modref, defines:set.symbol, exports:set.symbol
, unresolvedexports:set.symbol,  types:seq.seq.mytype, prg:program,text:seq.symtextpair) passsymbols
passsymbols(modname,uses,defines,exports,unresolvedexports,empty:set.mytype,text,types,prg) 

Function  passsymbols(
modname:modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol, uses:set.modref, typedict:set.mytype, text:seq.symtextpair 
) passsymbols
passsymbols(modname, uses ,defines , exports , unresolvedexports ,  typedict , text,empty:seq.seq.mytype,emptyprogram )

/Function ?(a:passsymbols, b:passsymbols)ordering toalphaseq.print.module.a ? toalphaseq.print.module.b

Function  firstpass(module:modref, uses:set.modref, defines:set.symbol, exports:set.symbol  , types:seq.seq.mytype )passsymbols
firstpass(module , uses , defines , exports 
, empty:set.symbol,  types, emptyprogram,empty:seq.symtextpair) 

Function firstpass(module:modref) passsymbols
firstpass( module, empty:set.modref, empty:set.symbol, empty:set.symbol
, empty:set.symbol, empty:seq.seq.mytype, emptyprogram,empty:seq.symtextpair)
 
Function fixtype(t:seq.mytype) mytype first.t  

/function name(m:seq.mytype) word abstracttype.first.m
   
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
