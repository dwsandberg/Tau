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

use seq.firstpass


Export type:firstpass

Export  firstpass(module:modref, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.seq.mytype, p:program)firstpass

Export module(f:firstpass) modref

Export defines(firstpass)set.symbol

Export exports(firstpass)set.symbol

Export uses(firstpass)seq.mytype

Export unboundexports(firstpass)seq.symbol

Export unbound(firstpass)set.symbol

Export types(firstpass)seq.seq.mytype

Export prg(firstpass)program

type firstpass is module:modref, uses:seq.mytype, defines:set.symbol, exports:set.symbol
, unboundexports:seq.symbol, unbound:set.symbol, types:seq.seq.mytype, prg:program

Function ?(a:firstpass, b:firstpass)ordering toalphaseq.print.module.a ? toalphaseq.print.module.b

Function  firstpass(module:modref, uses:seq.mytype, defines:set.symbol, exports:set.symbol  , types:seq.seq.mytype )firstpass
firstpass(module , uses , defines , exports , empty:seq.symbol, empty:set.symbol, types, emptyprogram) 

Function firstpass(module:modref) firstpass
firstpass( module, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, empty:seq.seq.mytype, emptyprogram)
 
Function fixtype(t:seq.mytype) mytype first.t  

function subflds(t:seq.mytype) seq.mytype t << 1

function name(m:seq.mytype) word abstracttype.first.m
   
Function addtype(dict:seq.seq.mytype,name:word, module:modref,subflds:seq.mytype) seq.seq.mytype
  dict+([if not.issimple.module then 
addabstract(typeref3(module , name ),para.module)
 else typeref3(module , name )]+subflds) 
      
Function replaceTmyinternaltype(with:mytype, s:seq.seq.mytype) seq.seq.mytype
for acc = empty:seq.seq.mytype , it = s do 
  acc + (   [replaceT(with, first.it)]+it << 1 )
    /for(acc)


Function processtypedef( s:seq.firstpass) type2dict
 let a=for acc = empty:seq.seq.mytype, @e = s do acc + types.@e /for(acc)
 processtypedef(emptytypedict, a, 1, empty:seq.seq.mytype)
 
 Function processtypedef( fldtypes:seq.seq.mytype) type2dict
 processtypedef(emptytypedict, fldtypes, 1, empty:seq.seq.mytype)

 
function print3(it:seq.mytype)seq.word
    "type" +print.first.it +"subfield types" 
  + for acc ="", e = it << 1 do acc + print.e /for(acc)
      
   function processtypedef(defined:type2dict, undefined:seq.seq.mytype, i:int, newundefined:seq.seq.mytype)type2dict
 if i > length.undefined then
  if length.newundefined = 0 then defined
  else
   assert length.undefined > length.newundefined report"unresolved types:"
   + for acc ="", @e = newundefined do list(acc," /br", print3.@e)/for(acc)
   processtypedef(defined, newundefined, 1, empty:seq.seq.mytype)
 else
   let td = undefined_i
   let flds = for acc = empty:seq.mytype, idx = 1, fld = subflds.td do
   let typ=replaceT(parameter.first.td, fld)
   let tmp = if isseq.typ ∨ typ ∈ [ typeint, typereal, typeboolean, typeT]then [ typ]
 else if isencoding.typ then [ typeint] else flatflds(defined, typ)
   next(
   if idx = 1 ∨ isempty.tmp then tmp else if isempty.acc then acc else acc + tmp, idx + 1)
  /for(acc)
  if length.flds = 0 then
    { some fld is not defined }
     processtypedef(defined, undefined, i + 1, newundefined + undefined_i)
   else 
   processtypedef(add(defined,first.td ,  flds) 
   , undefined, i + 1, newundefined)

