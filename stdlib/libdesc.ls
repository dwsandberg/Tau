#!/bin/sh tau   stdlib stdlib

Module libdesc


use bits

use compilerfront

use libraryModule

use mytype

use standard

use symbol

use symref

use set.int

use seq.liblib

use otherseq.mytype

use set.mytype

use seq.parc

use otherseq.symbol

use seq.symbol

use set.symbol

use otherseq.symbolref

use seq.symbolref

use set.symbolref

use set.symdef

use otherseq.word

use set.word

use encoding.seq.char



use seq.seq.int

use seq.seq.symbol

use set.seq.symbol

use seq.seq.symbolref

use seq.seq.word

use codegennew

function print(l:seq.mytype)seq.word
for acc = "(", t ∈ l do acc + print.t /for(acc + ")")

Export ?(a:symbolref, b:symbolref)ordering
                     


use mytype

Export type:compileinfo

Function compilerback(info:compileinfo,libname:seq.word,dependentlibs:seq.word ) seq.word
let prg10 = asset.prg.info  
  let newmods= for acc = empty:seq.libraryModule, @e ∈ mods.info do 
    for newexports = empty:seq.symbolref, r ∈ exports.@e do 
    newexports +  symbolrefnew.(symbolrefdecode.info)_toint.r
  /for (   acc + libraryModule(modname.@e,newexports  ,types.@e))
/for(acc) 
let code2 = libcode(prg10,mods.info,symbolrefdecode.info)
 let gensym=gencode(mods.info,code.info,symbolrefdecode.info)
let prg= for  acc=empty:seq.symdef,  sd /in toseq.prg10 do
   if  isabstract.module.sym.sd /or  symbolref.sym.sd /nin gensym then acc
   else acc+sd 
 /for(asset.acc)
 let profilearcs = 
 for acc = [ symbolref.0 ], sd ∈ toseq.prg10 do
  if  isabstract.module.sym.sd /or "PROFILE"_1 ∉ getoption.code.sd /or symbolref.sym.sd /nin gensym  then acc
  else
   for txt = acc, sym ∈ toseq.asset.code.sd do
    if isconstantorspecial.sym ∨ isInternal.sym then txt else txt + [  
     symbolrefnew.sym.sd, symbolrefnew.sym]
   /for(txt)
 /for(acc)
 let newmap2=symbolrefdecodenew
let bc = 
 codegen(prg  
 , last.libname
 , compileinfo(typedict.info
 ,   [profilearcs]+code2
 ,empty:seq.seq.word
 , { decode ref } newmap2
, newmods)
 , isempty.dependentlibs
 , length.newmap2  
 )
let z2 = createlib(bc, last.libname, dependentlibs)
"OK"


use seq.seq.symbolref

use sparseseq.seq.symbolref

function gencode(mods:seq.libraryModule,code:seq.seq.symbolref,refdecode:seq.symbol)set.symbolref
let code2=for acc=sparseseq(empty:seq.symbolref), row /in code do 
   replaceS(acc,toint.first.row,[row << 1]) 
/for(
 for  acc2=acc,idx=1,sym /in refdecode do
                next(if isFref.sym then 
                replaceS(acc2, idx,[[symbolref.basesym.sym]]) else acc2,
                 idx+1)
           /for (acc2))
 for acc = empty:seq.symbolref, m ∈ mods do acc + exports.m 
 /for
 (for acc2 = empty:set.symbolref, r ∈ toseq.asset.acc do 
  if isabstract.module.refdecode _(toint.r) then acc2 else  acc2 +  r
 /for(
 close(code2,acc2,empty:set.symbolref,refdecode))
 )
 
 function close(symdefs:seq.seq.symbolref,toprocess:set.symbolref,symlist:set.symbolref,refdecode:seq.symbol)
  set.symbolref
 for acc = empty:seq.symbolref, sym /in toseq.toprocess do
           acc+  symdefs_toint.sym
 /for( let newsymlist=toprocess /cup symlist
        let newtoprocess=   asset.acc \ newsymlist  
   { assert false report "XXX"+toword.cardinality.newtoprocess +for acc4="", r2 /in toseq( newtoprocess) do
       acc4+ print.( refdecode)_toint.r2+EOL
  /for(acc4)}
       if isempty.newtoprocess then newsymlist else close(symdefs,newtoprocess,newsymlist,refdecode) 
  )




use seq.libraryModule

function libcode(prg:set.symdef,mods:seq.libraryModule,refdecode:seq.symbol)seq.seq.symbolref
let symstoexport2 = 
 for acc = empty:seq.symbolref, m ∈ mods  do acc + exports.m /for(
 for acc2 = empty:set.symbol, r ∈ toseq.asset.acc do acc2 + (refdecode)_(toint.r)/for(acc2))
 for acc = empty:seq.seq.symbolref, sym ∈ toseq.symstoexport2 do
   let libsymcode=if isabstract.module.sym then getCode(prg, sym)else libcode(prg,getCode(prg, sym), symstoexport2)
   acc + for acc2 = [ symbolrefnew.sym] , sym2 ∈ libsymcode
  do
   if isFref.sym2 then acc2 + symbolrefnew.PreFref + symbolrefnew.basesym.sym2 else acc2 + symbolrefnew.sym2
  /for(acc2)
 /for(acc)


-------------------------- 