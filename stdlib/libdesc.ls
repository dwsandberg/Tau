#!/bin/sh tau   stdlib stdlib

Module libdesc

use bits

use libraryModule

use mytype

use standard

use symbol

use symref

use typedict

use set.int

use seq.liblib

use seq.libraryModule

use otherseq.mytype

use set.mytype

use seq.parc

use otherseq.symbol

use seq.symbol

use set.symbol

use encoding.symbolnew

use otherseq.symbolref

use seq.symbolref

use set.symbolref

use seq.symdef

use set.symdef

use otherseq.word

use set.word

use encoding.seq.char

use seq.seq.int

use seq.seq.symbol

use set.seq.symbol

use seq.encodingpair.symbolnew

use otherseq.seq.symbolref

use seq.seq.symbolref

use seq.seq.word

function print(l:seq.mytype)seq.word
for acc = "(", t ∈ l do acc + print.t /for(acc + ")")

Export ?(a:symbolref, b:symbolref)ordering
                     
function =(a:symbolref, b:symbolref)boolean toint.a=toint.b

Export type:compileinfo

Function compilerback2(prg10:set.symdef,oldmods:seq.libraryModule,typedict:typedict ) compileinfo
let symdecode=symbolrefdecode
let newmods = 
 for acc = empty:seq.libraryModule, @e ∈ oldmods do
  for newexports = empty:seq.symbolref, r ∈ exports.@e do newexports + symbolrefnew.symdecode_(toint.r)/for(acc + libraryModule(modname.@e, newexports, types.@e))
/for(acc) 
let code2 = libcode(prg10,oldmods,symbolrefdecode)
  let gensym=gencode(oldmods,prg10,symbolrefdecode)
  let profilearcs = 
 for acc = empty:seq.symbolref, sd ∈ toseq.prg10 do
  if isabstract.module.sym.sd ∨ symbolref.sym.sd ∉ gensym then acc
  else 
    let options=getoption.code.sd
   if"PROFILE"_1 ∈ options then
   for txt = acc, sym ∈ toseq.asset.code.sd do
     if isconstantorspecial.sym ∨ isInternal.sym then txt
     else txt + [symbolrefnew.sym.sd, symbolrefnew.sym]
   /for(txt)
   else if"COMPILETIME"_1 ∈ options then
    let discard=symbolrefnew.sym.sd
    acc
  else acc
 /for(acc)
let newmap2 = symbolrefdecodenew
for code3 = empty:seq.seq.symbolref, sd ∈ toseq.prg10 do
 if isabstract.module.sym.sd ∨ isempty.code.sd ∨ not.isrecordconstant.sym.sd ∧ isconstantorspecial.sym.sd
 ∨ symbolref.sym.sd ∉ gensym then
    code3
   else 
  for acc = [symbolrefnew.sym.sd], sym ∈ code.sd do acc + symbolrefnew.sym /for(code3 + acc)
 /for( compileinfo(typedict
 ,   [[ symbolref.0,symbolref.length.newmap2,symbolref.length.code2 ]+profilearcs]+code2+code3
 ,empty:seq.seq.word
 , symbolrefdecodenew
, newmods
))

function gencode(mods:seq.libraryModule,prg:set.symdef,refdecode:seq.symbol)set.symbolref
for acc = empty:seq.symbolref, m ∈ mods do acc + exports.m /for(for acc2 = empty:set.symbolref, r ∈ toseq.asset.acc do
  if isabstract.module.refdecode _(toint.r) then acc2 else  acc2 +  r
 /for( close(prg,acc2,empty:set.symbolref,refdecode)))
 
function close(prg:set.symdef, toprocess:set.symbolref, symlist:set.symbolref, refdecode:seq.symbol)set.symbolref
for acc = empty:seq.symbolref, symref ∈ toseq.toprocess do
 for acc2 = acc, sym ∈ toseq.asset.getCode(prg, refdecode_(toint.symref))do
  if isFref.sym then acc2 + symbolref.sym + symbolref.basesym.sym else acc2 + symbolref.sym
 /for(acc2)
/for(let newsymlist = toprocess ∪ symlist
        let newtoprocess=   asset.acc \ newsymlist  
if isempty.newtoprocess then newsymlist else close(prg, newtoprocess, newsymlist, symbolrefdecode)/if)

function libcode(prg:set.symdef,mods:seq.libraryModule,refdecode:seq.symbol)seq.seq.symbolref
let symstoexport2 = 
 for acc = empty:seq.symbolref, m ∈ mods do acc + exports.m /for(for acc2 = empty:set.symbol, r ∈ toseq.asset.acc do acc2 + refdecode_(toint.r)/for(acc2))
 for acc = empty:seq.seq.symbolref, sym ∈ toseq.symstoexport2 do
 let libsymcode = 
  if isabstract.module.sym then getCode(prg, sym)
  else libcode(prg, getCode(prg, sym), symstoexport2)
 acc
 + for acc2 = [symbolrefnew.sym], sym2 ∈ libsymcode do
  if isFref.sym2 then acc2 + symbolrefnew.PreFref + symbolrefnew.basesym.sym2
  else acc2 + symbolrefnew.sym2
  /for(acc2)
 /for(acc)

function libcode(prg:set.symdef,code1:seq.symbol, toexport:set.symbol)seq.symbol
let code = removeoptions.code1
let optionsx = getoption.code1
let z = 
 if length.code < 15 then
  let x =  removerecordconstant(prg,code)
  if"VERYSIMPLE"_1 ∈ optionsx then x
  else if for acc = true, @e ∈ x do
   acc ∧ (isconst.@e ∨ isBuiltin.@e ∧ para.module.@e ∈ [ typereal, typeint] ∨ isspecial.@e ∨ @e ∈ toexport)
  /for(acc)then
   x
  else empty:seq.symbol
 else empty:seq.symbol
if"COMPILETIME"_1 ∈ optionsx ∨ not.isempty.z then z + Words.optionsx + Optionsym else z

________________________

type symbolnew is tosymbol:symbol

function symbolrefnew(sym:symbol)symbolref symbolref.valueofencoding.encode.symbolnew.sym

function symbolrefdecodenew seq.symbol
for acc = empty:seq.symbol, p ∈ encoding:seq.encodingpair.symbolnew do acc + tosymbol.data.p /for(acc) 

function hash(a:symbolnew)int hash.tosymbol.a

function =(a:symbolnew,b:symbolnew) boolean tosymbol.a=tosymbol.b

function assignencoding(a:symbolnew) int nextencoding.a
