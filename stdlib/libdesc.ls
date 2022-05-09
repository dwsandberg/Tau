Module libdesc

use bits

use codegennew

use inputoutput

use libraryModule

use standard

use symbol2

use set.int

use seq.liblib

use seq.libraryModule

use otherseq.mytype

use set.mytype

use seq.parc

use encoding.symbol

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

use seq.seq.int

use seq.seq.symbol

use set.seq.symbol

use otherseq.seq.symbolref

use seq.seq.symbolref

use seq.seq.word

function print(l:seq.mytype)seq.word
for acc = "(", t ∈ l do acc + print.t /for(acc + ")")

Export ?(a:symbolref, b:symbolref)ordering

Export callfunc(ctsym:symbol, typedict:typedict, stk:seq.int)seq.int

Export dependentinfo(dependentlibs:seq.word)midpoint

use symbol

/Function gatherfref(s:seq.symbol) set.symbol {OPTION PROFILE}
 for acc=empty:set.symbol,  sym /in s do    
    if hasfref.sym then 
      if isFref.sym then acc+basesym.sym
      else acc /cup   gatherfref(fullconstantcode.sym )  
    else acc 
/for(acc)



function gatherfref(p:set.symdef, s:seq.symbol)set.symbol
for code = empty:set.symbol, sym ∈ s do
  if isFref.sym then code+basesym.sym
  else 
 if not.hasfref.sym then code  
 else code  /cup  gatherfref(p, getCode(p, sym))
/for(code)


function bbb(prg:set.symdef,   toexport:set.symbol)seq.symbol 
for  new=empty:seq.symbol,     sym /in toseq.toexport do 
let code1= getCode(prg,sym)
let code = removeoptions.code1
let optionsx = getoption.code1
if length.code > 14 then new
else 
   let z=if"VERYSIMPLE"_1 ∈ optionsx then code
  else   
   for acc = true, @e ∈ code do
   acc ∧ (isconstantorspecial.@e ∨ isBuiltin.@e  ∨ @e ∈ toexport
   ∨ isInternal.@e)
  /for( if acc then  code else empty:seq.symbol)
  for acc=new,   sym2 /in z   do 
   if isFref.sym2 /or hasfref.sym2 then  acc+ toseq.gatherfref(prg,[sym2  ] )
   else if isconst.sym2 ∨ isBuiltin.sym2  ∨ isspecial.sym2 ∨ sym2 ∈ toexport
   ∨ isInternal.sym2  then acc
   else  acc+sym2  
   /for(acc)
/for(toseq.asset.new)  
         

Function compilerback2(prg10:set.symdef
, oldmods:seq.modExports
, typedict:typedict
, src:seq.seq.word
, uses:seq.word
, dependentlibs:midpoint
)seq.bits
{OPTION PROFILE}
let libname = extractValue(first.src, "Library")_1
let maybereferenced0 = 
 for acc = empty:seq.symbol, @e ∈ oldmods do
  for acc2 = acc, sym ∈ exports.@e do
   if isabstract.module.sym ∨ library.module.sym ≠ libname then acc2 else 
     acc2+sym
  /for(acc2 )
 /for(acc)
let maybereferenced1 = 
 for acc = maybereferenced0+bbb(prg10,   asset.maybereferenced0), sd ∈ toseq.prg10 do
  if"COMPILETIME"_1 ∈ getoption.code.sd then
   acc+sym.sd
  else acc
 /for(acc)
let profilearcs = 
 for acc = empty:set.seq.symbol, sd ∈ toseq.prg10 do
  if isabstract.module.sym.sd  then acc
  else
   let options = getoption.code.sd
   if"PROFILE"_1 ∈ options then
    for txt = acc, sym ∈ toseq.asset.code.sd do
     if isconstantorspecial.sym ∨ isInternal.sym ∨ sym = sym.sd /or isBuiltin.sym then txt
     else 
     txt + [ sym.sd,  sym]
    /for(txt)
   else acc
 /for(acc)
 let maybereferenced2=for acc=empty:seq.symbol , a /in toseq.profilearcs do acc+a 
 /for(maybereferenced1+acc)
let discard22= for acc=symbolref.0,   sym /in maybereferenced2 do symbolrefnew.sym /for(acc)
 let addresses = length.symbolrefdecodenew
 let newmods = 
 for acc = empty:seq.libraryModule, @e ∈ oldmods do
  for newexports = empty:seq.symbolref, sym ∈ exports.@e do newexports + symbolrefnew.sym /for(acc + libraryModule(modname.@e, newexports, types.@e))
 /for(acc)
let code2 = libcode(prg10, oldmods, symbolrefdecode)
let gensym = gencode(convert.oldmods, prg10, symbolrefdecode)
let newmap2 = symbolrefdecodenew
for code3 = empty:seq.seq.symbolref, sd ∈ toseq.prg10 do
 if isabstract.module.sym.sd ∨ isempty.code.sd ∨ not.isrecordconstant.sym.sd ∧ isconstantorspecial.sym.sd
 ∨ symbolref.sym.sd ∉ gensym then
  code3
 else
  for acc = [symbolrefnew.sym.sd], sym ∈ code.sd do
   if isFref.sym then acc + symbolref.-toint.symbolrefnew.basesym.sym else acc + symbolrefnew.sym
  /for(code3 + acc)
/for(let finaldecode = symbolrefdecodenew
assert cardinality.asset.symbolrefdecodenew = length.symbolrefdecodenew report "KLJDSF"+%.cardinality.asset.symbolrefdecodenew
 +%.length.symbolrefdecodenew
 +for acc=empty:set.symbol,txt="", sym /in symbolrefdecodenew do
    if sym /in acc then next(acc,txt+print.sym) else next( acc+sym,txt) /for(txt)
codegen(libname
, typedict
, newmods
, dependentlibs
, dependentwords.uses
, finaldecode
, profilearcs 
,  profiledata(finaldecode,  profilearcs)
,  code3 
, code2
, subseq(finaldecode, 1, length.newmap2)
, subseq(finaldecode, 1, addresses)
))

use otherseq.int


Function profiledata(decode:seq.symbol,profilearcs:set.seq.symbol) seq.int
   for  acc= [1, cardinality.profilearcs ],        a /in toseq.profilearcs do
    let tail=findindex( a_1,decode)
    let head=findindex( a_2,decode)
    assert tail > 0 /and head > 0 /and head /le length.decode /and tail /le length.decode
    report "CCC"+print.a
    acc+[tail,head,0,0,0,0]
    /for(acc)

use seq.symbol

/function replace(s:seq.symbol, old:symbol, new:symbol)seq.symbol
for acc = empty:seq.symbol, changed = false, sym ∈ s do
 if isFref.sym ∧ basesym.sym = old then next(acc + Fref.new, true)
 else if sym = old then next(acc + new, true)else next(acc + sym, false)
/for(if changed then acc else empty:seq.symbol /if)

function gencode(mods:seq.libraryModule, prg:set.symdef, refdecode:seq.symbol)set.symbolref
{/OPTION PROFILE}
for acc = empty:seq.symbolref, m ∈ mods do acc + exports.m /for(for acc2 = empty:set.symbolref, r ∈ toseq.asset.acc do
 if isabstract.module.refdecode_(toint.r)then acc2 else acc2 + r
/for(close(prg, acc2, empty:set.symbolref, refdecode)))

function close(prg:set.symdef, toprocess:set.symbolref, symlist:set.symbolref, refdecode:seq.symbol)set.symbolref
{/OPTION PROFILE}
for acc = empty:seq.symbolref, symref ∈ toseq.toprocess do
 for acc2 = acc, sym ∈ toseq.asset.getCode(prg, refdecode_(toint.symref))do
  if isFref.sym then acc2 + symbolref.sym + symbolref.basesym.sym else acc2 + symbolref.sym
 /for(acc2)
/for(let newsymlist = toprocess ∪ symlist
let newtoprocess = asset.acc \ newsymlist
if isempty.newtoprocess then newsymlist else close(prg, newtoprocess, newsymlist, symbolrefdecode)/if)

function libcode(prg:set.symdef, mods:seq.modExports, refdecode:seq.symbol)seq.seq.symbolref
let symstoexport2 = for acc = empty:seq.symbol, m ∈ mods do acc + exports.m /for(asset.acc)
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

function libcode(prg:set.symdef, code1:seq.symbol, toexport:set.symbol)seq.symbol
let code = removeoptions.code1
let optionsx = getoption.code1
let z = 
 if length.code < 15 then
  let x = removerecordconstant(prg, code)
  if"VERYSIMPLE"_1 ∈ optionsx then x
  else for acc = true, @e ∈ x do
   acc ∧ (isconstantorspecial.@e ∨ isBuiltin.@e   ∨ @e ∈ toexport)
  /for(if acc then x else empty:seq.symbol) 
 else empty:seq.symbol
if"COMPILETIME"_1 ∈ optionsx ∨ not.isempty.z then z + Words.optionsx + Optionsym else z

function removerecordconstant(p:set.symdef, s:seq.symbol)seq.symbol
for code = empty:seq.symbol, sym ∈ s do
 if not.isrecordconstant.sym then code + sym else code + removerecordconstant(p, getCode(p, sym))
/for(code)

________________________

type symbolnew is tosymbol:symbol

function symbolrefnew(sym:symbol)symbolref symbolref.addorder.symbolnew.sym

function symbolrefdecodenew seq.symbol
for acc = empty:seq.symbol, p ∈ encodingdata:symbolnew do acc + tosymbol.p /for(acc)

function hash(a:symbolnew)int hash.tosymbol.a

function =(a:symbolnew, b:symbolnew)boolean tosymbol.a = tosymbol.b

function assignencoding(a:symbolnew)int nextencoding.a 