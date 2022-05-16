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


function gatherfref(p:set.symdef, s:seq.symbol)set.symbol
for code = empty:set.symbol, sym ∈ s do
  if isFref.sym then code+basesym.sym
  else 
 if not.hasfref.sym then code  
 else code  /cup  gatherfref(p, getCode(p, sym))
/for(code)



function close(prg:set.symdef,toprocess:set.symbol,processed:set.symbol,len:int)set.symbol
   let toexport= toprocess \ processed 
    for  new=empty:seq.symbol,     sym /in toseq.toexport do 
let code = removeoptions.getCode(prg,sym)
   if len > 0 /and length.code /ge len then  new else  
   for acc=new,   sym2 /in code   do 
   if isrecordconstant.sym2 then acc+sym2
   else if isFref.sym2 then      acc+basesym.sym2 
   else if isconstantorspecial.sym2 then acc
   else if name.module.sym2 /in "internal" then
     if name.sym2 /in "stacktrace" then acc+sym2 else acc
   else if   name.module.sym2 /in " builtin   $for $base "  then acc
   else  acc+sym2  
   /for(acc)
/for(
   if isempty.toexport then processed else 
     close(prg,asset.new,processed /cup toprocess,len))
     
     
         
function roots(s1:seq.modExports)set.symbol
  for exports = empty:seq.symbol, m ∈ s1 do exports + exports.m /for(asset.exports)


Function compilerback2(prg10:set.symdef
, oldmods:seq.modExports
, typedict:typedict
, libname:word
, uses:seq.word
, dependentlibs:midpoint
)seq.bits
{OPTION PROFILE}
let libextnames = 
 for acc = empty:seq.symdef, sd ∈ toseq.prg.dependentlibs do 
    if paragraphno.sd = 0 then acc else 
    {let sd1=lookup(prg10,symdef(sym.sd,empty:seq.symbol,0) )
    assert isempty.sd1 /or paragraphno.sd=paragraphno.sd1_1 
    report "XJKL"+print.sym.sd+%.paragraphno.sd+%.paragraphno.sd1_1}
    acc + sd 
 /for(asset.acc)
 let symsforlib=roots.oldmods
 let z=close(prg10,roots.oldmods,empty:set.symbol,15) 
 {assert false report print.toseq(close(prg10,roots.oldmods,empty:set.symbol,15) \ symsforlib)
}let maybereferenced0 = close(prg10,z,empty:set.symbol,0)
let profilearcs = 
 for acc = empty:set.seq.symbol, sd ∈ toseq.prg10 do
  if isabstract.module.sym.sd /or sym.sd /nin maybereferenced0 then acc
  else
   let options = getoption.code.sd
   if"PROFILE"_1 ∈ options then
    for txt = acc, sym ∈ toseq.asset.code.sd do
     if isconstantorspecial.sym  ∨ sym = sym.sd 
      /or name.module.sym /in "$base $for builtin internal" then txt
     else 
     assert sym /in maybereferenced0 report "profile X"+print.sym
     txt + [ sym.sd,  sym]
    /for(txt)
   else acc
 /for(acc)
let addresses= for acc=symbolref.0, other=empty:seq.symbol, sym /in toseq.maybereferenced0 do 
  if isabstract.module.sym /or isrecordconstant.sym then 
   next(acc,other+sym) else  next(symbolrefnew.sym,other) 
   /for(let addresses = length.symbolrefdecodenew
    let discard23=for acc2=symbolref.0, sym2 /in other do  symbolrefnew.sym2 /for(acc2) 
  addresses)
 let newmods = 
 for acc = empty:seq.libraryModule, @e ∈ oldmods do
  for newexports = empty:seq.symbolref, sym ∈ exports.@e do newexports + symbolrefnew.sym /for(acc + libraryModule(modname.@e, newexports, types.@e))
 /for(acc)
 {assert addresses =length.symbolrefdecodenew report 
 "PP"+print( symbolrefdecodenew << addresses)}
 let z2=for acc=empty:set.symbol , sym /in toseq.z do 
   if isrecordconstant.sym then acc else acc+sym /for(acc)
let code2 = libcode(prg10,  {roots.oldmods} z2 )
{assert 1=2^5 report "XX"+print.toseq(z \ symsforlib)}
let newmap2 = symbolrefdecodenew
let prg11= for acc=empty:seq.symdef,  sym /in newmap2 do
    if isGlobal.sym then  
    acc+symdef(sym,empty:seq.symbol,0) else acc /for(acc)
for code3 = empty:seq.seq.symbolref, sd ∈ toseq( prg10 /cup asset.prg11 ) do
 if isabstract.module.sym.sd ∨ {isempty.code.sd 
 ∨} not.isrecordconstant.sym.sd ∧ isconstantorspecial.sym.sd
 ∨  sym.sd ∉ maybereferenced0 then
  code3
 else
  for acc = [symbolrefnew.sym.sd], sym ∈ code.sd do
   if isFref.sym then acc + symbolref.-toint.symbolrefnew.basesym.sym else acc + symbolrefnew.sym
  /for(code3 + acc)
/for(let finaldecode = symbolrefdecodenew
{assert cardinality.asset.symbolrefdecodenew = length.symbolrefdecodenew report "KLJDSF"+%.cardinality.asset.symbolrefdecodenew
 +%.length.symbolrefdecodenew
 +for acc=empty:set.symbol,txt="", sym /in symbolrefdecodenew do
    if sym /in acc then next(acc,txt+print.sym) else next( acc+sym,txt) /for(txt)}
codegen(libname
, typedict
, newmods
, libextnames
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

function libcode(prg:set.symdef, symstoexport2:set.symbol)seq.seq.symbolref
for acc = empty:seq.seq.symbolref, sym ∈ toseq.symstoexport2 do
 acc
 + for acc2 = [symbolrefnew.sym], sym2 ∈ libsymcode(prg,sym,symstoexport2) do
  if isFref.sym2 then acc2 + symbolrefnew.PreFref + symbolrefnew.basesym.sym2
  else acc2 + symbolrefnew.sym2
 /for(acc2)
/for(acc)

function libsymcode(prg:set.symdef, sym:symbol, toexport:set.symbol)seq.symbol
  let code1=getCode(prg,sym)
 if isabstract.module.sym then code1
 else 
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