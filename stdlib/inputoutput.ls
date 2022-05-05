Module inputoutput

use UTF8

use bits

use bitstream

use libraryModule

use standard

use symbol2

use symbol

use tausupport

use otherseq.addrsym

use seq.addrsym

use seq.bit

use seq.bits

use seq.byte

use otherseq.char

use process.int

use seq.int

use seq.liblib

use otherseq.symbol

use seq.symbol

use process.seq.bit

use process.seq.byte

use process.seq.int

Export type:cstr

Function tocstr(s:seq.word)cstr
let t = for acc = emptyUTF8, w ∈ s do acc + decodeword.w /for(toseqbyte.acc)
cstr.packed.bits.for acc = empty:bitstream, @e ∈ t + tobyte.0 do add(acc, bits.toint.@e, 8)/for(acc)

type cstr is dummy:seq.bits

Builtin getfile2(cstr)process.seq.int{OPTION STATE}

Builtin getbytefile2(cstr)process.seq.byte{OPTION STATE}

Builtin getbitfile2(cstr)process.seq.bit{OPTION STATE}

Function getfile:byte(name:seq.word)seq.byte
let a = getbytefile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.byte)

Function getfile:bit(name:seq.word)seq.bit
let a = getbitfile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.bit)

Builtin createfile3(a:seq.seq.byte,name:cstr) int 

use seq.seq.byte

Function createfile(name:seq.word, a:seq.byte)int
createfile3(
  packed.toseqseqbyte.for acc = empty:bitstream, @e ∈ a do add(acc, bits.toint.@e, 8)/for(acc)
, tocstr.name )

Function createfile(name:seq.word, a:seq.bits)int 
createfile3( packed.toseqseqbyte.tobitstream.a, tocstr.name)

use bitcast.seq.byte

use bitcast.seq.bits

type addrsym is addr:int, sym:symbol

function ?(a:addrsym, b:addrsym)ordering addr.a ? addr.b


Function stacktraceimp seq.word
let t = 
 for acc = empty:seq.addrsym, ll ∈ loadedLibs do
  for t = acc, idx = 1, i ∈ symboladdress.ll do next(t + addrsym(i, (libinfo.ll)_(symbolref.idx)), idx + 1)/for(t)
 /for(sort.acc)
for txt = " /p", r ∈ callstack.30 << 2 do
 let i = binarysearch(t, addrsym(r, Lit.1))
 txt + %.r
 + if between(-i - 1, 1, length.t)then print.sym.t_(-i - 1)else""/if
 + " /br"
/for(txt)

builtin callstack(n:int)seq.int

Builtin loadedLibs seq.liblib

Function funcaddress(sym:symbol)int
let addrs = symboladdress.first.loadedLibs
let i = findindex(sym, subseq(symbolrefdecode.libinfo.first.loadedLibs, 1, length.addrs))
if i ≤ length.addrs then addrs_i else 0

Export createthread(adcret:int, adc:int, funcaddress:int, args:seq.int, argcode:int)process.int 

use set.symdef

use seq.symbol

use typedict


Function externnames(dependentlibs:seq.word)set.symdef
for org = empty:set.symdef, ll ∈ loadedLibs do
 if(libname.ll)_1 ∉ dependentlibs then org
 else
  for acc = org, idx = 1, sym ∈ decoderef.ll do
   if isconstantorspecial.sym ∨ isabstract.module.sym ∨ not.isempty.getCode(org, sym)then
    next(acc, idx + 1)
   else next(symdef(sym, [Word.merge(libname.ll + "$$" + toword.idx)],0) ∪ acc, idx + 1)
  /for(acc)
/for(org)

function buildargcode(sym:symbol, typedict:typedict)int
{needed because the call interface implementation for reals is different than other types is some implementations}
for acc = 1, typ ∈ paratypes.sym + resulttype.sym do acc * 2 + if basetype(typ, typedict) = typereal then 1 else 0 /for(acc)

use seq.mytype

Function callfunc(ctsym:symbol,typedict:typedict,stk:seq.int) seq.int
let t = funcaddress(ctsym)
if t = 0 then empty:seq.int
else let adcret = funcaddress(deepcopySym.resulttype.ctsym)
 let adc = funcaddress(deepcopySym.seqof.typeword)
 let p = createthread(adcret, adc, t, stk, buildargcode(ctsym, typedict))
 assert not.aborted.p report message.p
  [ result.p ]
  
use encoding.seq.char

use words

Function dependentinfo(dependentlibs:seq.word)midpoint
for org = empty:midpoint, ll ∈ loadedLibs do
 let libname = (libname.ll)_1
 if libname ∈ dependentlibs then tomidpoint(org, libinfo.ll, libname)else org
/for(org)   
  
Function addlibwords(l:liblib)int
let discard = addencodingpairs.words.l
1