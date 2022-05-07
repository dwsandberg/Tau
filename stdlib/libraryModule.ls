Module libraryModule

use bits

use standard

use symbol

use symbol2

use seq.bits

use seq.char

use seq.libraryModule

use seq.modExports

use set.modref

use seq.mytype

use set.mytype

use encoding.symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use otherseq.symbolref

use seq.symbolref

use seq.symdef

use set.symdef

use seq.seq.mytype

use otherseq.seq.symbol

use set.seq.symbol

use otherseq.seq.symbolref

use seq.seq.symbolref

use seq.seq.word

use seq.encodingpair.seq.char

Export type:symbolref

Export symbolref(sym:symbol)symbolref symbolref.addorder.sym

Export decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s)

type libraryModule is modname:modref, exports:seq.symbolref, types:seq.seq.mytype

Export libraryModule(modname:modref, exports:seq.symbolref, types:seq.seq.mytype)libraryModule

Export type:libraryModule

Export exports(libraryModule)seq.symbolref

Export modname(libraryModule)modref

Export types(libraryModule)seq.seq.mytype

Function convert(s:seq.modExports)seq.libraryModule
for all = empty:seq.libraryModule, m ∈ s do
 for acc = empty:seq.symbolref, sym ∈ exports.m do acc + symbolref.sym /for(all + libraryModule(modname.m, acc, types.m))
/for(all)

______________________

type parc is caller:symbolref, callee:symbolref, counts:int, clocks:int, space:int, unused:int

Export type:parc

Export parc(caller:symbolref, callee:symbolref, counts:int, clocks:int, space:int, unused:int)parc

Function =(a:parc, b:parc)boolean toint.callee.a = toint.callee.b ∧ toint.caller.a = toint.caller.b

Export caller(parc)symbolref

Export callee(parc)symbolref

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

Export type:liblib

___________________________

type liblib is libname:seq.word
, words:seq.encodingpair.seq.char
, entrypointaddress:int
, unused0:int
, profiledata:seq.parc
, symbolrefdecode:seq.symbol
, mods:seq.libraryModule
, code:seq.seq.symbolref
, unused1:int
, unused2:int
, symboladdress:seq.int


Export symboladdress(liblib)seq.int

Export entrypointaddress(liblib)int

Function decoderef(l:liblib)seq.symbol symbolrefdecode.l

Export libname(liblib)seq.word

Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

_________________

Export symbolrefdecode(liblib)seq.symbol

Function _(info:seq.symbol, r:symbolref)symbol
let i = toint.r
if i > 0 then info_i else Fref.info_(-i)

Function tomidpoint(org:midpoint, libinfo:liblib, libname:word)midpoint
let symdecode = 
 for acc = empty:seq.symbol, sym ∈ symbolrefdecode.libinfo do acc + rehash.sym /for(acc)
let new = 
 for acc = empty:set.symdef, c ∈ code.libinfo do
  if toint.first.c = 0 then acc
  else
   for code = empty:seq.symbol, r ∈ c << 1 do code + symdecode_r /for(acc + symdef(symdecode_(c_1), code, 0))
 /for(acc)
for acc = new, idx = 1, sym ∈ symdecode do
 if isconstantorspecial.sym ∨ isabstract.module.sym ∨ library.module.sym ≠ libname then next(acc, idx + 1)
 else next(symdef(sym, getCode(acc, sym), idx) ∪ acc, idx + 1)
/for(for mods = empty:seq.modExports, m ∈ mods.libinfo do
 mods
 + modExports(modname.m
 , for acc2 = empty:seq.symbol, r ∈ exports.m do acc2 + symdecode_r /for(acc2)
 , types.m
 )
/for(midpoint("", acc ∪ prg.org, emptytypedict, libmods.org + mods, empty:seq.seq.word)))

Function symbolrefdecode seq.symbol for acc = empty:seq.symbol, p ∈ encodingdata:symbol do acc + p /for(acc) 