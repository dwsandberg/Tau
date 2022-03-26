Module libraryModule

use bits

use standard

use symbol

use typedict

use seq.bits

use seq.char

use seq.libraryModule

use encoding.symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use seq.symbolref

use encoding.seq.char

use seq.seq.mytype

use seq.encodingpair.symbol

use otherseq.seq.symbol

use set.seq.symbol

use otherseq.seq.symbolref

use seq.seq.symbolref

use seq.seq.word

use seq.encodingpair.seq.char

type symbolref is toint:int

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function ?(a:symbolref, b:symbolref)ordering toint.a ? toint.b

type libraryModule is modname:modref, exports:seq.symbolref, types:seq.seq.mytype

Export libraryModule(modname:modref, exports:seq.symbolref, types:seq.seq.mytype)libraryModule

Export type:libraryModule

Export exports(libraryModule)seq.symbolref

Export modname(libraryModule)modref

Export types(libraryModule)seq.seq.mytype

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
, timestamp:int
, profiledata:seq.parc
, libinfo:compileinfo
, symboladdress:seq.int


Export symboladdress(liblib)seq.int

Export entrypointaddress(liblib)int

Export libinfo(liblib)compileinfo

Function code(l:liblib)seq.seq.symbolref code.libinfo.l

Export timestamp(liblib)int

Function decoderef(l:liblib)seq.symbol symbolrefdecode.libinfo.l

Export libname(liblib)seq.word

Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

_________________

type compileinfo is symbolrefdecode:seq.symbol
, mods:seq.libraryModule
, code:seq.seq.symbolref
, src:seq.seq.word
, typedict:typedict

Function libname(info:compileinfo) word   
extractValue(src.info,"Library")_1

Function extractValue(s:seq.seq.word,name:seq.word) seq.word  
 if first.first.s /in "Library" then
   for value="",p /in  break(s_1, "uses exports", true) do
    if p_1 /in name then  p << 1 else value
 /for(value)
else 
  for value="",last="="_1,p /in  break(first.s, "=", false) do
  next(  if last /in name then p else value ,last)
  /for( if value = p then value else value >> 1 )
  
Export type:compileinfo

Export code(compileinfo)seq.seq.symbolref

Export mods(compileinfo)seq.libraryModule

Export typedict(compileinfo)typedict

Export symbolrefdecode(compileinfo)seq.symbol

Export src(compileinfo)seq.seq.word

Function compileinfo(t:typedict, code:seq.seq.symbolref, src:seq.seq.word, d:seq.symbol, m:seq.libraryModule)compileinfo
compileinfo(d, m, code, src, t)

Function profiledata(info:compileinfo)seq.int
let l = first.code.info << 4
for acc = [1, length.l / 2], first = true, r ∈ l do
 if first then next(acc + toint.r, false)else next(acc + toint.r + [0, 0, 0, 0], true)
/for(acc)

Function profilearcs(info:compileinfo)set.seq.symbol
let l = first.code.info << 4
for acc = empty:set.seq.symbol, first = true, last = Lit.0, r ∈ l do
 let sym = info_r
 if first then next(acc, false, sym)else next(acc + [last, sym], true, sym)
/for(acc)

Function newmaplength(info:compileinfo)int toint.(first.code.info)_2

Function libcodelength(info:compileinfo)int toint.(first.code.info)_3

Function addresslength(info:compileinfo)int toint.(first.code.info)_4

Function libcode(info:compileinfo)seq.seq.symbolref subseq(code.info, 2, libcodelength.info + 1)

Function prgcode(info:compileinfo)seq.seq.symbolref subseq(code.info, libcodelength.info + 2, length.code.info)

Function _(info:compileinfo, r:symbolref)symbol
let i = toint.r
if i > 0 then(symbolrefdecode.info)_i else Fref.(symbolrefdecode.info)_(-i)

Function roots(s:compileinfo)set.symbol
let exports = 
 for exports = empty:seq.symbolref, m ∈ mods.s do exports + exports.m /for(exports)
for acc = empty:set.symbol, r ∈ exports do acc + s_r /for(acc)

Function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

Function assignencoding(a:symbol)int nextencoding.a

Function decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s)

Function symbolrefdecode seq.symbol
for acc = empty:seq.symbol, p ∈ encoding:seq.encodingpair.symbol do acc + data.p /for(acc) 