#!/bin/sh tau   stdlib stdlib

Module symref

use libraryModule

use standard

use symbol

use typedict

use encoding.symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use seq.symbolref

use seq.encodingpair.symbol

use otherseq.seq.symbol

use set.seq.symbol

use otherseq.seq.symbolref

use seq.seq.symbolref

Function compileinfo(t:typedict, code:seq.seq.symbolref, src:seq.seq.word, d:seq.symbol,m: seq.libraryModule)compileinfo
         compileinfo( d, m,code,src,t)

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

Function assignencoding(a:symbol)int nextencoding.a

Function decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s)

Function symbolrefdecode seq.symbol
for acc = empty:seq.symbol, p ∈ encoding:seq.encodingpair.symbol do acc + data.p /for(acc) 

Export type:compileinfo

type compileinfo is  symbolrefdecode:seq.symbol
, mods:seq.libraryModule
, code:seq.seq.symbolref
, src:seq.seq.word
 ,typedict:typedict



 

Function roots(s:compileinfo)set.symbol
let exports = 
 for exports = empty:seq.symbolref, m ∈ mods.s do exports + exports.m /for(exports)
for acc = empty:set.symbol, r ∈ exports do acc + s_r /for(acc)

Export code(compileinfo)seq.seq.symbolref

Export mods(compileinfo)seq.libraryModule

Export typedict(compileinfo)typedict

Export symbolrefdecode(compileinfo)seq.symbol

Export src(compileinfo)seq.seq.word

Function profiledata(info:compileinfo)seq.int
  let l=first.code.info << 3
for acc = [1, length.l / 2], first = true, r ∈ l do
 if first then next(acc + toint.r, false)else next(acc + toint.r + [0, 0, 0, 0], true)
  /for( acc  )
  
Function profilearcs(info:compileinfo) set.seq.symbol
    let l=first.code.info << 3
for acc = empty:set.seq.symbol, first = true, last = Lit.0, r ∈ l do
 let sym =  info_r 
 if first then next(acc, false, sym)else next(acc + [last, sym], true, sym)
  /for( acc)

Function newmaplength(info:compileinfo)int toint.(first.code.info)_2

Function libcodelength(info:compileinfo)int toint.(first.code.info)_3

Function libcode(info:compileinfo)seq.seq.symbolref subseq(code.info, 2, libcodelength.info + 1)

Function prgcode(info:compileinfo)seq.seq.symbolref subseq(code.info, libcodelength.info + 2, length.code.info) 

Function   _(info:compileinfo,r:symbolref) symbol
 let i=toint.r
 if i > 0 then  (symbolrefdecode.info)_i  else Fref.(symbolrefdecode.info)_-i
 