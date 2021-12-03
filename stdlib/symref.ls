#!/bin/sh tau   stdlib stdlib

Module symref

use libraryModule

use standard

use symbol

use encoding.symbol

use seq.symbol

use typedict

use seq.symbolref

use set.symbol

Export compileinfo(typedict, seq.seq.symbolref, seq.seq.word, seq.symbol, seq.libraryModule)
compileinfo

use seq.encodingpair.symbol

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

Function assignencoding(a:symbol)int nextencoding.a

Function decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s)

Function symbolrefdecode seq.symbol
for acc = empty:seq.symbol, p ∈ encoding:seq.encodingpair.symbol do acc + data.p /for(acc) 


Export type:compileinfo

type compileinfo is typedict:typedict
, code:seq.seq.symbolref
, src:seq.seq.word
, symbolrefdecode:seq.symbol
, mods:seq.libraryModule
 
Function roots(s:compileinfo)set.symbol
let exports=for  exports=empty:seq.symbolref , m /in mods.s do exports+exports.m /for(exports)
for acc = empty:set.symbol, r ∈ exports do acc + (symbolrefdecode.s)_(toint.r)/for(acc)

Export code(compileinfo)seq.seq.symbolref

Export mods(compileinfo)seq.libraryModule

Export typedict(compileinfo)typedict

Export symbolrefdecode(compileinfo)seq.symbol

Export src(compileinfo)seq.seq.word

type symbolnew is tosymbol:symbol

Function symbolrefnew(sym:symbol)symbolref symbolref.valueofencoding.encode.symbolnew.sym

Function symbolrefdecodenew seq.symbol
for acc = empty:seq.symbol, p ∈ encoding:seq.encodingpair.symbolnew do acc + tosymbol.data.p /for(acc) 

function hash(a:symbolnew) int hash(tosymbol.a)

function =(a:symbolnew,b:symbolnew) boolean tosymbol.a=tosymbol.b

function assignencoding(a:symbolnew) int nextencoding.a

use encoding.symbolnew

use seq.encodingpair.symbolnew
