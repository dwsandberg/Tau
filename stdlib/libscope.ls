
Module libscope

use mytype

use encoding.seq.char

use seq.encodingrep.seq.char

use seq.liblib

use seq.libmod



use seq.mytype

use stdlib

use seq.seq.word

use seq.word



Function type:liblib internaltype export


Function type:libmod internaltype export



type liblib is record libname:seq.word, words:seq.encodingrep.seq.char, mods:seq.libmod, timestamp:int, readonly:boolean

Function liblib(a:seq.word, d:seq.libmod)liblib liblib(a, empty:seq.encodingrep.seq.char, d, 0, false)

Function timestamp(liblib)int export

Function libname(liblib)seq.word export

Function mods(liblib)seq.libmod export

Function words(liblib)seq.encodingrep.seq.char export

Function readonly(liblib)boolean export


use otherseq.word


function =(a:libmod, b:libmod)boolean modname.a = modname.b

Function uses(libmod)seq.mytype export

Function loadedlibs seq.liblib builtin.usemangle


type libmod is record parameterized:boolean, modnamex:word, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype

Function libmod(parameterized:boolean, modname:word, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype)libmod export

Function libmod(modname:mytype, defines:seq.symbol, exports:seq.symbol, uses:seq.mytype)libmod 
 libmod(isabstract.modname,abstracttype.modname,defines,exports,uses)
 
Function modname(l:libmod)mytype  mytype.if parameterized.l then  "T"+modnamex.l else [modnamex.l]


Function defines(l:libmod)seq.symbol export

Function exports(l:libmod)seq.symbol export


use bits


type symbol is record  fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol,extrabits:bits

use seq.symbol

Function symbol(fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol) symbol 
symbol(fsig,module,returntype,zcode,bits.0)

function symbol(fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol,extrabits:bits) symbol 
export

Function fsig(symbol)seq.word export

Function module(symbol)seq.word export

Function returntype(symbol)seq.word export

Function type:symbol internaltype export

Function zcode(symbol)seq.symbol export

Function extrabits(symbol)bits export

type myinternaltype is record size:int,kind:word,name:word,modname:mytype,subflds:seq.mytype

function myinternaltype(size:int,kind:word,name:word,modname:mytype,subflds:seq.mytype) myinternaltype
export

Function type:myinternaltype internaltype export

Function size(myinternaltype)int export

Function kind(myinternaltype)word export

Function name(myinternaltype)word export

Function modname(myinternaltype)mytype export

Function subflds(myinternaltype)seq.mytype export

use seq.myinternaltype



Function type:firstpass internaltype export

type firstpass is record modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, 
unbound:set.symbol,types:seq.myinternaltype

Function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, 
unboundx:set.symbol,types:seq.myinternaltype) firstpass
 export
 

Function exportmodule(firstpass)boolean false

Function modname(firstpass)mytype export

Function defines(firstpass)set.symbol export

Function exports(firstpass)set.symbol export

Function uses(firstpass)seq.mytype export

Function unboundexports(firstpass)seq.symbol export

Function unbound(firstpass)set.symbol export

Function types(firstpass) seq.myinternaltype export



