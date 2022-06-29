Module debuginfo

use encoding.seq.char

use seq.seq.char

use standard

use symbol

use seq.symbol

use words

type parc is caller:int, callee:int, counts:int, clocks:int, space:int, unused:int

Export type:parc

Function =(a:parc, b:parc)boolean callee.a = callee.b ∧ caller.a = caller.b

Export caller(parc)int

Export callee(parc)int

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

___________________________

Export type:debuginfo

type debuginfo is libname:seq.word
, words:seq.seq.char
, entrypointaddress:int
, symboladdress:seq.int
, profiledata:seq.parc
, symbolrefdecodeX:seq.symbol


Function dependentwords(dependentlibs:seq.word)seq.seq.char
if isempty.dependentlibs then empty:seq.seq.char
else for acc = empty:seq.seq.char, ll ∈ loadedLibs do acc + words.ll /for(acc)

Builtin loadedLibs seq.debuginfo

Function symboladdress seq.int for acc = empty:seq.int, ll ∈ loadedLibs do acc + symboladdress.ll /for(acc)

Function symbolrefdecodeX seq.symbol
for acc = empty:seq.symbol, ll ∈ loadedLibs do acc + symbolrefdecodeX.ll /for(acc)

Export symbolrefdecodeX(debuginfo)seq.symbol

Export words(debuginfo)seq.seq.char

Export profiledata(debuginfo)seq.parc

Function addlibwords(l:debuginfo)int
let discard = addencodings.words.l
1 