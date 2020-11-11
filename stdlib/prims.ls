Module prims

use seq.bits

use bits

use fileio

use encoding.seq.int

use stdlib

use seq.seq.word

function assignencoding(l:int, a:seq.int) int assignrandom(l,a)


Function execute(name:word)seq.word executecode(toCformat.[ name], empty:seq.int)


Function unloadlib(a:seq.word)int unloadlib.toCformat.a

builtin unloadlib(seq.bits)int  

Function loadlibrary(a:word)int loadlib.toCformat.[ a]

Builtin loadlib(seq.bits)int  

Builtin executecode(seq.bits, para:seq.int)seq.word  

