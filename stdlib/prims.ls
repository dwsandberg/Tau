Module prims

use seq.bits

use bits

use fileio

use encoding.seq.int

use seq.encodingrep.seq.int

use stdlib

use seq.seq.word

function assignencoding(l:int, a:seq.int) int assignrandom(l,a)


Function execute(name:word)seq.word executecode(toCformat.[ name], empty:seq.int)

type argblock3 is record a:int, length:int, arg1:seq.word, arg2:word, arg3:word

type argblock4 is record a:int, length:int, state:seq.word, arg:seq.word, arg2:seq.word, b:seq.seq.word

function cvt(a:argblock3)seq.int builtin."PARAM 1"

function cvt(a:argblock4)seq.int builtin."PARAM 1"

Function execute(name:word, arg1:seq.word, arg2:word, arg3:word)seq.word
 executecode(toCformat.[ name], cvt.argblock3(0, 3, arg1, arg2, arg3))

Function execute(name:word, state:seq.word, arg:seq.word, arg2:seq.word, b:seq.seq.word)seq.word
 executecode(toCformat.[ name], cvt.argblock4(0, 4, state, arg, arg2, b))

Function unloadlib(a:seq.word)int unloadlib.toCformat.a

function unloadlib(seq.bits)int builtin.usemangle

Function loadlibrary(a:word)int loadlib.toCformat.[ a]

Function loadlib(seq.bits)int builtin.usemangle

Function executecode(seq.bits, para:seq.int)seq.word builtin.usemangle

Function add2(h:encodingstate.seq.int, v:seq.encodingrep.seq.int)encodingstate.seq.int // so add is included in stdlib // add(h, v)