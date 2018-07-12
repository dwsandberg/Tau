Module prims

use fileio

use stdlib

use seq.word

use seq.seq.word

Function execute(name:word)seq.word executecode(toCformat.[ name], empty:seq.int)

type argblock3 is record a:int, length:int, arg1:seq.word, arg2:word, arg3:word

type argblock4 is record a:int, length:int, state:seq.word, arg:seq.word, arg2:seq.word, b:seq.seq.word

function cvt(a:argblock3)seq.int builtin.NOOP

function cvt(a:argblock4)seq.int builtin.NOOP

Function execute(name:word, arg1:seq.word, arg2:word, arg3:word)seq.word 
 executecode(toCformat.[ name], cvt.argblock3(0, 3, arg1, arg2, arg3))

Function execute(name:word, state:seq.word, arg:seq.word, arg2:seq.word, b:seq.seq.word)seq.word 
 executecode(toCformat.[ name], cvt.argblock4(0, 4, state, arg, arg2, b))

Function unloadlib(a:seq.word)int unloadlib.toCformat.a

function unloadlib(seq.bits)int builtin.usemangle

Function loadlib(a:seq.word, timestamp:int)int loadlib.toCformat.a

function loadlib(seq.bits)int builtin.usemangle

function executecode(seq.bits, para:seq.int)seq.word builtin.usemangle

