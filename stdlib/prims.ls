Module prims

use UTF8

use blockseq.int

use fileresult

use internals.int

use seq.liblib

use seq.libsym

use seq.mytype

use seq.seq.int

use stdlib

Function execute(name:word)seq.word executecode(toCformat.toUTF8.[ name], empty:seq.int)

type argblock3 is record a:int, length:int, arg1:seq.word, arg2:word, arg3:word

type argblock4 is record a:int, length:int, state:seq.word, arg:seq.word, arg2:seq.word, b:seq.seq.word

function cvt(a:argblock3)seq.int builtin

function cvt(a:argblock4)seq.int builtin

Function toCformat(a:UTF8)UTF8 UTF8.packedbyte(toseqint.a + [ 0])

Function execute(name:word, arg1:seq.word, arg2:word, arg3:word)seq.word 
 executecode(toCformat.toUTF8.[ name], cvt.argblock3(0, 3, arg1, arg2, arg3))

Function execute(name:word, state:seq.word, arg:seq.word, arg2:seq.word, b:seq.seq.word)seq.word 
 executecode(toCformat.toUTF8.[ name], cvt.argblock4(0, 4, state, arg, arg2, b))

function addsuffix(suffix:seq.word, a:word)seq.word [ a]+ suffix

Function createlib(b:seq.int, libname:word, dependlibs:seq.word)int 
 let z2 = createbytefile([ libname]+".bc", b)
  createlib3(toCformat.toUTF8.[ libname], toCformat.toUTF8.@(+, addsuffix.".dylib","", dependlibs))

function createlib3(name:UTF8, libs:UTF8)int builtin.createlib3ZbuiltinZUTF8ZUTF8

Function unloadlib(a:seq.word)int unloadlib.toCformat.toUTF8.a

function unloadlib(UTF8)int builtin.usemangle

Function loadlib(a:seq.word, timestamp:int)int loadlib.toCformat.toUTF8.a

function loadlib(UTF8)int builtin.usemangle

function executecode(UTF8, para:seq.int)seq.word builtin.usemangle

type fileresult is record size:int, word1:int, word2:int, data:seq.int

Function getfile(f:UTF8)fileresult builtin.usemangle.STATE

Function getfile(f:seq.word)seq.int 
 // as file byte // 
  let file = getfile.toCformat.UTF8.@(+, decode, empty:seq.int, f)
  assert size.file > -1 report"Error opening file"+ f 
  if size.file ≤ 16 
  then smallbyteseq(size.file, word1.file, word2.file, 1)
  else let discard = setfld3(address.data.file, 1, 0)
  let discard2 = setfld3(address.data.file, size.file - 16, 1)
  smallbyteseq(16, word1.file, word2.file, 1)+ data.file

Function fileexists(f:seq.word)boolean 
 let file = getfile.toCformat.UTF8.@(+, decode, empty:seq.int, f)
  size.file > -1

Function readfile(f:seq.word)seq.int 
 // as file of 64 bit integers // 
  let file = getfile.toCformat.UTF8.@(+, decode, empty:seq.int, f)
  assert size.file > -1 report"Error opening file"+ f 
  // assert size.file / 8 = length.data.file:"JJJ"+ toword.size.file + toword.length.data.file // 
   [ word1.file, word2.file]+ data.file

