Module fileio

use UTF8

use bitpackedseq.bit

use bitpackedseq.byte

use bits

use blockseq.bits

use blockseq.int

use seq.bit

use seq.bits

use seq.byte


use seq.seq.bits

use seq.seq.int

use stdlib

use textio

use seq.UTF8

use bits

Function type:outputformat internaltype export

Function type:fileresult internaltype export


Function toCformat(s:seq.word)seq.bits 
 packed.data2.add(@(add, byte, bitpackedseq(0, empty:seq.byte, bits.0), toseqint.toUTF8.s), byte.0)

type outputformat is record length:int, data:seq.bits

Function outputformat(a:seq.int)outputformat 
 outputformat(length.a, blockit.data2.@(add, byte, empty:bitpackedseq.byte, a))

Function createbytefile(name:seq.word, a:seq.int)int createfile(toCformat.name, outputformat.a)

Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int 
 createlib(toCformat.[ libname], toCformat.@(+, addsuffix.".dylib","", dependlibs), outputformat(length.b * 8, blockit.b))

function addsuffix(suffix:seq.word, a:word)seq.word [ a]+ suffix

function createlib(name:seq.bits, libs:seq.bits, t:outputformat)int builtin.usemangle

function createfile(name:seq.bits, data:outputformat)int builtin.usemangle

Function createfile(name:seq.word, a:seq.int)int createfile(toCformat.name, blockit.a)

function createfile(name:seq.bits, data:seq.int)int builtin.usemangle

function getfile(f:seq.bits)fileresult builtin.STATE.usemangle

function size(fileresult)int export

function word1(fileresult)int export

function word2(fileresult)int export

function data(fileresult)seq.int export

Function getfile2(name:seq.word)fileresult getfile.toCformat.name

type fileresult is record size:int, word1:int, word2:int, data:seq.int

Function getfile(name:seq.word)seq.int 
 // as file byte // 
  let file = getfile.toCformat.name 
  assert size.file >-1 report"Error opening file"+ name 
  tointseq.toseq.bitpackedseq(size.file, tobitpackedseq([ word1.file, word2.file]+ data.file), bits.0)

Function getbitfile(name:seq.word)seq.bit 
 let file = getfile.toCformat.name 
  assert size.file >-1 report"Error opening file"+ name 
  toseq.bitpackedseq(size.file * 8, tobitpackedseqbit([ word1.file, word2.file]+ data.file), bits.0)

Function fileexists(f:seq.word)boolean 
 let file = getfile.toCformat.f 
  size.file >-1

Function gettext(filename:seq.word)seq.seq.word 
 @(+, towords, empty:seq.seq.word, breakparagraph.getUTF8file.filename)
 
 Function createfile(filename:seq.word, s:seq.seq.word)int 
 createbytefile(filename, @(+, toUTF8plus, empty:seq.int, s))

 
 
Function getUTF8file(filename:seq.word) UTF8  UTF8(getfile.filename)

function tobitpackedseq(s:seq.int)seq.byte @(+, byte, empty:seq.byte, s)

function tobitpackedseqbit(s:seq.int)seq.bit @(+, bit, empty:seq.bit, s)

function tointseq(s:seq.byte)seq.int @(+, toint, empty:seq.int, s)


Blockit is exported so other deepcopy functions will compile

