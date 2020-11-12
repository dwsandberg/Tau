Module fileio

use seq.UTF8

use UTF8

use bitpackedseq.bit

use seq.bit

use seq.seq.bits

use seq.bits

use bits

use bitpackedseq.byte

use seq.byte

use seq.seq.int

use seq.int

use stdlib

use textio

Export_(a:bitpackedseq.byte, idx:int)byte

Export type:outputformat

Export type:fileresult

Function toCformat(s:seq.word)seq.bits
 packed
 .data2.add(@(add, byte, bitpackedseq(0, empty:seq.byte, bits.0), toseqint.toUTF8.s), byte.0)

type outputformat is record length:int, data:seq.bits

Function outputformat(a:seq.int)outputformat outputformat(length.a, packed.data2.@(add, byte, empty:bitpackedseq.byte, a))

Function createbytefile(name:seq.word, a:seq.int)int createfile(toCformat.name, outputformat.a)

Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int
 createlib(toCformat.[ libname], toCformat.@(+, addsuffix.".dylib","", dependlibs), outputformat(length.b * 8, packed.b))

function addsuffix(suffix:seq.word, a:word)seq.word [ a] + suffix

builtin createlib(name:seq.bits, libs:seq.bits, t:outputformat)int

builtin createfile(name:seq.bits, data:outputformat)int

Function createfile(name:seq.word, a:seq.int)int
 createfile(toCformat.name, outputformat(length.a * 8, @(+, bits, empty:seq.bits, packed.a)))

builtin getfile(f:seq.bits)fileresult

Export size(fileresult)int

Export word1(fileresult)int

Export word2(fileresult)int

Export data(fileresult)seq.int

Function getfile2(name:seq.word)fileresult getfile.toCformat.name

type fileresult is record size:int, word1:int, word2:int, data:seq.int

Function getfile(name:seq.word)seq.int
 // as file byte //
 let file = getfile.toCformat.name
  assert size.file > -1 report"Error opening file" + name
   tointseq.toseq.bitpackedseq(size.file, tobitpackedseq([ word1.file, word2.file] + data.file), bits.0)

Function getbitfile(name:seq.word)seq.bit
 let file = getfile.toCformat.name
  assert size.file > -1 report"Error opening file" + name
   toseq.bitpackedseq(size.file * 8, tobitpackedseqbit([ word1.file, word2.file] + data.file), bits.0)

Function fileexists(f:seq.word)boolean
 let file = getfile.toCformat.f
  size.file > -1

Function gettext(filename:seq.word)seq.seq.word @(+, towords, empty:seq.seq.word, breakparagraph.getUTF8file.filename)

Function createfile(filename:seq.word, s:seq.seq.word)int createbytefile(filename, @(+, toUTF8plus, empty:seq.int, s))

Function createfile(filename:seq.word, s:seq.word)int createbytefile(filename, toseqint.toUTF8.s)

function toUTF8plus(s:seq.word)seq.int toseqint.toUTF8.s + [ 10, 10]

Function getUTF8file(filename:seq.word)UTF8 UTF8.getfile.filename

function tobitpackedseq(s:seq.int)seq.byte @(+, byte, empty:seq.byte, s)

function tobitpackedseqbit(s:seq.int)seq.bit @(+, bit, empty:seq.bit, s)

function tointseq(s:seq.byte)seq.int @(+, toint, empty:seq.int, s)