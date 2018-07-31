Module fileio

use UTF8

use bitpackedseq.bit

use bitpackedseq.byte

use bits

use blockseq.bits

use blockseq.int

use packedseq.bits

use packedseq.seq.bits

use packedseq.int

use seq.seq.int

use packedseq.seq.int

use seq.bit

use seq.bits

use seq.seq.bits 

use seq.byte

use seq.int

use stdlib

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

function getfile(f:seq.bits)fileresult builtin.STATE.usemangle

type fileresult is record size:int, word1:int, word2:int, data:seq.int

Function getfile(name:seq.word)seq.int 
 // as file byte // 
  let file = getfile.toCformat.name 
  assert size.file > -1 report"Error opening file"+ name 
  tointseq.toseq.bitpackedseq(size.file, tobitpackedseq([ word1.file, word2.file]+ data.file), bits.0)

Function getbitfile(name:seq.word)seq.bit 
 let file = getfile.toCformat.name 
  assert size.file > -1 report"Error opening file"+ name 
  toseq.bitpackedseq(size.file * 8, tobitpackedseqbit([ word1.file, word2.file]+ data.file), bits.0)

Function fileexists(f:seq.word)boolean 
 let file = getfile.toCformat.f 
  size.file > -1

type byte is record toint:int

function tobitpackedseq(s:seq.int)seq.byte @(+, byte, empty:seq.byte, s)

function tobitpackedseqbit(s:seq.int)seq.bit @(+, bit, empty:seq.bit, s)

function tointseq(s:seq.byte)seq.int @(+, toint, empty:seq.int, s)

Function sizeinbits(a:byte)int 8

Function tobits(a:byte)bits bits.toint.a

Function frombits(a:bits)byte byte.toint.a

Function blockit(seq.int)seq.int export

Blockit is exported so other deepcopy functions will compile

