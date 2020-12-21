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

use standard

use textio

Export_(a:bitpackedseq.byte, idx:int)byte


Export type:fileresult

Function toCformat(s:seq.word)seq.bits
 packed
 .data2
 .add(toseqint.toUTF8.s @ add(bitpackedseq(0, empty:seq.byte, bits.0), byte.@e), byte.0)


Function   createfile( name:seq.word,  a:bitpackedseq.byte) int
createfile2(length.a,packed.data2.a, tocstr.toCformat.name)

Function createbytefile(name:seq.word, a:seq.int)int 
let t= packed.data2(a @ add(empty:bitpackedseq.byte, byte.@e))
    createfile2(length.a,t , tocstr.toCformat.name)

Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int
  createlib2(tocstr.toCformat.[ libname], tocstr.toCformat(dependlibs @ +("", [@e]+".dylib" ))
,  length.b * 8, packed.b)  

builtin createlib2(name:cstr, libs:cstr, length:int,data:seq.bits)int

Function createfile(name:seq.word, a:seq.int)int
   createfile2(length.a * 8 ,packed.a @ +(empty:seq.bits, bits.@e), tocstr.toCformat.name)


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
   tointseq.bitpackedseq2(size.file, tobitpackedseq([ word1.file, word2.file] + data.file), bits.0)

Function getbitfile(name:seq.word)seq.bit
 let file = getfile.toCformat.name
  assert size.file > -1 report"Error opening file" + name
    bitpackedseq2(size.file * 8, tobitpackedseqbit([ word1.file, word2.file] + data.file), bits.0)

Function fileexists(f:seq.word)boolean
 let file = getfile.toCformat.f
  size.file > -1

Function gettext(filename:seq.word)seq.seq.word breakparagraph.getUTF8file.filename  

Function createfile(filename:seq.word, s:seq.seq.word)int
 createbytefile(filename, s @ +(empty:seq.int, toseqint.toUTF8.@e + [ 10, 10]))

Function createfile(filename:seq.word, s:seq.word)int createbytefile(filename, toseqint.toUTF8.s)


Function getUTF8file(filename:seq.word)UTF8 UTF8.getfile.filename

function tobitpackedseq(s:seq.int)seq.byte s @ +(empty:seq.byte, byte.@e)

function tobitpackedseqbit(s:seq.int)seq.bit s @ +(empty:seq.bit, bit.@e)

function tointseq(s:seq.byte)seq.int s @ +(empty:seq.int, toint.@e)


builtin tocstr(seq.bits) cstr

type cstr is record dummy:int

builtin createfile2(byteLength:int,data:seq.bits,cstr) int  

