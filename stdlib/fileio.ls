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

Function tocstr(s:seq.word) cstr tocstr.packed
 .data2((toseqint.toUTF8.s + 0) @ add(bitpackedseq(0, empty:seq.byte, bits.0), byte.@e)) 

Export type:cstr

Function   createfile( name:seq.word,  a:bitpackedseq.byte) int
createfile2(length.a,packed.data2.a, tocstr.name)

Function createbytefile(name:seq.word, a:seq.int)int 
let t= packed.data2(a @ add(empty:bitpackedseq.byte, byte.@e))
    createfile2(length.a,t , tocstr.name)

Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int
  createlib2(tocstr.[ libname], tocstr(dependlibs @ +("", [@e]+".dylib" ))
,  length.b * 8, packed.b)  

builtin createlib2(name:cstr, libs:cstr, length:int,data:seq.bits)int

Function createfile(name:seq.word, a:seq.int)int
   createfile2(length.a * 8 ,packed.a @ +(empty:seq.bits, bits.@e), tocstr.name)

type fileresult is record size:int, start:seq.int, data:seq.int 

type fileresultbit is record size:int, start:seq.bit, data:seq.bit 

type fileresultbyte is record size:int, start:seq.byte, data:seq.byte


builtin getfile(name:cstr)fileresult

builtin getbytefile(cstr) fileresultbyte

builtin getbitfile(cstr)  fileresultbit


Function getfile:int(name:seq.word) seq.int  
let file = getfile.tocstr.name
start.file  + data.file

Function getfile:byte(name:seq.word) seq.byte
 let file = getbytefile.tocstr.name
  assert size.file > -1 report"Error opening file" + name
      start.file  + data.file 


Function getfile:bit(name:seq.word)  seq.bit
let file = getbitfile.tocstr.name
  assert size.file > -1 report"Error opening file" + name
      start.file  + data.file 



function getfile2(name:seq.word)seq.int
 // as file byte //
 let file = getfile.tocstr.name
  assert size.file > -1 report"Error opening file" + name
   tointseq.bitpackedseq2(size.file, tobitpackedseq(  start.file  + data.file), bits.0)


Function fileexists(name:seq.word)boolean
 let file = getfile.tocstr.name
  size.file > -1

Function gettext(filename:seq.word)seq.seq.word breakparagraph.getUTF8file.filename  

Function createfile(filename:seq.word, s:seq.seq.word)int
 createbytefile(filename, s @ +(empty:seq.int, toseqint.toUTF8.@e + [ 10, 10]))

Function createfile(filename:seq.word, s:seq.word)int createbytefile(filename, toseqint.toUTF8.s)


Function getUTF8file(filename:seq.word)UTF8 UTF8.getfile2.filename

function tobitpackedseq(s:seq.int)seq.byte s @ +(empty:seq.byte, byte.@e)

function tobitpackedseqbit(s:seq.int)seq.bit s @ +(empty:seq.bit, bit.@e)

function tointseq(s:seq.byte)seq.int s @ +(empty:seq.int, toint.@e)


builtin tocstr(seq.bits) cstr

type cstr is record dummy:int

builtin createfile2(byteLength:int,data:seq.bits,cstr) int  

