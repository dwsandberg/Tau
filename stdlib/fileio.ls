Module fileio

use seq.UTF8

use UTF8

use seq.bit

use seq.bits

use bits
 
use seq.byte

use seq.int

use standard

use textio

use bitstream

Export type:cstr

Function tocstr(s:seq.word) cstr 
tocstr.packed.bits((toseqbyte.toUTF8.s + tobyte.0) @ add(empty:bitstream,bits.toint.@e,8))

    

type fileresult is record size:int, start:seq.int, data:seq.int 

type fileresultbit is record size:int, start:seq.bit, data:seq.bit 

type fileresultbyte is record size:int, start:seq.byte, data:seq.byte

type cstr is record dummy:int

builtin createlib2(name:cstr, libs:cstr, length:int,data:seq.bits)int

builtin getfile(name:cstr)fileresult

builtin getbytefile(cstr) fileresultbyte

builtin getbitfile(cstr)  fileresultbit

builtin tocstr(seq.bits) cstr

builtin createfile(byteLength:int,data:seq.bits,cstr) int 

function createfile3(byteLength:int,data:seq.bits,name:cstr) int createfile(byteLength,data,name )


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


Function fileexists(name:seq.word)boolean
 let file = getbitfile.tocstr.name
  size.file > -1

Function gettext(filename:seq.word)seq.seq.word breakparagraph.UTF8.getfile:byte(filename)  


Function getfileaslines(filename:seq.word) seq.UTF8  breaklines.UTF8.getfile:byte(filename)

Function createfile(filename:seq.word, s:seq.seq.word)int
 createfile(filename, s @ +(empty:seq.byte, toseqbyte.toUTF8.@e + [ tobyte.10, tobyte.10]))

Function createfile(filename:seq.word, s:seq.word)int createfile(filename, toseqbyte.toUTF8.s)

Function createfile(name:seq.word, a:seq.byte)int 
  createfile3(length.a,packed.bits(a @ add(empty:bitstream,bits.toint.@e,8)) , tocstr.name)


Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int
  createlib2(tocstr.[ libname], tocstr(dependlibs @ +("", [@e]+".dylib" ))
,  length.b * 8, packed.b)  

Function createfile(name:seq.word, a:seq.int)int
   createfile3(length.a * 8 ,packed.a @ +(empty:seq.bits, bits.@e), tocstr.name)


