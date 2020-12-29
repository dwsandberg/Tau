Module fileio

use seq.UTF8

use UTF8

 
use seq.bit

use seq.seq.bits

use seq.bits

use bits

 
use seq.byte

use seq.seq.int

use seq.int

use standard

use textio

 
Function tocstr(s:seq.word) cstr 
tocstr.packed.bits((toseqbyte.toUTF8.s + byte.0) @ add(empty:bitstream,bits.toint.@e,8))


Export type:cstr


Function createbytefile(name:seq.word, a:seq.int)int 
  createfile2(length.a,packed.bits(a @ add(empty:bitstream,bits.@e,8)) , tocstr.name)
    
Function createbytefile(name:seq.word, a:seq.byte)int 
    createfile2(length.a,packed.bits(a @ add(empty:bitstream,bits.toint.@e,8)) , tocstr.name)

          
use bitstream


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


Function fileexists(name:seq.word)boolean
 let file = getbitfile.tocstr.name
  size.file > -1

Function gettext(filename:seq.word)seq.seq.word breakparagraph.UTF8.getfile:byte(filename)  

Function createfile(filename:seq.word, s:seq.seq.word)int
 createbytefile(filename, s @ +(empty:seq.byte, toseqbyte.toUTF8.@e + [ byte.10, byte.10]))

Function createfile(filename:seq.word, s:seq.word)int createbytefile(filename, toseqbyte.toUTF8.s)

Function getfileaslines(filename:seq.word) seq.UTF8  breaklines.UTF8.getfile:byte(filename)


builtin tocstr(seq.bits) cstr

type cstr is record dummy:int

builtin createfile2(byteLength:int,data:seq.bits,cstr) int  

