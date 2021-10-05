Module fileio

use UTF8

use bits

use bitstream

use standard

use textio

use seq.UTF8

use seq.bit

use seq.bits

use seq.byte

use seq.int

Export type:cstr

Function tocstr(s:seq.word)cstr
tocstr.packed.bits.for acc = empty:bitstream, @e ∈ toseqbyte.toUTF8.s + tobyte.0 do add(acc, bits.toint.@e, 8)/for(acc)

type fileresult is size:int, start:seq.int, data:seq.int

type fileresultbit is size:int, start:seq.bit, data:seq.bit

type fileresultbyte is size:int, start:seq.byte, data:seq.byte

type cstr is dummy:int

builtin createlib2(name:cstr, libs:cstr, length:int, data:seq.bits)int

Builtin getfile(name:cstr)fileresult

Builtin getbytefile(cstr)fileresultbyte

Builtin getbitfile(cstr)fileresultbit

Export type:fileresult

Export type:fileresultbyte

Export type:fileresultbit

builtin tocstr(seq.bits)cstr

Builtin createfile2(byteLength:int, data:seq.bits, cstr)int

Function createfile3(byteLength:int, data:seq.bits, name:cstr)int createfile2(byteLength, data, name)

Function getfile:int(name:seq.word)seq.int
let file = getfile.tocstr.name
start.file + data.file

Function getfile:byte(name:seq.word)seq.byte
let file = getbytefile.tocstr.name
assert size.file > -1 report"Error opening file" + name
start.file + data.file

Function getfile:bit(name:seq.word)seq.bit
let file = getbitfile.tocstr.name
assert size.file > -1 report"Error opening file" + name
start.file + data.file

Function fileexists(name:seq.word)boolean
let file = getbitfile.tocstr.name
size.file > -1

Function gettext(filename:seq.word)seq.seq.word breakparagraph.UTF8.getfile:byte(filename)

Function getfileaslines(filename:seq.word)seq.UTF8 breaklines.UTF8.getfile:byte(filename)

Function createfile(filename:seq.word, s:seq.seq.word)int
createfile(filename
, for acc = empty:seq.byte, @e ∈ s do acc + toseqbyte.toUTF8.@e + [ tobyte.10, tobyte.10]/for(acc)
)

Function createfile(filename:seq.word, s:seq.word)int createfile(filename, toseqbyte.toUTF8.s)

Function createfile(name:seq.word, a:seq.byte)int
createfile3(length.a
, packed.bits.for acc = empty:bitstream, @e ∈ a do add(acc, bits.toint.@e, 8)/for(acc)
, tocstr.name
)

Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int
createlib2(tocstr.[ libname]
, tocstr.for acc ="", @e ∈ dependlibs do acc + [ @e] + ".dylib"/for(acc)
, length.b * 8
, packed.b
)

Function createfile(name:seq.word, a:seq.int)int
createfile3(length.a * 8
, for acc = empty:seq.bits, @e ∈ packed.a do acc + bits.@e /for(acc)
, tocstr.name
)

Function toUTF8(a:seq.word)UTF8 addspace(a, 1, true, emptyUTF8)

function addspace(s:seq.word, i:int, nospace:boolean, result:UTF8)UTF8
{ nospace means add no space before word s_i.comma adds space after but not before single means add no space before or after 
 }
if i > length.s then result
else
 let this = s_i
 if this = " /br"_1 then addspace(s, i + 1, true, result + char.10)
 else if this = ","_1 then
  { no space before but space after } addspace(s, i + 1, false, result + char1.",")
 else
  let d = for acc = emptyUTF8, @e ∈ decodeword.this do acc + encodeUTF8.@e /for(acc)
  if this ∈ ('-()].:"_^. ' + space)then
   { no space before or after } addspace(s, i + 1, true, result + d)
  else
   addspace(s, i + 1, false, if nospace then result + d else result + char.32 + d) 