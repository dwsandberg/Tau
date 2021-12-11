
Module inputoutput

use UTF8

use bits

use bitstream

use standard

use fileT.bit

use seq.bit

use seq.bits

use fileT.byte

use seq.byte

use fileT.int

use seq.int

use encoding.seq.char

Export type:cstr

Function tocstr(s:seq.word)cstr
let t = for acc = emptyUTF8, w ∈ s do acc + decodeword.w /for(toseqbyte.acc)
cstr.packed.bits.for acc = empty:bitstream, @e ∈ t + tobyte.0 do add(acc, bits.toint.@e, 8)/for(acc)

type cstr is dummy:seq.bits

Builtin getfile2(cstr)fileresult.int {OPTION STATE }

Builtin getbytefile2(cstr)fileresult.byte {OPTION STATE }

Builtin getbitfile2(cstr)fileresult.bit {OPTION STATE }

Function getfile:byte(name:seq.word)seq.byte    result(getbytefile2.tocstr.name,name)
 
Function getfile:bit(name:seq.word)seq.bit result(getbitfile2.tocstr.name,name)

Function getfile:int(name:seq.word)seq.int result(getfile2.tocstr.name,name)

Builtin createfile2(byteLength:int, data:seq.bits, cstr)int {OPTION STATE }

Function createfile(name:seq.word, a:seq.byte)int
createfile2(length.a
, packed.bits.for acc = empty:bitstream, @e ∈ a do add(acc, bits.toint.@e, 8)/for(acc)
, tocstr.name
)

Function createfile(name:seq.word, a:seq.int)int
createfile2(length.a * 8
, for acc = empty:seq.bits, @e ∈ packed.a do acc + bits.@e /for(acc)
, tocstr.name
)


Builtin randomint(i:int)seq.int

Function stacktrace seq.word internalstacktrace

Function internalstacktrace seq.word
for acc = "", @e ∈ callstack.30 << 2 do acc + " /br" + printfunc.addresstosymbol2.@e /for(acc)

function printfunc(name:seq.char)seq.word
 let i = findindex(char1."$", name)
 let library = encodeword.subseq(name, 1, i - 1)
 let idx = toint.encodeword.subseq(name, i + 2, length.name)
 for name2 = "", ll ∈ loadedLibs
 while isempty.name2
 do if first.libname.ll = library  /and  idx /le length.decoderef.ll  then print.(decoderef.ll)_idx else name2
 /for(if isempty.name2 then [ encodeword.name]else name2 /if)

builtin callstack(n:int)seq.int

builtin addresstosymbol2(a:int)seq.char 

use otherseq.char

use seq.symbol

use symbol

use libraryModule


Module fileT.T

use inputoutput

use standard

use seq.T

Export type:fileresult.T

type fileresult is size:int, start:seq.T, data:seq.T

Function result(a:fileresult.T,name:seq.word)seq.T 
 assert size.a /ge 0 report "Error opening file:"+name
start.a + data.a


