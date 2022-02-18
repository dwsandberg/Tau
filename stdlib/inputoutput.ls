Module inputoutput

use UTF8

use bits

use bitstream

use libraryModule

use standard

use symbol

use seq.bit

use seq.bits

use seq.byte

use otherseq.char

use process.int

use seq.int

use seq.liblib

use otherseq.symbol

use seq.symbol

use process.seq.bit

use process.seq.byte

use encoding.seq.char

use process.seq.int

Export type:cstr

Function tocstr(s:seq.word)cstr
let t = for acc = emptyUTF8, w ∈ s do acc + decodeword.w /for(toseqbyte.acc)
cstr.packed.bits.for acc = empty:bitstream, @e ∈ t + tobyte.0 do add(acc, bits.toint.@e, 8)/for(acc)

type cstr is dummy:seq.bits

Builtin getfile2(cstr)process.seq.int{OPTION STATE}

Builtin getbytefile2(cstr)process.seq.byte{OPTION STATE}

Builtin getbitfile2(cstr)process.seq.bit{OPTION STATE}

Function getfile:byte(name:seq.word)seq.byte
let a = getbytefile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.byte)

Function getfile:bit(name:seq.word)seq.bit
let a = getbitfile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.bit)

Function getfile:int(name:seq.word)seq.int
let a = getfile2.tocstr.name
assert not.aborted.a report"Error opening file:" + name
result.merge(a, result.a + body2.a, empty:seq.int)

Builtin createfile2(byteLength:int, data:seq.bits, cstr)int{OPTION STATE}

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
do if first.libname.ll = library ∧ idx ≤ length.decoderef.ll then print.(decoderef.ll)_idx else name2
/for(if isempty.name2 then[encodeword.name]else name2 /if)

builtin callstack(n:int)seq.int

builtin addresstosymbol2(a:int)seq.char

Builtin loadedlibs2 seq.liblib

Function loadedLibs seq.liblib loadedlibs2

Function unloadlib(a:seq.word)int unloadlib2.tocstr.a

builtin unloadlib2(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[a]

builtin loadlib(cstr)int

Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int
createlib2(tocstr.[libname]
, tocstr.for acc = "", @e ∈ dependlibs do acc + [@e] + ".dylib"/for(acc)
, length.b * 8
, packed.b
)

builtin createlib2(name:cstr, libs:cstr, length:int, data:seq.bits)int

Function createthreadB(funcaddress:int, returntype:mytype, args:seq.int, argcode:int)process.int
let adcret = funcaddress.deepcopySym.returntype
let adc = funcaddress.deepcopySym.seqof.typeword
createthreadI(adcret, adc, funcaddress, packed.args, argcode)

Function funcaddress(sym:symbol)int
let addrs = symboladdress.first.loadedLibs
let i = findindex(sym, subseq(symbolrefdecode.libinfo.first.loadedLibs, 1, length.addrs))
if i ≤ length.addrs then addrs_i else 0

builtin createthreadI(int, int, int, seq.int, int)process.int 