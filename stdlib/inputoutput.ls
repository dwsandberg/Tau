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

type addrsym is addr:int, sym:symbol

use otherseq.addrsym

use seq.addrsym

use seq.int

function ?(a:addrsym, b:addrsym)ordering addr.a ? addr.b

Function stacktrace seq.word
let t = 
 for acc = empty:seq.addrsym, ll ∈ loadedLibs do
  for t = acc, idx = 1, i ∈ symboladdress.ll do next(t + addrsym(i, (libinfo.ll)_(symbolref.idx)), idx + 1)/for(t)
 /for(sort.acc)
for txt = " /p", r ∈ callstack.30 << 2 do
 let i = binarysearch(t, addrsym(r, Lit.1))
 txt + print.r
 + if between(-i - 1, 1, length.t)then print.sym.t_(-i - 1)else""/if
 + " /br"
/for(txt)

builtin callstack(n:int)seq.int

Builtin loadedLibs seq.liblib

Function createfile(name:seq.word, a:seq.bits)int createfile2(length.a * 8, packed.a, tocstr.name)

use tausupport

Function funcaddress(sym:symbol)int
let addrs = symboladdress.first.loadedLibs
let i = findindex(sym, subseq(symbolrefdecode.libinfo.first.loadedLibs, 1, length.addrs))
if i ≤ length.addrs then addrs_i else 0

Export createthread(adcret:int, adc:int, funcaddress:int, args:seq.int, argcode:int)process.int 