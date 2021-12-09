Module libraryModule

use bits

use inputoutput

use standard

use symbol

use seq.bits

use seq.char

use seq.libraryModule

use seq.symbolref

use encoding.seq.char

use seq.seq.mytype

use seq.seq.word

use seq.encodingpair.seq.char

use symref


type symbolref is toint:int

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function ?(a:symbolref, b:symbolref)ordering toint.a ? toint.b

type libraryModule is modname:modref, exports:seq.symbolref, types:seq.seq.mytype

Export libraryModule(modname:modref, exports:seq.symbolref, types:seq.seq.mytype)libraryModule

Export type:libraryModule

Export exports(libraryModule)seq.symbolref

Export modname(libraryModule)modref

Export types(libraryModule)seq.seq.mytype

______________________

type parc is caller:symbolref, callee:symbolref, counts:int, clocks:int, space:int, unused:int

Export type:parc

Export parc(caller:symbolref, callee:symbolref, counts:int, clocks:int, space:int, unused:int)parc

Function =(a:parc, b:parc)boolean toint.callee.a = toint.callee.b ∧ toint.caller.a = toint.caller.b

Export caller(parc)symbolref

Export callee(parc)symbolref

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

Export type:liblib

___________________________

type liblib is libname:seq.word
, words:seq.encodingpair.seq.char
, entrypointaddress:int
, timestamp:int
, profiledata:seq.parc
, libinfo:compileinfo

Export entrypointaddress(liblib) int 

Export libinfo(liblib) compileinfo

Function code(l:liblib) seq.seq.symbolref code.libinfo.l

Export timestamp(liblib)int

Function decoderef(l:liblib)seq.symbol  symbolrefdecode.libinfo.l

Export libname(liblib)seq.word

Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

builtin loadedlibs2 seq.liblib

Function loadedLibs seq.liblib loadedlibs2

Function unloadlib(a:seq.word)int unloadlib2.tocstr.a

builtin unloadlib2(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[ a]

builtin loadlib(cstr)int

Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int
createlib2(tocstr.[ libname]
, tocstr.for acc = "", @e ∈ dependlibs do acc + [ @e] + ".dylib"/for(acc)
, length.b * 8
, packed.b
)

builtin createlib2(name:cstr, libs:cstr, length:int, data:seq.bits)int

_______________________

function findlibclause(a:seq.seq.word, i:int)seq.word
assert i < length.a report"No Library clause found"
let s = a_i
if s_1 = "Library"_1 then s else findlibclause(a, i + 1)

Function getlibrarysrc(libname:seq.word)seq.seq.word getlibraryinfo2.libname

Function getlibraryinfo2(libname:seq.word)seq.seq.word
{ first three lines are dependentlibs filelist and exports }
let a = gettext.[ merge([ first.libname] + "/" + last.libname + ".ls")]
let s = findlibclause(a, 1)
let l = break(s,"uses exports", true)
assert length.l = 3 ∧ l_2_1 = "uses"_1 ∧ l_3_1 = "exports"_1
report"lib clause problem"
let filelist = l_1 << 1
for acc = [ { dependentlibs } l_2 << 1, filelist, { exports } l_3 << 1] + a
, @e ∈ filelist
do
 if @e = last.libname then acc
 else
  let chars = decodeword.@e
  acc
  + gettext.if chars_1 = char1."/"then [ encodeword(chars << 1)] + ".ls"
  else [ first.libname] + "/" + @e + ".ls"/if
  + { File seperator } [ encodeword.[ char.28]]
/for(acc) 