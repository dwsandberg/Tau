Module libraryModule

use symbol

use seq.symbolref

use seq.seq.mytype

use standard

 type symbolref is toint:int

Export toint(symbolref)int

Export symbolref(int)symbolref

Export type:symbolref

Function ?(a:symbolref,b:symbolref) ordering toint.a ? toint.b

type libraryModule is modname:modref, exports:seq.symbolref,types:seq.seq.mytype

Export libraryModule( modname:modref, exports:seq.symbolref,types:seq.seq.mytype)libraryModule

Export type:libraryModule

Export   exports(libraryModule)  seq.symbolref

Export modname(libraryModule) modref

Export types(libraryModule) seq.seq.mytype

______________________

type parc is caller:symbolref, callee:symbolref, counts:int, clocks:int, 
space:int, unused:int

Export type:parc 

Export parc(caller:symbolref, callee:symbolref, counts:int, clocks:int, 
space:int, unused:int) parc

Function =(a:parc,b:parc)boolean toint.callee.a=toint.callee.b /and toint.caller.a=toint.caller.b

Export caller(parc) symbolref

Export callee(parc) symbolref

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int

Export type:liblib

___________________________

use seq.encodingpair.seq.char

use encoding.seq.char


type liblib is libname:seq.word, words:seq.encodingpair.seq.char,unused:int, timestamp:int
, profiledata:seq.parc ,decoderef:seq.symbol,newmods:seq.libraryModule
, code:seq.seq.symbolref



Export code(liblib) seq.seq.symbolref 

Export timestamp(liblib)int

Export decoderef(liblib) seq.symbol

Export newmods(liblib) seq.libraryModule

Export libname(liblib)seq.word

Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

builtin loadedlibs2 seq.liblib

Function loadedLibs seq.liblib loadedlibs2

Function unloadlib(a:seq.word)int unloadlib2.tocstr.a

use seq.libraryModule

use fileio
  
builtin unloadlib2(cstr)int

Function loadlibrary(a:word)int loadlib.tocstr.[ a]

builtin loadlib(cstr)int 

_______________________

function findlibclause(a:seq.seq.word, i:int)seq.word
 assert i < length.a report"No Library clause found"
 let s = a_i
  if s_1 = "Library"_1 then s else findlibclause(a, i + 1)

Function getlibraryinfo(libname:seq.word)seq.seq.word
let a = gettext.[ merge([ first.libname] + "/" + last.libname + ".ls")]
let s = findlibclause(a, 1)
let l = break(s,"uses exports", true)
assert length.l = 3 ∧ l_2_1 = "uses"_1
 ∧ l_3_1 = "exports"_1 report"lib clause problem"
 [ { dependentlibs }l_2 << 1, { filelist }l_1 << 1, { exports }l_3 << 1]

Function getlibrarysrc(libname:seq.word)seq.seq.word
let filelist =(getlibraryinfo.libname)_2
 for acc = empty:seq.seq.word, @e = filelist do
  acc + gettext.[ merge([ first.libname] + "/" + @e + ".ls")]
 /for(acc)

Function getlibraryinfo(libname:word)seq.seq.word getlibraryinfo.[ libname]

Function getlibrarysrc(libname:word)seq.seq.word getlibrarysrc.[ libname] 