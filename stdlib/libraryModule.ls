Module libraryModule

use bits

use standard

use symbol

use textio

use typedict

use seq.bits

use seq.char

use seq.libraryModule

use encoding.symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use seq.symbolref

use encoding.seq.char

use seq.seq.mytype

use seq.encodingpair.symbol

use otherseq.seq.symbol

use set.seq.symbol

use otherseq.seq.symbolref

use seq.seq.symbolref

use seq.seq.word

use seq.encodingpair.seq.char

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
, symboladdress:seq.int


Export symboladdress(liblib)seq.int

Export entrypointaddress(liblib)int

Export libinfo(liblib)compileinfo

Function code(l:liblib)seq.seq.symbolref code.libinfo.l

Export timestamp(liblib)int

Function decoderef(l:liblib)seq.symbol symbolrefdecode.libinfo.l

Export libname(liblib)seq.word

Export words(liblib)seq.encodingpair.seq.char

Export profiledata(liblib)seq.parc

_______________________

function findlibclause(a:seq.seq.word, i:int)seq.word
assert i < length.a report"No Library clause found"
let s = a_i
if s_1 = "Library"_1 then s else findlibclause(a, i + 1)

Function getlibrarysrc(libname:seq.word)seq.seq.word
{OPTION INLINE}
{library info is contain in first paragraph of result}
let a = breakparagraph.getfile:UTF8([first.libname] + "/" + last.libname + ".ls")
let l = extractinfo.a
let filelist = l_1 << 1
for acc = ["Library" + first.libname + "uses" + l_2 << 1 + "exports" + l_3 << 1
, "file(" + first.libname + "/" + last.libname + ".ls)"
]
+ a
, @e ∈ filelist
do
 if @e = last.libname then acc
 else
  let chars = decodeword.@e
  let t = 
   breakparagraph.getfile:UTF8(if chars_1 = char1."/"then[encodeword(chars << 1)] + ".ls"
   else[first.libname] + "/" + @e + ".ls"
   )
  acc
  + if subseq(t, 1, 1) = ["file(" + first.libname + "/" + @e + ".ls)"]then
   t
  else["file(" + first.libname + "/" + @e + ".ls)"] + t
/for(acc)

Function extractinfo(a:seq.seq.word)seq.seq.word
{first three lines are dependentlibs filelist and exports}
for l = empty:seq.seq.word, s ∈ a
while isempty.l
do if subseq(s, 1, 1) = "Library"then break(s, "uses exports", true)else l
/for(assert length.l = 3 ∧ l_2_1 = "uses"_1 ∧ l_3_1 = "exports"_1
report"lib clause problem"
l)

_________________

type compileinfo is symbolrefdecode:seq.symbol
, mods:seq.libraryModule
, code:seq.seq.symbolref
, src:seq.seq.word
, typedict:typedict


Export type:compileinfo

Export code(compileinfo)seq.seq.symbolref

Export mods(compileinfo)seq.libraryModule

Export typedict(compileinfo)typedict

Export symbolrefdecode(compileinfo)seq.symbol

Export src(compileinfo)seq.seq.word

Function compileinfo(t:typedict, code:seq.seq.symbolref, src:seq.seq.word, d:seq.symbol, m:seq.libraryModule)compileinfo
compileinfo(d, m, code, src, t)

Function profiledata(info:compileinfo)seq.int
let l = first.code.info << 4
for acc = [1, length.l / 2], first = true, r ∈ l do
 if first then next(acc + toint.r, false)else next(acc + toint.r + [0, 0, 0, 0], true)
/for(acc)

Function profilearcs(info:compileinfo)set.seq.symbol
let l = first.code.info << 4
for acc = empty:set.seq.symbol, first = true, last = Lit.0, r ∈ l do
 let sym = info_r
 if first then next(acc, false, sym)else next(acc + [last, sym], true, sym)
/for(acc)

Function newmaplength(info:compileinfo)int toint.(first.code.info)_2

Function libcodelength(info:compileinfo)int toint.(first.code.info)_3

Function addresslength(info:compileinfo)int toint.(first.code.info)_4

Function libcode(info:compileinfo)seq.seq.symbolref subseq(code.info, 2, libcodelength.info + 1)

Function prgcode(info:compileinfo)seq.seq.symbolref subseq(code.info, libcodelength.info + 2, length.code.info)

Function _(info:compileinfo, r:symbolref)symbol
let i = toint.r
if i > 0 then(symbolrefdecode.info)_i else Fref.(symbolrefdecode.info)_(-i)

Function roots(s:compileinfo)set.symbol
let exports = 
 for exports = empty:seq.symbolref, m ∈ mods.s do exports + exports.m /for(exports)
for acc = empty:set.symbol, r ∈ exports do acc + s_r /for(acc)

Function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

Function assignencoding(a:symbol)int nextencoding.a

Function decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s)

Function symbolrefdecode seq.symbol
for acc = empty:seq.symbol, p ∈ encoding:seq.encodingpair.symbol do acc + data.p /for(acc) 