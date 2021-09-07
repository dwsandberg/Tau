Module persistant

use UTF8

use bits

use libraryModule

use llvm

use llvmconstants

use standard

use tausupport

use words

use encoding.const3

use seq.const3

use seq.liblib

use seq.slot

use encoding.word3

use seq.word3

use encoding.seq.char

use seq.encodingpair.const3

use seq.seq.slot

use seq.encodingpair.word3

use seq.encoding.seq.char

use set.encoding.seq.char

use seq.encodingpair.seq.char

use set.encodingpair.seq.char

/ use maindict

Export initialdict seq.encodingpair.seq.char

type word3 is toword:word

function assignencoding(p:seq.encodingpair.word3, a:word3)int encoding.toword.a

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

function eword2(ww:encodingpair.word3)encodingpair.seq.char
let w = data.ww
let a = decodeword.toword.w
 encodingpair(to:encoding.seq.char(valueofencoding.encode.w), a)

Function constdata seq.slot for acc = empty:seq.slot, @e = encoding:seq.encodingpair.const3 do acc + flds.@e /for(acc)

type const3 is place:int, flds:seq.slot

function flds(p:encodingpair.const3)seq.slot flds.data.p

function =(a:const3, b:const3)boolean flds.a = flds.b

function =(a:slot, b:slot)boolean toint.a = toint.b

function hash(a:const3)int
 hash.for acc = empty:seq.int, @e = flds.a do acc + toint.@e /for(acc)

function assignencoding(p:seq.encodingpair.const3, a:const3)int assignrandom(p, a)

llvmtypeele

/Function dumpword3 seq.word let x = encoding:seq.encodingpair.word3"len:"+ toword.length.x + @(+, toword,"", @(+, data, empty:seq.word3, x))

Function wordref(w:word)int let d = encode.word3.w
 toint.C64.valueofencoding.d

function wordcode(a:encodingpair.word3)encoding.seq.char to:encoding.seq.char(encoding.toword.data.a)

Function addliblib(libname:seq.word, mods:seq.int, profiledata:int, isbase:boolean)int
let name = addwordseq2.libname
let have = if isbase then empty:set.encoding.seq.char
else
 { @(+, code, empty:set.encoding.seq.char, words.loadedlibs_1)}
 for acc = empty:set.encoding.seq.char, @e = initialdict do acc + code.@e /for(acc)
let used = for acc = empty:set.encoding.seq.char, @e = encoding:seq.encodingpair.word3 do acc + wordcode.@e /for(acc)
{ build packed seq of word encodings }
 let wordstoadd = toseq(used \ have)
 let data = for acc = [ toint.C64.0, toint.C64.length.wordstoadd], @e = wordstoadd do acc + addobject.fldsofwordencoding.@e /for(acc)
 let wordreps = addobject.data
  addobject("liblib", [ name, wordreps, toint.C64.0, toint.C64.0, profiledata]+ mods)

function addobject(name:seq.word, data:seq.int)int
let objtype = array(length.data, i64)
let ll = global("liblib", objtype, AGGREGATE.for acc = empty:seq.slot, @e = data do acc + asi64.slot.@e /for(acc))
toint.CGEP(slot.ll, 0)

Function global(name:seq.word, type:llvmtype, init:slot)int
 toint.modulerecord(name, [ toint.GLOBALVAR, typ.type, 2, 1 + toint.init, 0, toint.align8 + 1, 0])

Function addobject(fldsin:seq.int)int
let flds = for acc = empty:seq.slot, @e = fldsin do acc + asi64.slot.@e /for(acc)
let t = encoding:seq.encodingpair.const3
let place = if length.t = 0 then 0 else place.data.last.t + length.flds.data.last.t
let x = decode.encode.const3(place, flds)
let idx = if place.x ≠ place then place.x else place
 toint.CGEP(modulerecord("list", [ 0]), idx)

function fldsofwordencoding(code:encoding.seq.char)seq.int
let s = tointseq.decode.code
let k = addobject.for acc = empty:seq.int, @e = for acc = [ C64.0, C64.length.s], @e = s do acc + C64.@e /for(acc)do
 acc + toint.@e
/for(acc)
[ toint.C64.valueofencoding.code, k, toint.C64.0]

Function addwordseq2(a:seq.word)int
 addobject.for acc = [ toint.C64.0, toint.C64.length.a], @e = a do acc + wordref.@e /for(acc) 