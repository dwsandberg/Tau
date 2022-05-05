Module persistant

use UTF8

use bits

use inputoutput

use libraryModule

use llvm

use llvmconstants

use mytype

use standard

use symbol

/use symbol2

use words

use encoding.const3

use seq.const3

use seq.liblib

use seq.libraryModule

use seq.mytype

use seq.slot

use seq.symbol

use seq.symbolref

use seq.typedef

use encoding.word3

use seq.word3

use encoding.seq.char


use seq.seq.mytype

use seq.seq.slot

use seq.seq.symbolref


use seq.encoding.seq.char

use set.encoding.seq.char

use otherseq.char

use set.word3

Export loadedLibs seq.liblib

Export externnames(seq.word) set.symdef

type word3 is chars:seq.char,code:encoding.seq.char ,slot:int

function word3(a:word) word3    
word3.decodeword.a 

function word3(a:seq.char) word3
   let b=asencoding.encodeword.a
   word3(a,b,toint.C64.valueofencoding.b)

function ?(a:word3,b:word3) ordering chars.a ? chars.b 


function assignencoding(a:word3)int  valueofencoding.encode.chars.a  

nextencoding.a

function =(a:word3, b:word3)boolean chars.a = chars.b

function hash(a:word3)int hash.chars.a

Function constdata seq.slot
for acc = empty:seq.slot, @e ∈ encodingdata:const3 do acc + flds.@e /for(acc)

type const3 is place:int, flds:seq.slot

function =(a:const3, b:const3)boolean flds.a = flds.b

function =(a:slot, b:slot)boolean toint.a = toint.b

function hash(a:const3)int hash.for acc = empty:seq.int, @e ∈ flds.a do acc + toint.@e /for(acc)

function assignencoding(a:const3)int nextencoding.a

Function wordref(w:word)int 
assert  valueofencoding.encode.word3.w=valueofencoding.code.word3.w report "ADDFDSDF"+w
slot.word3.w



Function addliblib(libname:seq.word
, decodesymref:seq.symbol
, libmods2:seq.libraryModule
, code2:seq.seq.symbolref
, profiledata:int
, dependlibs:seq.word
, entrypoint:slot
, symboladdresses:int
)int
let symbolrefdecode2 = addsymbolseq.decodesymref
let code = addsymbolrefseqseq.code2
let libmods = addlibmodseq.libmods2
let name = addwordseq.libname
let have = 
 for acc0 = empty:set.word3, ll ∈ loadedLibs do
  if first.libname.ll ∈ dependlibs then
   for acc = acc0, @e ∈ words.ll do acc + word3(data.@e) /for(acc)
  else acc0
 /for(acc0)
let used = 
 for acc = empty:set.word3, @e ∈ encodingdata:word3 do  acc + @e /for(acc)
{build packed seq of word encodings}
let wordstoadd = toseq(used \ have)
let data = 
 for acc = [toint.C64.0, toint.C64.length.wordstoadd], @e ∈ wordstoadd do acc + addobject.fldsofwordencoding.@e /for(acc)
let wordreps = addobject.data
let emptyseq = addobject.[toint.C64.0, toint.C64.0]
addobject2("liblib" + libname
, [name
, wordreps
, toint.entrypoint
, toint.C64.0
, profiledata
, symbolrefdecode2
, libmods
, code
, {src}emptyseq
, {typedict}emptyseq
, symboladdresses
]
)

function addobject2(name:seq.word, data:seq.int)int
let objtype = array(length.data, i64)
let ll = 
 global(name
 , objtype
 , AGGREGATE.for acc = empty:seq.slot, @e ∈ data do acc + asi64.slot.@e /for(acc)
 )
toint.CGEP(slot.ll, 0)

Function global(name:seq.word, type:llvmtype, init:slot)int
toint.modulerecord(name, [toint.GLOBALVAR, typ.type, 2, 1 + toint.init, 0, toint.align8 + 1, 0])

Function addobject(fldsin:seq.int)int
let flds = for acc = empty:seq.slot, @e ∈ fldsin do acc + asi64.slot.@e /for(acc)
let t =encodingdata:const3
let place = if length.t = 0 then 0 else place.last.t + length.flds.last.t
let x = decode.encode.const3(place, flds)
let idx = if place.x ≠ place then place.x else place
toint.CGEP(modulerecord("list", [0]), idx)

function fldsofwordencoding(w3:word3)seq.int
let s = tointseq.chars.w3
let k = 
 addobject.for acc = empty:seq.int
 , @e ∈ for acc = [C64.0, C64.length.s], @e ∈ s do acc + C64.@e /for(acc)
 do acc + toint.@e /for(acc)
[slot.w3, k, toint.C64.0]

Function addwordseq(a:seq.word)int
addobject.for acc = [toint.C64.0, toint.C64.length.a], @e ∈ a do acc + wordref.@e /for(acc)

Function addtype(a:mytype)int
addobject.for acc = [toint.C64.1, toint.C64.length.typerep.a], e ∈ typerep.a do
 acc + wordref.name.e + wordref.modname.e + wordref.library.e
/for(acc)

Function addtypeseq(a:seq.mytype)int
addobject.for acc = [toint.C64.0, toint.C64.length.a], @e ∈ a do acc + addtype.@e /for(acc)

Function addtypeseqseq(a:seq.seq.mytype)int
addobject.for acc = [toint.C64.0, toint.C64.length.a], @e ∈ a do acc + addtypeseq.@e /for(acc)

Function addsymbolrefseq(a:seq.symbolref)int
addobject.for acc = [toint.C64.0, toint.C64.length.a], @e ∈ a do acc + toint.C64.toint.@e /for(acc)

function addsymbolrefseqseq(a:seq.seq.symbolref)int
addobject.for acc = [toint.C64.0, toint.C64.length.a], @e ∈ a do acc + addsymbolrefseq.@e /for(acc)

Function addlibmod(a:libraryModule)int
addobject.[wordref.library.modname.a
, wordref.name.modname.a
, addtype.para.modname.a
, addsymbolrefseq.exports.a
, addtypeseqseq.types.a
]

function addlibmodseq(a:seq.libraryModule)int
addobject.for acc = [toint.C64.0, toint.C64.length.a], @e ∈ a do acc + addlibmod.@e /for(acc)

Function addsymbol(a:symbol)int
addobject.[addwordseq.worddata.a
, wordref.library.module.a
, wordref.name.module.a
, addtype.para.module.a
, addtypeseq.types.a
, toint.C64.toint.raw.a
, toint.C64.extrabits.a
]

function addsymbolseq(a:seq.symbol)int
addobject.for acc = [toint.C64.0, toint.C64.length.a], @e ∈ a do acc + addsymbol.@e /for(acc)

/type modref is library:word, name:word, para:mytype

/type libraryModule is modname:modref, exports:seq.symbolref, types:seq.seq.mytype

/type symbol is worddata:seq.word, module:modref, types:seq.mytype, raw:bits, hashbits:bits 