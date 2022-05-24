
Module liblib 

use standard

use libraryModule

use persistant

use symbol2

use seq.mytype

use seq.symbol

use mytype

use seq.typedef

use seq.seq.mytype

use seq.symbolref

use seq.seq.symbolref

use seq.libraryModule

/use symbol

use bits


Function morefields(profiledata:int,libcode:seq.symdef,m:midpoint,addresses:seq.symbol,symboladdresses:int) seq.int
 let discard23 = for acc2 = symbolref.0, sym2 ∈ addresses do symbolrefnew.sym2 /for(acc2)
let newmods = 
 for acc = empty:seq.libraryModule, @e ∈  libmods.m do
  for newexports = empty:seq.symbolref, sym2 ∈ exports.@e do newexports + symbolrefnew.sym2 /for(acc + libraryModule(modname.@e, newexports, types.@e))
 /for(acc)
let code = 
for acc = empty:seq.seq.symbolref,sd2 /in libcode  do 
 acc
 + for acc2 = [symbolrefnew.sym.sd2], sym2 ∈ code.sd2 do
  if isFref.sym2 then acc2 + symbolrefnew.PreFref + symbolrefnew.basesym.sym2
  else acc2 + symbolrefnew.sym2
 /for(acc2)
/for(acc)
[profiledata
, addsymbolseq.symbolrefdecodenew
, addlibmodseq.newmods
, addsymbolrefseqseq.code
,  addint.0
,  addint.0
, symboladdresses]

Function addtype(a:mytype)int
addobject.for acc = [addint.1, addint.length.typerep.a], e ∈ typerep.a do
 acc + wordref.name.e + wordref.modname.e + wordref.library.e
/for(acc)

Function addtypeseq(a:seq.mytype)int
addobject.for acc = [addint.0, addint.length.a], @e ∈ a do acc + addtype.@e /for(acc)

Function addtypeseqseq(a:seq.seq.mytype)int
addobject.for acc = [addint.0, addint.length.a], @e ∈ a do acc + addtypeseq.@e /for(acc)

Function addsymbolrefseq(a:seq.symbolref)int
addobject.for acc = [addint.0, addint.length.a], @e ∈ a do acc + addint.toint.@e /for(acc)

Function addsymbolrefseqseq(a:seq.seq.symbolref)int
addobject.for acc = [addint.0, addint.length.a], @e ∈ a do acc + addsymbolrefseq.@e /for(acc)

Function addlibmod(a:libraryModule)int
addobject.[wordref.library.modname.a
, wordref.name.modname.a
, addtype.para.modname.a
, addsymbolrefseq.exports.a
, addtypeseqseq.types.a
]

Function addlibmodseq(a:seq.libraryModule)int
addobject.for acc = [addint.0, addint.length.a], @e ∈ a do acc + addlibmod.@e /for(acc)

Function addsymbol(a:symbol)int
let t=privatefields.a
addobject.[addwordseq.worddata.a
, wordref.library.module.a
, wordref.name.module.a
, addtype.para.module.a
, addtypeseq.types.a
, addint.t_1
, addint.t_2
]

Function addsymbolseq(a:seq.symbol)int
addobject.for acc = [addint.0, addint.length.a], @e ∈ a do acc + addsymbol.@e /for(acc)

/type modref is library:word, name:word, para:mytype

/type libraryModule is modname:modref, exports:seq.symbolref, types:seq.seq.mytype

/type symbol is worddata:seq.word, module:modref, types:seq.mytype, raw:bits, hashbits:bits 

type symbolnew is tosymbol:symbol

Function symbolrefnew(sym:symbol)symbolref symbolref.addorder.symbolnew.clearrequiresbit.sym

Function symbolrefdecodenew seq.symbol
for acc = empty:seq.symbol, p ∈ encodingdata:symbolnew do acc + tosymbol.p /for(acc)

function hash(a:symbolnew)int hash.tosymbol.a

function =(a:symbolnew, b:symbolnew)boolean tosymbol.a = tosymbol.b


use encoding.symbolnew


Module persistant

use UTF8

use bits

use llvm

use llvmconstants

use standard

use words

use otherseq.char

use encoding.const3

use seq.const3

use seq.slot

use encoding.word3

use seq.word3

use set.word3

use encoding.seq.char

use seq.seq.slot

use seq.encoding.seq.char

use set.encoding.seq.char

type word3 is chars:seq.char 

function word3(a:word)word3 word3.decodeword.a

function slotX(a:word3) int toint.C64.valueofencoding.encode.a

function ?(a:word3, b:word3)ordering chars.a ? chars.b


function =(a:word3, b:word3)boolean chars.a = chars.b

function hash(a:word3)int hash.chars.a

Function constdata seq.slot for acc = empty:seq.slot, @e ∈ encodingdata:const3 do acc + flds.@e /for(acc)

type const3 is place:int, flds:seq.slot

function =(a:const3, b:const3)boolean flds.a = flds.b

function =(a:slot, b:slot)boolean toint.a = toint.b

function hash(a:const3)int hash.for acc = empty:seq.int, @e ∈ flds.a do acc + toint.@e /for(acc)

use seq.seq.char

use set.encoding.word3

Function wordref(w:word)int
{identity, y}
let w3 = word3.w
let discard = encode.w3
slotX.w3

Function addint(i:int)int toint.C64.i

Function initwordref(dependentwords:seq.seq.char) int
 { assert length.dependentwords=0 report
   for txt="",max=0, p /in subseq(encodingdata:seq.char,1,length.dependentwords) do
     let w=encodeword.p
     next(txt+"/br"+%.valueofencoding.asencoding.w+w 
     , max(max,valueofencoding.asencoding.w))
     /for(%.max+%.length.dependentwords+txt)
0
}
  for acc = 0, @e ∈ dependentwords do 
max(acc,valueofencoding.asencoding.encodeword(@e))
 /for(for  acc2=0, k /in subseq(encodingdata:seq.char,1,acc) do
            valueofencoding.encode.word3.k /for(acc))
 
 use seq.encoding.word3

Function addliblib(libname:seq.word, dependentwords:seq.seq.char, entrypoint:slot, more:seq.int)int
let name = addwordseq.libname
let have = for acc = empty:set.encoding.word3, @e ∈ dependentwords do acc + encode.word3.@e /for(acc)
let used = for acc = empty:set.encoding.word3, @e ∈ encodingdata:word3 do acc + encode.@e /for(acc)
{build packed seq of word encodings}
let wordstoadd = toseq(used \ have)
let data = 
 for acc = [toint.C64.0, toint.C64.length.wordstoadd], @e ∈ wordstoadd do acc + addobject.fldsofwordencoding.decode.@e /for(acc)
let wordreps = addobject.data
addobject2("liblib" + libname, [name, wordreps, toint.entrypoint, addint.0] + more)

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
let t = encodingdata:const3
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
[slotX.w3, k, toint.C64.0]

Function addwordseq(a:seq.word)int
addobject.for acc = [toint.C64.0, toint.C64.length.a], @e ∈ a do acc + wordref.@e /for(acc) 