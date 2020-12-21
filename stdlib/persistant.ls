Module persistant

use UTF8

use bits

use seq.encoding.seq.char

use set.encoding.seq.char

use encoding.seq.char

use seq.encodingpair.seq.char

use set.encodingpair.seq.char

use encoding.const3

use seq.encodingpair.const3

use seq.const3

use libdesc

use seq.liblib

use llvm

use llvmconstants

// use maindict //

use seq.seq.slot

use seq.slot

use standard

use encoding.word3

use seq.encodingpair.word3

use seq.word3

use words

Builtin initialdict seq.encodingpair.seq.char


type word3 is record toword:word

function assignencoding(l:int, a:word3)int valueofencoding.asencoding.toword.a

if toword.a in"//"then valueofencoding.asencoding.toword.a else toint(bits.assignrandom(l, a)&and bits(toint(bits.1 << 31)-1))

valueofencoding.asencoding.toword.a

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

function eword2(ww:encodingpair.word3)encodingpair.seq.char
 let w = data.ww
 let a = decodeword.toword.w
  encodingpair(to:encoding.seq.char(valueofencoding.encode.w), a)

Function constdata seq.slot encoding:seq.encodingpair.const3 @ +(empty:seq.slot, flds.@e)

type const3 is record place:int, flds:seq.slot

function flds(p:encodingpair.const3)seq.slot flds.data.p

function =(a:const3, b:const3)boolean flds.a = flds.b

function =(a:slot, b:slot)boolean toint.a = toint.b

function hash(a:const3)int hash(flds.a @ +(empty:seq.int, toint.@e))

function assignencoding(l:int, a:const3)int assignrandom(l, a)


/Function dumpword3 seq.word let x = encoding:seq.encodingpair.word3"len:"+ toword.length.x + @(+, toword,"", @(+, data, empty:seq.word3, x))

Function wordref(w:word)int
 let d = encode.word3.w
  toint.C64.valueofencoding.d

function wordcode(a:encodingpair.word3)encoding.seq.char asencoding.toword.data.a

Function addliblib(libname:seq.word, mods:int, profiledata:int,isbase:boolean)int
 let name = addwordseq2.libname
  let have = if isbase then empty:set.encoding.seq.char
  else
   // @(+, code, empty:set.encoding.seq.char, words.loadedlibs_1)//
   initialdict @ +(empty:set.encoding.seq.char, code.@e)
  let used = encoding:seq.encodingpair.word3 @ +(empty:set.encoding.seq.char, wordcode.@e)
   // build packed seq of word encodings //
   let wordstoadd = toseq(used - have)
      let data = wordstoadd @ +([ toint.C64.0, toint.C64.length.wordstoadd], addobject.fldsofwordencoding.@e)
    let wordreps = addobject.data
     addobject("liblib", [ name, wordreps, mods, toint.C64.0, profiledata])
     
     

function addobject(name:seq.word, data:seq.int)int
 let objtype = array(length.data, i64)
 let ll = global("liblib", objtype, toint.AGGREGATE(data @ +(empty:seq.slot, checkslot.@e)))
  toint.CGEP(slot.ll, 0)

function global(name:seq.word, type:llvmtype, init:int)int
 toint.modulerecord(name, [ toint.GLOBALVAR, typ.type, 2, 1 + init, 0, toint.align8 + 1, 0])

function checkslot(i:int)slot asi64.slot.i

Function addobject(fldsin:seq.int)int
 let flds = fldsin @ +(empty:seq.slot, checkslot.@e)
 let t = encoding:seq.encodingpair.const3
 let place = if length.t = 0 then 0 else place.data.last.t + length.flds.data.last.t
 let x = decode.encode.const3(place, flds)
 let idx = if place.x ≠ place then place.x else place
  toint.CGEP(modulerecord("list", [ 0]), idx)

function fldsofwordencoding(code:encoding.seq.char)seq.int
 let s = tointseq.decode.code
 let k = addobject(s @ +([ C64.0, C64.length.s], C64.@e)
 @ +(empty:seq.int, toint.@e))
  [ toint.C64.valueofencoding.code, k, toint.C64.0]

Function addwordseq2(a:seq.word)int
 addobject(a @ +([ toint.C64.0, toint.C64.length.a], wordref.@e))