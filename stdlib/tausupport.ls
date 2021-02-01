module $internal

use seq.boolean

use seq.int

use seq.ptr

use seq.real

Builtin extractbit(seq.int, int)int

Builtin extractbyte(seq.int, int)int

Builtin GEP(seq.ptr, int)ptr

Builtin callidx(seq.int, int)int

Builtin callidx(seq.real, int)real

Builtin callidx(seq.ptr, int)ptr

Builtin setfld(int, seq.int, int)int

Builtin setfld(int, seq.real, real)int

Builtin setfld(int, seq.ptr, ptr)int

Builtin setfld(int, seq.boolean, boolean)int

module abstractBuiltin.T

use seq.T

Builtin IDX(seq.T, int)T

Builtin IDX2(seq.T, int)T

Builtin allocatespace:T(i:int)seq.T

Builtin setfld(i:int, s:seq.T, val:T)int

Builtin callidx2(a:seq.T, int)T

Builtin callidx(a:seq.T, int)T

module taubuiltinsupport.T

use standard

use abstractBuiltin.T

use seq.T

use abstractBuiltin.seq.T

use seq.seq.T

builtin setfirst(r:seq.T, fld0:int, fld1:int)seq.T

builtin bitcast(blockseq.T)seq.seq.T

builtin bitcast(seq.seq.T)seq.T

builtin bitcast(T)seq.T

function memcpy(idx:int, i:int, memsize:int, s:seq.T, fromaddress:T)int
 if memsize = 0 then idx
 else memcpy(setfld(idx, s, IDX(bitcast.fromaddress, i)), i + 1, memsize - 1, s, fromaddress)

type blockseq is sequence length:int, dummy:seq.T

function blocksize:T int 10000

Function_(a:blockseq.T, i:int)T
 assert between(i, 1, length.a)report"out of bounds"
 let data = bitcast.a
 let typ = getseqtype.dummy.a
 let ds = max(typ, 1)
  \\ assert false report"where"+ toword.ds \\
  let blksz = blocksize:T / ds
  let blk = IDX(data,(i - 1) / blksz + 2)
  let b =(i - 1) mod blksz + 1
   if typ > 1000 then callidx(blk, b)else IDX(blk, b + 1)

Function blockit(s:seq.T, ds:int)seq.T
 assert ds > 1 report"blockit problem"
 let blksz = blocksize:T / ds
  if length.s ≤ blksz then
  let newseq = allocatespace:T(length.s * ds + 2)
   let d =(for(@e ∈ s, acc = 2)memcpy(acc, 0, ds, newseq, @e))
    setfirst(newseq, 1, length.s)
  else
   let noblks =(length.s + blksz - 1) / blksz
   let blkseq = allocatespace:seq.T(noblks + 2)
   let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
   let discard =(for(@e ∈ arithseq(noblks, blksz, 1), acc = 2)setfld(acc, blkseq, blockit(subseq(s, @e, @e + blksz - 1), ds)))
    setfirst(bitcast.blkseq, blockseqtype, length.s)

Function blockit(s:seq.T)seq.T
 let blksz = blocksize:T
  if length.s ≤ blksz then
  let newseq = allocatespace:T(length.s + 2)
   let d =(for(@e ∈ s, acc = 2)setfld(acc, newseq, @e))
    setfirst(newseq, 0, length.s)
  else
   let noblks =(length.s + blksz - 1) / blksz
   let blkseq = allocatespace:seq.T(noblks + 2)
   let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
   let discard =(for(@e ∈ arithseq(noblks, blksz, 1), acc = 2)setfld(acc, blkseq, blockit.subseq(s, @e, @e + blksz - 1)))
    setfirst(bitcast.blkseq, blockseqtype, length.s)

module tausupport

use fileio

use mangle

use standard

use abstractBuiltin.boolean

use seq.byte

use abstractBuiltin.int

use taubuiltinsupport.int

use abstractBuiltin.ptr

use abstractBuiltin.real

use taubuiltinsupport.real

use encoding.typename

use encoding.seq.char

use seq.seq.int

use seq.encodingpair.seq.char

use taubuiltinsupport.encodingpair.seq.char

type ptr is record xx:int

Export IDX2(seq.ptr, int)ptr

Export IDX2(seq.real, int)real

Export IDX2(seq.boolean, int)boolean

Export IDX2(seq.int, int)int

Builtin initialdict seq.encodingpair.seq.char

builtin dlsymbol(cstr)int

Builtin createthread(int, int, int, seq.int, int)process.int

builtin callstack(n:int)seq.int

builtin addresstosymbol2(a:int)seq.char

Builtin randomint(i:int)seq.int

Function dlsymbol(name:word)int dlsymbol.tocstr.[ name]

Export_(pseq.byte, int)byte

Export blockit(seq.int)seq.int

Export blockit(s:seq.encodingpair.seq.char, ds:int)seq.encodingpair.seq.char // for use where the element type is represented in ds * 64bits where ds > 1. // // if the length < = blocksize then the result is represented as <ds> <length> <fld1.s_1><fld2.s_1>... <fld1.s_2><fld2.s_2>.... // // if the length > bloocksize then result is represented as <blockindexfunc> <length> <packed.subseq(s, 1, blocksize)> <packed.subseq(s, blocksize + 1, 2*blocksize)>.....//

Export blockit(seq.real)seq.real

Export_(blockseq.int, int)int

Export_(seq.int, int)int

Export decode(encoding.seq.char)seq.char

Export encode(seq.char)encoding.seq.char

Function deepcopy(a:int)int a

Function deepcopy(a:real)real a

type typename is record name:seq.word

function =(a:typename, b:typename)boolean name.a = name.b

function hash(a:typename)int hash.name.a

Function encodingno(name:seq.word)int
 if name = "char seq"then 1
 else if name = "typename"then 2 else valueofencoding.encode.typename.name + 2

function assignencoding(a:int, typename)int a + 1

-----------

Function stacktrace seq.word((for(@e ∈ callstack.30, acc ="")acc + decodeaddress.@e))

Function addresstosymbol(a:int)word encodeword.addresstosymbol2.a

Function decodeaddress(address:int)seq.word
 " &br" + ((for(@e ∈ codedown.addresstosymbol.address, acc ="")acc + @e))