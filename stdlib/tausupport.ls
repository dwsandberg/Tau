module XXX2.T

use seq.T

Builtin IDX(seq.T, int)T

Builtin IDXSEQ(seq.T, int, int)T

Builtin allocatespace:T(i:int)seq.T

Builtin setfld(i:int, s:seq.T, val:T)int

module taubuiltinsupport.T

use XXX2.T

use XXX2.seq.T

use seq.seq.T

use seq.T

use standard

Builtin callidx(a:seq.T, int)T

builtin bitcast(blockseq.T)seq.seq.T

builtin bitcast(seq.seq.T)seq.T

builtin bitcast(T)seq.T

function memcpy(idx:int, i:int, memsize:int, s:seq.T, fromaddress:T)int
 if memsize = 0 then idx
 else memcpy(setfld(idx, s, IDX(bitcast.fromaddress, i)), i + 1, memsize - 1, s, fromaddress)

builtin setfirst(r:seq.T, fld0:int, fld1:int)seq.T

type blockseq is sequence length:int, dummy:seq.T

function blocksize:T int 10000

Function_(a:blockseq.T, i:int)T
 assert between(i, 1, length.a)report"out of bounds"
 let data = bitcast.a
 let typ = getseqtype.dummy.a
 let ds = max(typ, 1)
  // assert false report"where"+ toword.ds //
  let blksz = blocksize:T / ds
  let blk = IDX(data,(i - 1) / blksz + 2)
  let b =(i - 1) mod blksz + 1
   if typ > 1000 then callidx(blk, b)
   else if typ > 1 then IDXSEQ(blk, typ, b)else IDX(blk, b + 1)

blk_((i-1)mod blksz + 1)

Function blockit(s:seq.T, ds:int)seq.T
 let blksz = blocksize:T / ds
  if length.s ≤ blksz then
  let newseq = allocatespace:T(length.s * ds + 2)
   let d = if ds > 1 then s @ memcpy(2, 0, ds, newseq, @e)else s @ setfld(2, newseq, @e)
    setfirst(newseq, ds, length.s)
  else
   let noblks =(length.s + blksz - 1) / blksz
   let blkseq = allocatespace:seq.T(noblks + 2)
   let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
   let discard = arithseq(noblks, blksz, 1) @ setfld(2, blkseq, blockit(subseq(s, @e, @e + blksz - 1), ds))
    setfirst(bitcast.blkseq, blockseqtype, length.s)

Function blockit(s:seq.T)seq.T
 let blksz = blocksize:T
  if length.s ≤ blksz then
  let newseq = allocatespace:T(length.s + 2)
   let d = s @ setfld(2, newseq, @e)
    setfirst(newseq, 0, length.s)
  else
   let noblks =(length.s + blksz - 1) / blksz
   let blkseq = allocatespace:seq.T(noblks + 2)
   let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
   let discard = arithseq(noblks, blksz, 1) @ setfld(2, blkseq, blockit.subseq(s, @e, @e + blksz - 1))
    setfirst(bitcast.blkseq, blockseqtype, length.s)

module tausupport

use encoding.seq.char

use seq.encodingpair.seq.char

use taubuiltinsupport.encodingpair.seq.char

use seq.seq.int



use taubuiltinsupport.int

use taubuiltinsupport.real

use standard

use encoding.typename

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

use mangle

builtin callstack(n:int)seq.int

Function stacktrace seq.word callstack.30 @ +("", decodeaddress.@e)

builtin addresstosymbol2(a:int)seq.char

Function addresstosymbol(a:int)word encodeword.addresstosymbol2.a

Function decodeaddress(address:int)seq.word" &br" + codedown.addresstosymbol.address @ +("", @e)

