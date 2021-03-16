module abstractBuiltin.T

use seq.T

Builtin IDX(seq.T, int)T

Builtin IDX:T(ptr, int)T

Builtin allocatespace:T(i:int)seq.T

Builtin setfld(i:int, s:seq.T, val:T)int

Builtin indexseq44(seqtype:int,s:seq.T,i:int) T

module taublockseq.T

use standard

use abstractBuiltin.T

use seq.T

use abstractBuiltin.seq.T

use seq.seq.T

Export type:seq.T

builtin setfirst(r:seq.T, fld0:int, fld1:int)seq.T

builtin bitcast(blockseq.T)seq.seq.T

builtin bitcast(seq.seq.T)seq.T

builtin bitcast(T)seq.T

function memcpy(idx:int, i:int, memsize:int, s:seq.T, fromaddress:T)int
 if memsize = 0 then idx
 else memcpy(setfld(idx, s, IDX(bitcast.fromaddress, i)), i + 1, memsize - 1, s, fromaddress)

type blockseq is sequence, dummy:seq.T

function blocksize:T int 10000

Function_(a:blockseq.T, i:int)T
 assert between(i, 1, length.toseq.a)report"out of bounds"
 let data = bitcast.a
 let typ = getseqtype.dummy.a
 let ds = max(typ, 1)
  \\ assert false report"where"+ toword.ds \\
  let blksz = blocksize:T / ds
  let blk = IDX(data,(i - 1) / blksz + 2)
  let b =(i - 1) mod blksz + 1
   indexseq44(typ,blk,b)   


Function blockit(s:seq.T, ds:int)seq.T
 assert ds > 1 report"blockit problem"
 let blksz = blocksize:T / ds
  if length.s ≤ blksz then
  let newseq = allocatespace:T(length.s * ds + 2)
  let d = for acc = 2, @e = s do memcpy(acc, 0, ds, newseq, @e)end(acc)
    setfirst(newseq, 1, length.s)
  else
   let noblks =(length.s + blksz - 1) / blksz
   let blkseq = allocatespace:seq.T(noblks + 2)
   let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
   let discard = for acc = 2, @e = arithseq(noblks, blksz, 1)do
    setfld(acc, blkseq, blockit(subseq(s, @e, @e + blksz - 1), ds))
   end(acc)
    setfirst(bitcast.blkseq, blockseqtype, length.s)

Function blockit(s:seq.T)seq.T
 let blksz = blocksize:T
  if length.s ≤ blksz then
  let newseq = allocatespace:T(length.s + 2)
 let d = for acc = 2, @e = s do setfld(acc, newseq, @e)end(acc)
    setfirst(newseq, 0, length.s)
  else
   let noblks =(length.s + blksz - 1) / blksz
   let blkseq = allocatespace:seq.T(noblks + 2)
   let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
  let discard = for acc = 2, @e = arithseq(noblks, blksz, 1)do
   setfld(acc, blkseq, blockit.subseq(s, @e, @e + blksz - 1))
  end(acc)
    setfirst(bitcast.blkseq, blockseqtype, length.s)

module tausupport

use fileio

use mangle

use standard

use abstractBuiltin.boolean

use seq.byte

use abstractBuiltin.int

use seq.int

use taublockseq.int

use taublockseq.packed2

use taublockseq.packed3

use taublockseq.packed4

use taublockseq.packed5

use taublockseq.packed6

use taublockseq.byte

use abstractBuiltin.ptr

use taublockseq.ptr

use abstractBuiltin.real

use taublockseq.real

use encoding.typename

use encoding.seq.char

use seq.seq.int

use seq.encodingpair.seq.char

type packed2 is fld1:int, fld2:int

type packed3 is fld1:int, fld2:int, fld3:int

type packed4 is fld1:int, fld2:int, fld3:int, fld4:int

type packed5 is fld1:int, fld2:int, fld3:int, fld4:int, fld5:int

type packed6 is fld1:int, fld2:int, fld3:int, fld4:int, fld5:int, fld6:int

type ptr is xx:int

Export IDX:ptr(ptr, int)ptr

Export IDX:real(ptr, int)real

Export IDX:boolean(ptr, int)boolean

Export IDX:int(ptr, int)int

Export setfld(int, seq.int, int)int

Builtin initialdict seq.encodingpair.seq.char

builtin dlsymbol(cstr)int

Builtin createthread(int, int, int, seq.int, int)process.int

builtin callstack(n:int)seq.int

builtin addresstosymbol2(a:int)seq.char

Builtin randomint(i:int)seq.int

Builtin getseqtype(ptr) int

Builtin getseqlength(ptr) int

Builtin toseqX:seq.int(ptr) seq.int

Function dlsymbol(name:word)int dlsymbol.tocstr.[ name]

Export_(pseq.byte, int)byte

Export blockit(seq.int)seq.int

Export blockit(seq.real)seq.real

Export blockit(s:seq.ptr)seq.ptr

/Export blockit(s:seq.byte) seq.byte

Function blockit(s:seq.packed2)seq.packed2 blockit(s, 2)

Function blockit(s:seq.packed3)seq.packed3 blockit(s, 3)

Function blockit(s:seq.packed4)seq.packed4 blockit(s, 4)

Function blockit(s:seq.packed5)seq.packed5 blockit(s, 5)

Function blockit(s:seq.packed6)seq.packed6 blockit(s, 6)

Export_(blockseq.int, int)int

Export_(seq.int, int)int

Export decode(encoding.seq.char)seq.char

Export encode(seq.char)encoding.seq.char

Function deepcopy(a:int)int a

Function deepcopy(a:real)real a

type typename is name:seq.word

function =(a:typename, b:typename)boolean name.a = name.b

function hash(a:typename)int hash.name.a

Function encodingno(name:seq.word)int
 if name = "char seq"then 1
 else if name = "typename"then 2 else valueofencoding.encode.typename.name + 2

function assignencoding(a:int, typename)int a + 1

-----------

Function stacktrace seq.word for acc ="", @e = callstack.30 << 2 do acc + " &br" + printmangled.addresstosymbol.@e end(acc)

Function addresstosymbol(a:int)word encodeword.addresstosymbol2.a