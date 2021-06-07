module taublockseq.T

use standard

use tausupport

use seq.T

Export type:seq.T

builtin bitcast:T(ptr)seq.T

builtin load(address:blockseq.T,offset:int)  seq.T  {load value of type T at address}

unbound set (ptr, T) ptr

type blockseq is sequence, dummy:seq.T

function blocksize:T int 8160

Function_(a:blockseq.T, i:int)T
 assert between(i, 1, length.toseq.a)report"out of bounds"
  let blksz= length.dummy.a 
    let blk=load( a,(i - 1) / blksz + 2)
 blk_(toindex((i - 1) mod blksz + 1))

Function blockit3(s:seq.T)seq.T
let blksz = blocksize:T
 if length.s ≤ blksz then
    let newseq =  allocatespace (length.s   +2) 
   let d = for acc = set(set(newseq,  0 ) ,length.s) , @e = s do set (acc,  @e) /for(acc)
    bitcast:T(newseq)
 else
  let noblks =(length.s + blksz - 1) / blksz
 let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
    let blkseq=allocatespace(noblks+2)
  let discard = for acc = set(set(blkseq, blockseqtype), length.s), @e = arithseq(noblks, blksz, 1)do
        let newseq =  allocatespace ( blksz   +2) 
  let d = for acc2 = set(set(newseq, 0), blksz), e = subseq(s, @e, @e + blksz - 1)do
   set(acc2, e)
  /for(acc2)
     let x =bitcast:T(newseq)
    set (acc,   newseq) 
   /for(acc)
   bitcast:T(blkseq)

Function blockit2(s:seq.T, ds:int)seq.T
   assert ds > 1 report"blockit problem"  
 let blksz = blocksize:T / ds
  if length.s ≤ blksz then
   let newseq =  allocatespace (length.s * ds +2) 
   let d = for acc = set(set(newseq,  1),length.s) , @e = s do set (acc,  @e) /for(acc)
    bitcast:T(newseq)
  else 
   let noblks =(length.s + blksz - 1) / blksz
   let blockseqtype = getseqtype.toseq.blockseq(1, empty:seq.T)
   let blkseq=allocatespace(noblks+2)
   let discard = for acc = set(set(blkseq, blockseqtype), length.s), @e = arithseq(noblks, blksz, 1)do
        let s2=subseq(s, @e, @e + blksz - 1)
       let newseq =  allocatespace(length.s2 * ds+2)
       let d = for acc2 = set(set(newseq,  1),length.s) , e=s2 do set (acc2,  @e) /for(acc2)
        set (acc,   newseq) 
   /for(acc)
   bitcast:T(blkseq)
   
module tausupport

use bits


use real

use standard

use seq.byte

use taublockseq.byte

use seq.int

use taublockseq.int

use taublockseq.packed2

use taublockseq.packed3

use taublockseq.packed4

use taublockseq.packed5

use taublockseq.packed6

use taublockseq.ptr

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

Export type:ptr

Builtin set(ptr,int) ptr 

Builtin set(ptr,ptr) ptr 
 
Builtin allocatespace(int) ptr

Builtin getseqtype(ptr)int

Builtin getseqlength(ptr)int

Builtin toseqX:seq.int(ptr)seq.int

Export_(pseq.byte, int)byte

Export_(pseq.byte, int)byte

function set (i:ptr ,b:real)  ptr     set(i,representation.b)

function set (i:ptr ,b:packed2)  ptr   set (set (i ,fld1.b), fld2.b)  

function set (i:ptr ,b:packed3)  ptr  set(set (set (i ,fld1.b), fld2.b) ,fld3.b)

function set(i:ptr, b:packed4)ptr
 set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b)

function set(i:ptr, b:packed5)ptr
 set(set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b), fld5.b)

function set(i:ptr, b:packed6)ptr
 set(set(set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b), fld5.b), fld6.b)

Function blockIt(s:seq.int)seq.int  blockit3.s

Function blockIt(s:seq.ptr)seq.ptr blockit3.s

Function blockIt(s:seq.real)seq.real blockit3.s

Function blockIt(s:seq.packed2)seq.packed2 blockit2(s, 2)

Function blockIt(s:seq.packed3)seq.packed3 blockit2(s, 3)

Function blockIt(s:seq.packed4)seq.packed4 blockit2(s, 4)

Function blockIt(s:seq.packed5)seq.packed5 blockit2(s, 5)

Function blockIt(s:seq.packed6)seq.packed6 blockit2(s, 6)

/Export_(blockseq.int, int)int

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

function assignencoding( p:seq.encodingpair.typename,a:typename)int   length.p +1

-----------

use fileio

use mangle

use process.int

Builtin initialdict seq.encodingpair.seq.char

builtin dlsymbol(cstr)int

Builtin createthread(int, int, int, seq.int, int)process.int

Builtin createthread(int, int, int, ptr, int)process.int

builtin callstack(n:int)seq.int

builtin addresstosymbol2(a:int)seq.char

Builtin randomint(i:int)seq.int

Function dlsymbol(name:word)int dlsymbol.tocstr.[ name]

Function outofbounds seq.word "out of bounds"+stacktrace

Function stacktrace seq.word for acc ="", @e = callstack.30 << 2 do acc + " /br" + printmangled.addresstosymbol.@e /for(acc)

Function addresstosymbol(a:int)word encodeword.addresstosymbol2.a