module tausupport

use bits

use bitstream

use real

use standard

use seq.bits

use seq.byte

use taublockseq.byte

use bitcast.dummyrec2

use seq.index

use bitcast.int

use process.int

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

use seq.word

use bitcast.seq.bits

use bitcast.seq.byte

use encoding.seq.char

use bitcast.seq.int

use seq.seq.int

Export empty:seq.index seq.index

Export+(seq.index, index)seq.index

Export blockseqtype:int int

Export blockseqtype:byte int

Export_(seq.word, index)word

type packed2 is fld1:int, fld2:int

type packed3 is fld1:int, fld2:int, fld3:int

type packed4 is fld1:int, fld2:int, fld3:int, fld4:int

type packed5 is fld1:int, fld2:int, fld3:int, fld4:int, fld5:int

type packed6 is fld1:int, fld2:int, fld3:int, fld4:int, fld5:int, fld6:int

type ptr is xx:int

Export type:ptr

Export type:packed2

Export type:packed3

Export type:packed4

Export type:packed5

Export type:packed6

Export type:typename

Export_(blockseq.packed2, int)packed2

Export_(blockseq.packed3, int)packed3

Export_(blockseq.packed4, int)packed4

Export_(blockseq.packed5, int)packed5

Export_(blockseq.packed6, int)packed6

Export_(blockseq.int, int)int

Export_(blockseq.ptr, int)ptr

Export_(blockseq.real, int)real

Builtin set(ptr, int)ptr

Builtin set(ptr, ptr)ptr

Builtin allocatespace(int)ptr

Builtin getseqtype(ptr)int

Builtin getseqlength(ptr)int{OPTION COMPILETIME}

/Export_(pseq.byte, int)byte

/Export_(pseq.byte, int)byte

function set(i:ptr, b:real)ptr set(i, representation.b)

function set(i:ptr, b:packed2)ptr set(set(i, fld1.b), fld2.b)

function set(i:ptr, b:packed3)ptr set(set(set(i, fld1.b), fld2.b), fld3.b)

function set(i:ptr, b:packed4)ptr set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b)

function set(i:ptr, b:packed5)ptr set(set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b), fld5.b)

function set(i:ptr, b:packed6)ptr
set(set(set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b), fld5.b), fld6.b)

Function blockIt(s:seq.int)seq.int blockit3.s

Function blockIt(s:seq.ptr)seq.ptr blockit3.s

Function blockIt(s:seq.real)seq.real blockit3.s

Function blockIt(s:seq.packed2)seq.packed2 blockit2(s, 2)

Function blockIt(s:seq.packed3)seq.packed3 blockit2(s, 3)

Function blockIt(s:seq.packed4)seq.packed4 blockit2(s, 4)

Function blockIt(s:seq.packed5)seq.packed5 blockit2(s, 5)

Function blockIt(s:seq.packed6)seq.packed6 blockit2(s, 6)

Export decode(encoding.seq.char)seq.char

Export encode(seq.char)encoding.seq.char

Function deepcopy(a:int)int a

Function deepcopy(a:real)real a

type typename is name:seq.word

function =(a:typename, b:typename)boolean name.a = name.b

function hash(a:typename)int hash.name.a

Function encodingno(name:seq.word)int addorder.typename.name + 2

function assignencoding(a:typename)int nextencoding.a

Builtin abort:ptr(seq.word)ptr

Builtin abort:int(seq.word)int

Builtin abort:real(seq.word)real

Builtin abort:boolean(seq.word)boolean

Export type:encodingpair.seq.char

Export type:encodingpair.typename

-----------

Function outofbounds seq.word"out of bounds" +stacktrace2

function packedbytes(a:seq.byte)seq.byte
let b = packedbyteseqasbits.a
bitcast:seq.byte(set(set(toptr.b, getseqtype.b), length.b))

Function packedbyteseqasbits(a:seq.byte)seq.bits
let b = 
 packed([bits.1, bits.length.a]
 + bits.for acc = empty:bitstream, @e ∈ a do add(acc, bits.toint.@e, 8)/for(acc))
assert getseqtype.b = 0 report"to big byte sequence to pack"
b

Function blockIt(s:seq.byte)seq.byte
let blksz = 64000
if length.s ≤ blksz then packedbytes.s
else
 let noblks = (length.s + blksz - 1) / blksz
 let blkseq = allocatespace(noblks + 2)
 let discard = 
  for acc = set(set(blkseq, blockseqtype:byte), length.s), @e ∈ arithseq(noblks, blksz, 1)do
   set(acc, bitcast:int(toptr.packedbytes.subseq(s, @e, @e + blksz - 1)))
  /for(acc)
 bitcast:seq.byte(blkseq)
 
 Function    toseqseqbyte(t:bitstream)  seq.seq.byte 
      let blksz=8128
      let b=bits.t
       let noblks = (length.b + blksz - 1) / blksz
      let  bytestowrite= (length.t+7) / 8
        for acc=empty:seq.seq.byte, byteswritten /in arithseq(noblks,blksz * 8,0) do
          let new=  packed(subseq(b,byteswritten / 8 +1 , byteswritten / 8 +blksz  )+bits.0)
         { assert false report for txt="",i /in new do txt+print.i /for(txt)}
          let z=set(set(toptr.new, 1), min(bytestowrite-byteswritten ,blksz * 8))
          let x=bitcast:seq.byte( toptr.new )
         acc+x
        /for(acc)
        
use seq.seq.byte

___________

Function createthread(adcret:int, adc:int, funcaddress:int, args:seq.int, argcode:int)process.int
createthread(adcret, adc, funcaddress, c.bitcast:dummyrec2(toptr.packed.args), argcode)

type dummyparameterrecord is a:int, b:int

type dummyrec2 is a:int, b:int, c:dummyparameterrecord

builtin createthread(int, int, int, dummyparameterrecord, int)process.int 