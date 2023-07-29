Module tausupport

use bits

use seq.bits

use bitcast.seq.bits

use seq.byte

use bitcast.seq.byte

use seq.seq.byte

use taublockseq.byte

use encoding.seq.char

use encodingsupport

use bitcast.int

use bitcast.seq.int

use taublockseq.int

use seq.packed2

use bitcast.seq.packed2

use taublockseq.packed2

use seq.packed3

use bitcast.seq.packed3

use taublockseq.packed3

use seq.packed4

use bitcast.seq.packed4

use taublockseq.packed4

use seq.packed5

use bitcast.seq.packed5

use taublockseq.packed5

use seq.packed6

use bitcast.seq.packed6

use taublockseq.packed6

use ptr

use bitcast.ptr

use seq.ptr

use bitcast.seq.ptr

use taublockseq.ptr

use real

use seq.real

use bitcast.seq.real

use taublockseq.real

use standard

use words

Export type:packed2

Export type:packed3

Export type:packed4

Export type:packed5

Export type:packed6

Export decode(encoding.seq.char) seq.char {From encoding.seq.char}

Export encode(seq.char) encoding.seq.char {From encoding.seq.char}

Export addencodings(seq.seq.char) int {From encoding.seq.char}

Export type:ptr {From ptr}

Export blockseqtype:byte int {From taublockseq.byte}

Export _(blockseq.int, int) int {From taublockseq.int}

Export blockseqtype:int int {From taublockseq.int}

Export _(blockseq.packed2, int) packed2 {From taublockseq.packed2}

Export _(blockseq.packed3, int) packed3 {From taublockseq.packed3}

Export _(blockseq.packed4, int) packed4 {From taublockseq.packed4}

Export _(blockseq.packed5, int) packed5 {From taublockseq.packed5}

Export _(blockseq.packed6, int) packed6 {From taublockseq.packed6}

Export _(blockseq.ptr, int) ptr {From taublockseq.ptr}

Export _(blockseq.real, int) real {From taublockseq.real}

type packed2 is fld1:int, fld2:int

type packed3 is fld1:int, fld2:int, fld3:int

type packed4 is fld1:int, fld2:int, fld3:int, fld4:int

type packed5 is fld1:int, fld2:int, fld3:int, fld4:int, fld5:int

type packed6 is fld1:int, fld2:int, fld3:int, fld4:int, fld5:int, fld6:int

Builtin getseqlength(ptr) int {OPTION COMPILETIME}

Builtin getseqtype(ptr) int {OPTION COMPILETIME}

function set2(i:ptr, b:real) ptr set(i, representation.b)

function set2(i:ptr, b:int) ptr set(i, b)

function set2(i:ptr, b:ptr) ptr set(i, b)

function set2(i:ptr, b:packed2) ptr set(set(i, fld1.b), fld2.b)

function set2(i:ptr, b:packed3) ptr set(set(set(i, fld1.b), fld2.b), fld3.b)

function set2(i:ptr, b:packed4) ptr set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b)

function set2(i:ptr, b:packed5) ptr
set(set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b), fld5.b)

function set2(i:ptr, b:packed6) ptr
set(set(set(set(set(set(i, fld1.b), fld2.b), fld3.b), fld4.b), fld5.b), fld6.b)

Function blockIt(s:seq.int) seq.int blockit3.s

Function blockIt(s:seq.ptr) seq.ptr blockit3.s

Function blockIt(s:seq.real) seq.real blockit3.s

Function blockIt(s:seq.packed2) seq.packed2 blockit2(s, 2)

Function blockIt(s:seq.packed3) seq.packed3 blockit2(s, 3)

Function blockIt(s:seq.packed4) seq.packed4 blockit2(s, 4)

Function blockIt(s:seq.packed5) seq.packed5 blockit2(s, 5)

Function blockIt(s:seq.packed6) seq.packed6 blockit2(s, 6)

Function deepcopy(a:int) int a

Function deepcopy(a:real) real a

Builtin abort:ptr(seq.word) ptr

Builtin abort:int(seq.word) int

Builtin abort:real(seq.word) real

Builtin abort:boolean(seq.word) boolean

Function outofbounds seq.word "out of bounds^(stacktrace)"

function packedbytes(a:seq.byte) seq.byte
let c = packed([bits.1, bits.n.a] + toseqbits.a)
assert getseqtype.c = 0 report "to big byte sequence to pack",
bitcast:seq.byte(set(set(toptr.c, getseqtype.c), n.c))

Function blockIt(s:seq.byte) seq.byte
let blksz = 8128 * 8,
if n.s ≤ blksz then
packedbytes.s
else
 let noblks = (n.s + blksz - 1) / blksz
 let blkseq = allocatespace(noblks + 2)
 let discard =
  for acc = set(set(blkseq, blockseqtype:byte), n.s), @e ∈ arithseq(noblks, blksz, 1)
  do set(acc, bitcast:int(toptr.packedbytes.subseq(s, @e, @e + blksz - 1))),
  acc
 ,
 bitcast:seq.byte(blkseq)

Function toseqseqbyte(b:seq.bits, bytestowrite:int) seq.seq.byte
let blksz = 8128
let noblks = (n.b + blksz - 1) / blksz
for acc = empty:seq.seq.byte, byteswritten ∈ arithseq(noblks, blksz * 8, 0)
do
 let new = packed(subseq(b, byteswritten / 8 + 1, byteswritten / 8 + blksz) + bits.0)
 let z = set(set(toptr.new, 1), min(bytestowrite - byteswritten, blksz * 8)),
 acc + bitcast:seq.byte(toptr.new)
,
acc

Function toseqseqbyte(s:seq.byte) seq.seq.byte
let blksz = 8128 * 8
let noblks = (n.s + blksz - 1) / blksz
for acc = empty:seq.seq.byte, start ∈ arithseq(noblks, blksz, 1)
do acc + packedbytes.subseq(s, start, start + blksz - 1),
acc

____________

Function cat(obj1:ptr, obj2:ptr, typ:word) ptr
if typ ∈ "int" then
toptr(bitcast:seq.int(obj1) + bitcast:seq.int(obj2))
else if typ ∈ "real" then
toptr(bitcast:seq.real(obj1) + bitcast:seq.real(obj2))
else if typ ∈ "ptr" then
toptr(bitcast:seq.ptr(obj1) + bitcast:seq.ptr(obj2))
else if typ ∈ "packed2" then
toptr(bitcast:seq.packed2(obj1) + bitcast:seq.packed2(obj2))
else if typ ∈ "packed3" then
toptr(bitcast:seq.packed3(obj1) + bitcast:seq.packed3(obj2))
else if typ ∈ "packed4" then
toptr(bitcast:seq.packed4(obj1) + bitcast:seq.packed4(obj2))
else if typ ∈ "packed5" then
toptr(bitcast:seq.packed5(obj1) + bitcast:seq.packed5(obj2))
else
 assert typ ∈ "packed6" report "packing cat not found" + typ,
 toptr(bitcast:seq.packed6(obj1) + bitcast:seq.packed6(obj2))

Function blocktype(typ:word) int
if typ ∈ "int" then
blockseqtype:int
else if typ ∈ "real" then
blockseqtype:real
else if typ ∈ "ptr" then
blockseqtype:int
else if typ ∈ "packed2" then
blockseqtype:packed2
else if typ ∈ "packed3" then
blockseqtype:packed3
else if typ ∈ "packed4" then
blockseqtype:packed4
else if typ ∈ "packed5" then
blockseqtype:packed5
else assert typ ∈ "packed6" report "packing not found" + typ, blockseqtype:packed6

Function packobject(typ:word, obj:ptr) ptr
if typ ∈ "int" then
toptr.blockIt.bitcast:seq.int(obj)
else if typ ∈ "real" then
toptr.blockIt.bitcast:seq.real(obj)
else if typ ∈ "ptr" then
toptr.blockIt.bitcast:seq.ptr(obj)
else if typ ∈ "packed2" then
toptr.blockIt.bitcast:seq.packed2(obj)
else if typ ∈ "packed3" then
toptr.blockIt.bitcast:seq.packed3(obj)
else if typ ∈ "packed4" then
toptr.blockIt.bitcast:seq.packed4(obj)
else if typ ∈ "packed5" then
toptr.blockIt.bitcast:seq.packed5(obj)
else
 assert typ ∈ "packed6" report "packing not found" + typ,
 toptr.blockIt.bitcast:seq.packed6(obj)

Export geteinfo(gl:ptr, name:seq.word) einfo {From encodingsupport}

Export geteinfo2(int, int) einfo {From encodingsupport}

Export type:einfo {From encodingsupport}

Export evectorUpdate(b:ptr) ptr {From encodingsupport}

builtin clock int

builtin spacecount int

Function profileUpdate(time:int, beforeSpace:int, p:ptr) int
let p1 = set(p, fld:int(p, 0) + 1)
let p2 = set(p1, fld:int(p1, 0) + (clock - time))
let p3 = set(p2, fld:int(p2, 0) + (spacecount - beforeSpace)),
0 