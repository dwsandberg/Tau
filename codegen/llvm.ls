Module llvm

In addition to the llvm bitcode format documentation, an useful file for reference is LLVMBitCodes.h

use UTF8

use seq.seq.int

use encoding.llvmconst

use llvmconstants

use seq.llvmtype

use encoding.llvmtypeele

use seq.slot

use seq.slotrecord

use standard

Export slot(int) slot

Export type:llvmconst

Export type:llvmtype

Export typ(llvmtype) int

Export type:llvmtypeele

Export type:slot

Export toint(slot) int

Export type:slotrecord

type llvmtypeele is toseq:seq.int

type llvmtype is typ:int

function asseq(t:llvmtype) seq.int toseq.decode.to:encoding.llvmtypeele(typ.t + 1)

Function returntype(func:llvmtype) llvmtype llvmtype.(asseq.func)_3

Function llvmtype(s:seq.int) llvmtype llvmtype(addorder.llvmtypeele.s - 1)

function inttollvmtype(i:int) llvmtype llvmtype.i

function hash(a:llvmtypeele) int hash.toseq.a

function =(a:llvmtypeele, b:llvmtypeele) boolean toseq.a = toseq.b

Function %(t:llvmtype) seq.word
let a = asseq.t
let tp = typeop.a_1
let b = for acc = empty:seq.llvmtype, @e ∈ a do acc + inttollvmtype.@e /for (acc)
if tp = INTEGER then
 [merge("i" + toword.a_2)]
else if tp = ARRAY then
 "array (" + toword.a_2 + "," + %.b_3 + ")"
else if tp = POINTER then
 "ptr.$(b_2)"
else if tp = FUNCTION then
 "function ($(for acc = "", @e ∈ subseq(b, 3, length.a) do
  acc + %.@e + ",
   "
 /for (acc >> 1)))"
else if tp = TVOID then "VOID" else if tp = DOUBLE then "double" else "?"

Function typerecords seq.seq.int
for acc = empty:seq.seq.int, @e ∈ encodingdata:llvmtypeele do acc + toseq.@e /for (acc)

Function double llvmtype llvmtype.[toint.DOUBLE]

Function i64 llvmtype llvmtype.[toint.INTEGER, 64]

Function i32 llvmtype llvmtype.[toint.INTEGER, 32]

Function i8 llvmtype llvmtype.[toint.INTEGER, 8]

Function i1 llvmtype llvmtype.[toint.INTEGER, 1]

Function VOID llvmtype llvmtype.[toint.TVOID]

Function array(size:int, base:llvmtype) llvmtype llvmtype.[toint.ARRAY, size, typ.base]

Function ptr(base:llvmtype) llvmtype llvmtype.[toint.POINTER, typ.base, 0]

Function function(para:seq.llvmtype) llvmtype
llvmtype.for acc = [toint.FUNCTION, 0], @e ∈ para do acc + typ.@e /for (acc)

type llvmconst is typ:int, toseq:seq.int

function hash(a:llvmconst) int hash.symtabname.a

Function =(a:llvmconst, b:llvmconst) boolean
symtabname.a = symtabname.b ∧ typ.a = typ.b

function symtabname(a:llvmconst) seq.int
if typ.a ∈ [-1,-2] then subseq(toseq.a, 2, 1 + (toseq.a)_1) else toseq.a

Function modulerecord(name:seq.word, rec:seq.int) slot
let c = 
 if name = "" then
  llvmconst(-3, rec)
 else
  let chars = tointseq.for acc = empty:seq.char, @e ∈ name do acc + decodeword.@e /for (acc)
  llvmconst(-1, [length.chars] + chars + rec)
slot(addorder.c - 1)

Function C64(i:int) slot slot(addorder.llvmconst(typ.i64, [toint.CINTEGER, i]) - 1)

Function C32(i:int) slot slot(addorder.llvmconst(typ.i32, [toint.CINTEGER, i]) - 1)

function C(t:llvmtype, s:seq.int) int addorder.llvmconst(typ.t, s) - 1

Function constantrecord(t:llvmtype, s:seq.int) slot
slot(addorder.llvmconst(typ.t, s) - 1)

Function DATA(t:llvmtype, data:seq.int) slot
slot(addorder.llvmconst(typ.t, [toint.CDATA] + data) - 1)

Function AGGREGATE(data:seq.slot) slot
let t = array(length.data, i64)
slot(addorder.llvmconst(typ.t
 , [toint.CAGGREGATE] + for acc = empty:seq.int, @e ∈ data do acc + toint.@e /for (acc))
- 1)

Function ptrtoint(argtype:llvmtype, p:slot) slot
slot.C(i64, [toint.CCAST, 9, typ.argtype, toint.p])

Function CGEP(p:slot, b:int) slot
let t1 = consttype.p
slot.C(ptr.i64
 , [toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.i32, toint.C32.0, typ.i64, toint.C64.b])

Function CGEPi8(p:slot, b:int) slot
let t1 = consttype.p
slot.C(ptr.i8
 , [toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.i32, toint.C32.0, typ.i64, toint.C64.b])

/Function zeroinit (profiletype:llvmtype) int C (profiletype, [toint, CNULL])

Function Creal(i:int) slot slot.C(double, [toint.CCAST, 11, typ.i64, toint.C64.i])

Function asi64(s:slot) slot
let l = decode.to:encoding.llvmconst(toint.s + 1)
if typ.l = typ.i64 then
 s
else if typ.l = typ.ptr.i64 then
 constantrecord(i64, [toint.CCAST, toint.ptrtoint, typ.ptr.i64, toint.s])
else
 assert subseq(toseq.l, 1, 3) = [toint.CCAST, toint.bitcast, typ.i64]
 report "asi64 problem $(typ.l) $(stacktrace)"
 slot.(toseq.l)_4

Function constvalue(i:slot) int (toseq.decode.to:encoding.llvmconst(toint.i + 1))_2

Function constantrecords seq.slotrecord
for acc = empty:seq.slotrecord, @e ∈ encodingdata:llvmconst do acc + slotrecord.@e /for (acc)

type slotrecord is tollvmconst:llvmconst

Function record(b:slotrecord) seq.int
let a = tollvmconst.b
if typ.a = -1 then
 {name comes before record} subseq(toseq.a, 2 + (toseq.a)_1, length.toseq.a)
else
 toseq.a

Function symtablename(c:slotrecord) seq.char
let a = tollvmconst.c
if typ.a ∈ [-1,-2] then
 tocharseq.subseq(toseq.a, 2, 1 + (toseq.a)_1)
else
 empty:seq.char

Function ismoduleblock(a:slotrecord) boolean typ.tollvmconst.a < 0

Function typ(s:slotrecord) int typ.tollvmconst.s

Function consttype(s:slot) llvmtype
let l = decode.to:encoding.llvmconst(toint.s + 1)
inttollvmtype.if typ.l = -1 then
 ({must skip name to find record} toseq.l)_(3 + (toseq.l)_1)
else if typ.l = -3 then (toseq.l)_2 else typ.l

type slot is toint:int

Function r(a:int) slot slot.-a 