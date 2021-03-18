Module llvm

In addition to the llvm bitcode format documentation, an useful file for reference is LLVMBitCodes.h

use UTF8

use llvmconstants

use standard

use encoding.llvmconst

use seq.llvmconst

use otherseq.llvmtype

use encoding.llvmtypeele

use seq.llvmtypeele

use seq.slot

use seq.slotrecord

use seq.seq.int

use seq.encoding.llvmconst

use seq.encodingpair.llvmconst

use seq.encodingpair.llvmtypeele

use seq.seq.llvmtypeele

use seq.seq.seq.int

Export type:encodingpair.llvmconst

Export type:llvmtypeele

Export type:llvmtype

Export type:llvmconst

type llvmtypeele is toseq:seq.int

type llvmtype is index:encoding.llvmtypeele

function hash(a:llvmtypeele)int hash.toseq.a

Function assignencoding(l:int, a:llvmtypeele)int l + 1

function =(a:llvmtypeele, b:llvmtypeele)boolean toseq.a = toseq.b

function inttollvmtype(i:int)llvmtype llvmtype.to:encoding.llvmtypeele(i + 1)

Function print(t:llvmtype)seq.word
 let a = toseq.decode.index.t
 let tp = typeop.a_1
let b = for acc = empty:seq.llvmtype, @e = a do acc + inttollvmtype.@e /for(acc)
  if tp = INTEGER then [ merge("i" + toword.a_2)]
  else if tp = ARRAY then
  "array(" + toword.a_2 + "," + print.b_3 + ")"
  else if tp = POINTER then"ptr." + print.b_2
  else if tp = FUNCTION then
  "function("
  + for acc ="", @e = subseq(b, 3, length.a)do list(acc,",", print.@e)/for(acc)
   + ")"
  else if tp = TVOID then"VOID"else if tp = DOUBLE then"double"else"?"

function cvttorec(a:encodingpair.llvmtypeele)seq.int toseq.data.a

Function typerecords seq.seq.int for acc = empty:seq.seq.int, @e = encoding:seq.encodingpair.llvmtypeele do acc + cvttorec.@e /for(acc)

Function returntype(func:llvmtype)llvmtype llvmtype.to:encoding.llvmtypeele((toseq.decode.index.func)_3 + 1)

typerecords_(typ.llvmtype + 1)_3

Function typ(a:llvmtype)int valueofencoding.index.a - 1

Function llvmtype(s:seq.int)llvmtype llvmtype.encode.llvmtypeele.s

Function double llvmtype llvmtype.[ toint.DOUBLE]

Function i64 llvmtype llvmtype.[ toint.INTEGER, 64]

Function i32 llvmtype llvmtype.[ toint.INTEGER, 32]

Function i8 llvmtype llvmtype.[ toint.INTEGER, 8]

Function i1 llvmtype llvmtype.[ toint.INTEGER, 1]

Function VOID llvmtype llvmtype.[ toint.TVOID]

Function array(size:int, base:llvmtype)llvmtype llvmtype.[ toint.ARRAY, size, typ.base]

Function ptr(base:llvmtype)llvmtype llvmtype.[ toint.POINTER, typ.base, 0]

Function function(para:seq.llvmtype)llvmtype
 llvmtype.for acc = [ toint.FUNCTION, 0], @e = para do acc + typ.@e /for(acc)

-------------------------

type llvmconst is typ:int, toseq:seq.int

function hash(a:llvmconst)int hash.symtabname.a

Function assignencoding(l:int, a:llvmconst)int l + 1

Function =(a:llvmconst, b:llvmconst)boolean symtabname.a = symtabname.b ∧ typ.a = typ.b

function symtabname(a:llvmconst)seq.int
 if typ.a ∈ [-1,-2]then subseq(toseq.a, 2, 1 + (toseq.a)_1)
 else toseq.a

Function modulerecord(name:seq.word, rec:seq.int)slot
 let c = if name = ""then llvmconst(-3, rec)
 else
 let chars = tointseq.for acc = empty:seq.char, @e = name do acc + decodeword.@e /for(acc)
   llvmconst(-1, [ length.chars] + chars + rec)
  slot(valueofencoding.encode.c - 1)

Function C64(i:int)slot slot(valueofencoding.encode.llvmconst(typ.i64, [ toint.CINTEGER, i]) - 1)

Function C32(i:int)slot slot(valueofencoding.encode.llvmconst(typ.i32, [ toint.CINTEGER, i]) - 1)

function C(t:llvmtype, s:seq.int)int valueofencoding.encode.llvmconst(typ.t, s) - 1

Function constantrecord(t:llvmtype, s:seq.int)slot slot(valueofencoding.encode.llvmconst(typ.t, s) - 1)

Function DATA(t:llvmtype, data:seq.int)slot
 slot(valueofencoding.encode.llvmconst(typ.t, [ toint.CDATA] + data) - 1)

Function AGGREGATE(data:seq.slot)slot
 let t = array(length.data, i64)
 slot(valueofencoding.encode.llvmconst(typ.t, [ toint.CAGGREGATE]
 + for acc = empty:seq.int, @e = data do acc + toint.@e /for(acc))
  - 1)

Function ptrtoint(argtype:llvmtype, p:slot)slot slot.C(i64, [ toint.CCAST, 9, typ.argtype, toint.p])

Function CGEP(p:slot, b:int)slot
 let t1 =  consttype.p
  slot.C(ptr.i64
 , [ toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.i32, toint.C32.0, typ.i64, toint.C64.b]
 )

Function CGEPi8(p:slot, b:int)slot
 let t1 = consttype.p
  slot.C(ptr.i8
 , [ toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.i32, toint.C32.0, typ.i64, toint.C64.b]
 )

/Function zeroinit(profiletype:llvmtype)int C(profiletype, [ toint, CNULL])

Function Creal(i:int)slot slot.C(double, [ toint.CCAST, 11, typ.i64, toint.C64.i])

Function asi64(s:slot)slot
 let l = decode.to:encoding.llvmconst(toint.s + 1)
  if typ.l = typ.i64 then s
  else if typ.l = typ.ptr.i64 then
  constantrecord(i64, [ toint.CCAST, toint.ptrtoint, typ.ptr.i64, toint.s])
  else
   assert subseq(toseq.l, 1, 3) = [ toint.CCAST, toint.bitcast, typ.i64]report"asi64 problem"
    slot.(toseq.l)_4

Function constvalue(i:slot)int(toseq.decode.to:encoding.llvmconst(toint.i + 1))_2

Function constantrecords seq.slotrecord for acc = empty:seq.slotrecord, @e = encoding:seq.encodingpair.llvmconst do acc + slotrecord.@e /for(acc)

type slotrecord is cvt:encodingpair.llvmconst

Export type:slotrecord

Function record(b:slotrecord)seq.int
 let a = data.cvt.b
  if typ.a = -1 then
  { name comes before record } subseq(toseq.a, 2 + (toseq.a)_1, length.toseq.a)
  else toseq.a

Function symtablename(c:slotrecord)seq.char
 let b = cvt.c
 let a = data.b
  if typ.a ∈ [-1,-2]then
  tocharseq.subseq(toseq.a, 2, 1 + (toseq.a)_1)
  else empty:seq.char

Function ismoduleblock(a:slotrecord)boolean typ.data.cvt.a < 0

Function typ(s:slotrecord)int typ.data.cvt.s

Function consttype(s:slot)llvmtype
  { pretty print get prec wrong comment? }
 let l = decode.to:encoding.llvmconst(toint.s + 1)
  llvmtype.to:encoding.llvmtypeele(1
  + if typ.l = -1 then { must skip name to find record } (toseq.l)_(3 + (toseq.l)_1)
  else if typ.l = -3 then(toseq.l)_2 else typ.l)

type slot is toint:int

Export toint(slot)int

Export slot(int)slot

Export type:slot

Function r(a:int)slot slot.-a