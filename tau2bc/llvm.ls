Module llvm

In addition to the llvm bitcode format documentation, an useful files for reference are LLVMBitCodes.h and https://llvm.org/LICENSE.txt.

llvm-bcanalyzer is useful for examining a generated bitcode file that will not disassemble using llvm-dis because of errors.

use UTF8

use seq.seq.int

use seq.llvmtype

use encoding.llvmtypeele

use seq.slot

use encoding.slotrecord

use seq.slotrecord

use standard

Export type:align

Export toint(align) int

Export type:binaryop

Export toint(binaryop) int

Export type:blockop

Export toint(blockop) int

Export type:castop

Export toint(castop) int

Export type:cmp2op

Export toint(cmp2op) int

Export type:constop

Export toint(constop) int

Export type:instop

Export toint(instop) int

Export align(i:int) align

Export binaryop(i:int) binaryop

Export blockop(i:int) blockop

Export castop(i:int) castop

Export cmp2op(i:int) cmp2op

Export constop(i:int) constop

Export instop(i:int) instop

Export llvmtype(int) llvmtype

Export moduleop(i:int) moduleop

Export slot(int) slot

Export typeop(i:int) typeop

Export type:llvmtype

Export typ(llvmtype) int

Export type:llvmtypeele

Export type:moduleop

Export toint(moduleop) int

Export type:slot

Export toint(slot) int

Export type:slotrecord

Export typ(s:slotrecord) int

Export type:typeop

Export toint(typeop) int

type llvmtypeele is toseq:seq.int

type llvmtype is typ:int

function asseq(t:llvmtype) seq.int toseq.decode.to:encoding.llvmtypeele(typ.t + 1)

Function returntype(func:llvmtype) llvmtype llvmtype.3#asseq.func

Function llvmtype(s:seq.int) llvmtype llvmtype(addorder.llvmtypeele.s - 1)

function hash(a:llvmtypeele) int hash.toseq.a

function =(a:llvmtypeele, b:llvmtypeele) boolean toseq.a = toseq.b

Function %(t:llvmtype) seq.word
let a = asseq.t
let tp = typeop.1#a
let b =
 for acc = empty:seq.llvmtype, @e ∈ a do acc + llvmtype.@e,
 acc,
if tp = INTEGER then [merge("i" + toword.2#a)]
else if tp = ARRAY then "array (" + toword.2#a + "," + %.3#b + ")"
else if tp = POINTER then "ptr.^(2#b)"
else if tp = FUNCTION then
 "function (^(for acc = "", @e ∈ subseq(b, 3, n.a)
 do acc + %.@e + ",",
 acc >> 1))"
else if tp = TVOID then "VOID"
else if tp = DOUBLE then "double"
else "?"

Function typerecords seq.seq.int
for acc = empty:seq.seq.int, @e ∈ encodingdata:llvmtypeele
do acc + toseq.@e,
acc

Function double llvmtype llvmtype.[toint.DOUBLE]

Function i64 llvmtype llvmtype.[toint.INTEGER, 64]

Function i32 llvmtype llvmtype.[toint.INTEGER, 32]

Function i8 llvmtype llvmtype.[toint.INTEGER, 8]

Function i1 llvmtype llvmtype.[toint.INTEGER, 1]

Function VOID llvmtype llvmtype.[toint.TVOID]

Function array(size:int, base:llvmtype) llvmtype llvmtype.[toint.ARRAY, size, typ.base]

Function ptr(base:llvmtype) llvmtype llvmtype.[toint.POINTER, typ.base, 0]

Function function(para:seq.llvmtype) llvmtype
for acc = [toint.FUNCTION, 0], @e ∈ para do acc + typ.@e,
llvmtype.acc

type slotrecord is typ:int, toseq:seq.int

function hash(a:slotrecord) int hash.symtabname.a

Function =(a:slotrecord, b:slotrecord) boolean symtabname.a = symtabname.b ∧ typ.a = typ.b

function symtabname(a:slotrecord) seq.int
if typ.a ∈ [-1,-2] then subseq(toseq.a, 2, 1 + 1#toseq.a) else toseq.a

Function modulerecord(name:seq.word, rec:seq.int) slot
let c =
 if name = "" then slotrecord(-3, rec)
 else
  let chars =
   for acc = empty:seq.char, @e ∈ name do acc + decodeword.@e,
   tointseq.acc,
  slotrecord(-1, [n.chars] + chars + rec),
slot(addorder.c - 1)

Function %(slot:slot) seq.word
if between(toint.slot, 0, n.encodingdata:slotrecord) then
 let llvmConst = decode.to:encoding.slotrecord(toint.slot + 1),
 if 1#toseq.llvmConst = toint.CINTEGER then %.2#toseq.llvmConst
 else "{^(toint.slot)}"
else "{^(toint.slot)}"

Function dumpslots seq.word
for acc = "", i ∈ arithseq(n.encodingdata:slotrecord, 1, 0)
do acc + (%.i + ":" + %.slot.i + "/br"),
acc

Function C64(i:int) slot slot(addorder.slotrecord(typ.i64, [toint.CINTEGER, i]) - 1)

Function C32(i:int) slot slot(addorder.slotrecord(typ.i32, [toint.CINTEGER, i]) - 1)

function C(t:llvmtype, s:seq.int) int addorder.slotrecord(typ.t, s) - 1

Function constantrecord(t:llvmtype, s:seq.int) slot
slot(addorder.slotrecord(typ.t, s) - 1)

Function DATA(t:llvmtype, data:seq.int) slot
slot(addorder.slotrecord(typ.t, [toint.CDATA] + data) - 1)

Function AGGREGATE(data:seq.slot) slot
let t = array(n.data, i64),
slot(
 addorder.slotrecord(
  typ.t
  , [toint.CAGGREGATE]
   + for acc = empty:seq.int, @e ∈ data do acc + toint.@e,
  acc
 )
  - 1
)

Function ptrtoint(argtype:llvmtype, p:slot) slot
slot.C(i64, [toint.CCAST, 9, typ.argtype, toint.p])

Function CGEP(p:slot, b:int) slot
let t1 = consttype.p,
slot.C(
 ptr.i64
 , [toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.i32, toint.C32.0, typ.i64, toint.C64.b]
)

Function CGEPi8(p:slot, b:int) slot
let t1 = consttype.p,
slot.C(
 ptr.i8
 , [toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.i32, toint.C32.0, typ.i64, toint.C64.b]
)

/Function zeroinit (profiletype:llvmtype) int C (profiletype, [toint, CNULL])

Function Creal(i:int) slot slot.C(double, [toint.CCAST, 11, typ.i64, toint.C64.i])

Function asi64(s:slot) slot
let l = decode.to:encoding.slotrecord(toint.s + 1),
if typ.l = typ.i64 then s
else if typ.l = typ.ptr.i64 then constantrecord(i64, [toint.CCAST, toint.ptrtoint, typ.ptr.i64, toint.s])
else
 assert subseq(toseq.l, 1, 3) = [toint.CCAST, toint.bitcast, typ.i64] report "asi64 problem^(typ.l)^(stacktrace)",
 slot.4#toseq.l

Function constvalue(i:slot) int 2#toseq.decode.to:encoding.slotrecord(toint.i + 1)

Function constantrecords seq.slotrecord encodingdata:slotrecord

Function record(a:slotrecord) seq.int
if typ.a =-1 then {name comes before record} subseq(toseq.a, 2 + 1#toseq.a, n.toseq.a)
else toseq.a

Function symtablename(a:slotrecord) seq.char
if typ.a ∈ [-1,-2] then tocharseq.subseq(toseq.a, 2, 1 + 1#toseq.a)
else empty:seq.char

Function ismoduleblock(a:slotrecord) boolean typ.a < 0

Function consttype(s:slot) llvmtype
let l = decode.to:encoding.slotrecord(toint.s + 1),
llvmtype(
 if typ.l =-1 then {must skip name to find record} (3 + 1#toseq.l)#toseq.l
 else if typ.l =-3 then 2#toseq.l
 else typ.l
)

type slot is toint:int

Function r(a:int) slot slot.-a

function unused int
let a = decode.MODULE + decode.SETTYPE + decode.MODULE + decode.TVOID
let b = VOID
let c = align8 = align8 ∨ add = add ∨ trunc = trunc ∨ MODULE = MODULE ∨ CNULL = CNULL ∨ Feq = Feq,
0

function genEnum seq.seq.word
[
 "newType: align values: unspecified ? ? ? align8 align16 align32 align64"
 , "newType: instop values: ? BLOCK BINOP CAST ? SELECT ? ? ? ? RET BR SWITCH ? ? ? PHI ? ? ALLOCA LOAD ? ? ? ? ? ? ? CMP2 ? ? ? ? ? CALL ? ? ? ? ? ? ? ? GEP STORE"
 , "newType: typeop values: ? NumEle TVOID ? DOUBLE ? OPAQUE INTEGER POINTER ? ? ARRAY ? ? ? ? ? ? ? ? ? FUNCTION"
 , "newType: blockop values: INFOBLOCK ? ? ? ? ? ? ? MODULE PARA PARAGRP CONSTANTS FUNCTIONBLK ? VALUESYMTABLE ? ? TYPES"
 , "newType: moduleop values: ? Version TRIPLE LAYOUT ? ? ? GLOBALVAR FUNCTIONDEC"
 , "newType: constop values: ? SETTYPE CNULL CUNDEF CINTEGER CWIDEINTEGER CFLOAT CAGGREGATE CSTRING2 CSTRING0 CBINOP CCAST ? ? ? ? ? ? ? ? CGEP ? CDATA"
 , "newType: castop values: trunc zext sext fptoui fptosi uitofp sitofp fptrunc fpext ptrtoint inttoptr bitcast"
 , "newType: binaryop values: add sub mul udiv sdiv urem srem shl lshr ashr and or xor"
 , "newType: cmp2op values: ? Feq Fgt Fge Flt Fle Fne ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? eq ne ugt uge ult ule sgt sge slt sle"
]

<<<< Below is auto generated code >>>>

type align is toint:int

Export toint(align) int

Export align(i:int) align

Export type:align

Function =(a:align, b:align) boolean toint.a = toint.b

Function unspecified align align.0

Function align8 align align.4

Function align16 align align.5

Function align32 align align.6

Function align64 align align.7

Function decode(code:align) seq.word
let discard = [unspecified, align8, align16, align32, align64]
let i = toint.code,
if between(i + 1, 1, 8) then
 let r = [(i + 1)#"unspecified ? ? ? align8 align16 align32 align64"],
 if r ≠ "?" then r else "align." + toword.i
else "align." + toword.i

type instop is toint:int

Export toint(instop) int

Export instop(i:int) instop

Export type:instop

Function =(a:instop, b:instop) boolean toint.a = toint.b

Function BLOCK instop instop.1

Function BINOP instop instop.2

Function CAST instop instop.3

Function SELECT instop instop.5

Function RET instop instop.10

Function BR instop instop.11

Function SWITCH instop instop.12

Function PHI instop instop.16

Function ALLOCA instop instop.19

Function LOAD instop instop.20

Function CMP2 instop instop.28

Function CALL instop instop.34

Function GEP instop instop.43

Function STORE instop instop.44

Function decode(code:instop) seq.word
let discard =
 [
  BLOCK
  , BINOP
  , CAST
  , SELECT
  , RET
  , BR
  , SWITCH
  , PHI
  , ALLOCA
  , LOAD
  , CMP2
  , CALL
  , GEP
  , STORE
 ]
let i = toint.code,
if between(i + 1, 1, 45) then
 let r =
  [
   (i + 1)
   #"? BLOCK BINOP CAST ? SELECT ? ? ? ? RET BR SWITCH ? ? ? PHI ? ? ALLOCA LOAD ? ? ? ? ? ? ? CMP2 ? ? ? ? ? CALL ? ? ? ? ? ? ? ? GEP STORE"
  ],
 if r ≠ "?" then r else "instop." + toword.i
else "instop." + toword.i

type typeop is toint:int

Export toint(typeop) int

Export typeop(i:int) typeop

Export type:typeop

Function =(a:typeop, b:typeop) boolean toint.a = toint.b

Function NumEle typeop typeop.1

Function TVOID typeop typeop.2

Function DOUBLE typeop typeop.4

Function OPAQUE typeop typeop.6

Function INTEGER typeop typeop.7

Function POINTER typeop typeop.8

Function ARRAY typeop typeop.11

Function FUNCTION typeop typeop.21

Function decode(code:typeop) seq.word
let discard = [NumEle, TVOID, DOUBLE, OPAQUE, INTEGER, POINTER, ARRAY, FUNCTION]
let i = toint.code,
if between(i + 1, 1, 22) then
 let r =
  [
   (i + 1)
   #"? NumEle TVOID ? DOUBLE ? OPAQUE INTEGER POINTER ? ? ARRAY ? ? ? ? ? ? ? ? ? FUNCTION"
  ],
 if r ≠ "?" then r else "typeop." + toword.i
else "typeop." + toword.i

type blockop is toint:int

Export toint(blockop) int

Export blockop(i:int) blockop

Export type:blockop

Function =(a:blockop, b:blockop) boolean toint.a = toint.b

Function INFOBLOCK blockop blockop.0

Function MODULE blockop blockop.8

Function PARA blockop blockop.9

Function PARAGRP blockop blockop.10

Function CONSTANTS blockop blockop.11

Function FUNCTIONBLK blockop blockop.12

Function VALUESYMTABLE blockop blockop.14

Function TYPES blockop blockop.17

Function decode(code:blockop) seq.word
let discard = [INFOBLOCK, MODULE, PARA, PARAGRP, CONSTANTS, FUNCTIONBLK, VALUESYMTABLE, TYPES]
let i = toint.code,
if between(i + 1, 1, 18) then
 let r =
  [
   (i + 1)
   #"INFOBLOCK ? ? ? ? ? ? ? MODULE PARA PARAGRP CONSTANTS FUNCTIONBLK ? VALUESYMTABLE ? ? TYPES"
  ],
 if r ≠ "?" then r else "blockop." + toword.i
else "blockop." + toword.i

type moduleop is toint:int

Export toint(moduleop) int

Export moduleop(i:int) moduleop

Export type:moduleop

Function =(a:moduleop, b:moduleop) boolean toint.a = toint.b

Function Version moduleop moduleop.1

Function TRIPLE moduleop moduleop.2

Function LAYOUT moduleop moduleop.3

Function GLOBALVAR moduleop moduleop.7

Function FUNCTIONDEC moduleop moduleop.8

Function decode(code:moduleop) seq.word
let discard = [Version, TRIPLE, LAYOUT, GLOBALVAR, FUNCTIONDEC]
let i = toint.code,
if between(i + 1, 1, 9) then
 let r = [(i + 1)#"? Version TRIPLE LAYOUT ? ? ? GLOBALVAR FUNCTIONDEC"],
 if r ≠ "?" then r else "moduleop." + toword.i
else "moduleop." + toword.i

type constop is toint:int

Export toint(constop) int

Export constop(i:int) constop

Export type:constop

Function =(a:constop, b:constop) boolean toint.a = toint.b

Function SETTYPE constop constop.1

Function CNULL constop constop.2

Function CUNDEF constop constop.3

Function CINTEGER constop constop.4

Function CWIDEINTEGER constop constop.5

Function CFLOAT constop constop.6

Function CAGGREGATE constop constop.7

Function CSTRING2 constop constop.8

Function CSTRING0 constop constop.9

Function CBINOP constop constop.10

Function CCAST constop constop.11

Function CGEP constop constop.20

Function CDATA constop constop.22

Function decode(code:constop) seq.word
let discard =
 [
  SETTYPE
  , CNULL
  , CUNDEF
  , CINTEGER
  , CWIDEINTEGER
  , CFLOAT
  , CAGGREGATE
  , CSTRING2
  , CSTRING0
  , CBINOP
  , CCAST
  , CGEP
  , CDATA
 ]
let i = toint.code,
if between(i + 1, 1, 23) then
 let r =
  [
   (i + 1)
   #"? SETTYPE CNULL CUNDEF CINTEGER CWIDEINTEGER CFLOAT CAGGREGATE CSTRING2 CSTRING0 CBINOP CCAST ? ? ? ? ? ? ? ? CGEP ? CDATA"
  ],
 if r ≠ "?" then r else "constop." + toword.i
else "constop." + toword.i

type castop is toint:int

Export toint(castop) int

Export castop(i:int) castop

Export type:castop

Function =(a:castop, b:castop) boolean toint.a = toint.b

Function trunc castop castop.0

Function zext castop castop.1

Function sext castop castop.2

Function fptoui castop castop.3

Function fptosi castop castop.4

Function uitofp castop castop.5

Function sitofp castop castop.6

Function fptrunc castop castop.7

Function fpext castop castop.8

Function ptrtoint castop castop.9

Function inttoptr castop castop.10

Function bitcast castop castop.11

Function decode(code:castop) seq.word
let discard =
 [
  trunc
  , zext
  , sext
  , fptoui
  , fptosi
  , uitofp
  , sitofp
  , fptrunc
  , fpext
  , ptrtoint
  , inttoptr
  , bitcast
 ]
let i = toint.code,
if between(i + 1, 1, 12) then
 let r =
  [
   (i + 1)
   #"trunc zext sext fptoui fptosi uitofp sitofp fptrunc fpext ptrtoint inttoptr bitcast"
  ],
 if r ≠ "?" then r else "castop." + toword.i
else "castop." + toword.i

type binaryop is toint:int

Export toint(binaryop) int

Export binaryop(i:int) binaryop

Export type:binaryop

Function =(a:binaryop, b:binaryop) boolean toint.a = toint.b

Function add binaryop binaryop.0

Function sub binaryop binaryop.1

Function mul binaryop binaryop.2

Function udiv binaryop binaryop.3

Function sdiv binaryop binaryop.4

Function urem binaryop binaryop.5

Function srem binaryop binaryop.6

Function shl binaryop binaryop.7

Function lshr binaryop binaryop.8

Function ashr binaryop binaryop.9

Function and binaryop binaryop.10

Function or binaryop binaryop.11

Function xor binaryop binaryop.12

Function decode(code:binaryop) seq.word
let discard = [add, sub, mul, udiv, sdiv, urem, srem, shl, lshr, ashr, and, or, xor]
let i = toint.code,
if between(i + 1, 1, 13) then
 let r = [(i + 1)#"add sub mul udiv sdiv urem srem shl lshr ashr and or xor"],
 if r ≠ "?" then r else "binaryop." + toword.i
else "binaryop." + toword.i

type cmp2op is toint:int

Export toint(cmp2op) int

Export cmp2op(i:int) cmp2op

Export type:cmp2op

Function =(a:cmp2op, b:cmp2op) boolean toint.a = toint.b

Function Feq cmp2op cmp2op.1

Function Fgt cmp2op cmp2op.2

Function Fge cmp2op cmp2op.3

Function Flt cmp2op cmp2op.4

Function Fle cmp2op cmp2op.5

Function Fne cmp2op cmp2op.6

Function eq cmp2op cmp2op.32

Function ne cmp2op cmp2op.33

Function ugt cmp2op cmp2op.34

Function uge cmp2op cmp2op.35

Function ult cmp2op cmp2op.36

Function ule cmp2op cmp2op.37

Function sgt cmp2op cmp2op.38

Function sge cmp2op cmp2op.39

Function slt cmp2op cmp2op.40

Function sle cmp2op cmp2op.41

Function decode(code:cmp2op) seq.word
let discard = [Feq, Fgt, Fge, Flt, Fle, Fne, eq, ne, ugt, uge, ult, ule, sgt, sge, slt, sle]
let i = toint.code,
if between(i + 1, 1, 42) then
 let r =
  [
   (i + 1)
   #"? Feq Fgt Fge Flt Fle Fne ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? eq ne ugt uge ult ule sgt sge slt sle"
  ],
 if r ≠ "?" then r else "cmp2op." + toword.i
else "cmp2op." + toword.i 