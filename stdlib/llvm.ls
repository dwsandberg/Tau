module llvm

In addition to the llvm bicode format documentation, an useful file for reference is LLVMBitCodes.h

use bitpackedseq.bit

use bits

use internalbc



use seq.bitblock

use seq.boolean

use seq.encoding.llvmconst

use seq.encoding.llvmtype

use seq.int

use seq.internalbc

use seq.llvmconst

use seq.llvmtype

use seq.seq.int

use seq.seq.seq.int

use stacktrace

use stdlib

Function typ(llvmconst)int export

Function toseq(llvmconst)seq.int export

type llvmtype is record toseq:seq.int

type llvmtypes is encoding llvmtype

function hash(a:llvmtype)int hash.toseq.a

function =(a:llvmtype, b:llvmtype)boolean toseq.a = toseq.b

type llvmconst is record typ:int, toseq:seq.int

type llvmconsts is encoding llvmconst

function hash(a:llvmconst)int hash.toseq.a

function =(a:llvmconst, b:llvmconst)boolean toseq.a = toseq.b ∧ typ.a = typ.b

Function getelementptr(type:encoding.llvmtype, name:seq.word)int 
 C(ptr.i64, [ CONSTGEP, typ.type, typ.ptr.type, C.name, typ.i32, C32.0, typ.i32, C32.0])

Function llvmconsts erecord.llvmconst export

Function mapping(erecord.llvmconst)seq.llvmconst export

type machineinfo is record triple:seq.int, datalayout:seq.int

function getmachineinfo machineinfo builtin.usemangle

Function llvm(deflist:seq.seq.int, bodytxts:seq.internalbc, trecords:seq.seq.int)seq.bits 
 let MODABBREVLEN = 3 
  let TYPEABBREVLEN = 4 
  let offset = length.mapping.llvmconsts 
  let h = addblockheader(add(add(add(add(empty:bitpackedseq.bit, bits.66, 8), bits.67, 8), bits.192, 8), bits.222, 8), 2, MODULEBLOCK, MODABBREVLEN)
  let info = getmachineinfo 
  let a = addrecords(h, MODABBREVLEN, [ [ 1, 1], [ MODULETRIPLE]+ triple.info, [ MODULELAYOUT]+ datalayout.info])
  // type block // 
  let typeheader = addblockheader(a, MODABBREVLEN, TYPEBLOCK, TYPEABBREVLEN)
  let a2 = addrecords(typeheader, TYPEABBREVLEN, [ [ ENTRY, length.trecords]]+ trecords)
  let a3 = finishblock(a2, typeheader, TYPEABBREVLEN)
  // PARAGRPBLOCK // 
  let pgh = addblockheader(a3, MODABBREVLEN, PARAGRPBLOCK, TYPEABBREVLEN)
  let pge = finishblock(addrecords(pgh, TYPEABBREVLEN, [ [ 3, 0, 2^32 - 1, 0, 14, 0, 26, 0, 18]+ @(+, decode, [ 3],"no-frame-pointer-elim-non-leaf")+ [ 0]]), pgh, TYPEABBREVLEN)
  // para block // 
  let paraheader = addblockheader(pge, MODABBREVLEN, PARABLOCK, TYPEABBREVLEN)
  let a4 = finishblock(addrecords(paraheader, TYPEABBREVLEN, [ [ 2, 0]]), paraheader, TYPEABBREVLEN)
  // def list // 
  let a5 = addrecords(a4, MODABBREVLEN, deflist)
  // const block // 
  let constheader = addblockheader(a5, MODABBREVLEN, CONSTANTSBLOCK, TYPEABBREVLEN)
  let a6 = finishblock(constrecords(constheader, -1, mapping.llvmconsts, 1), constheader, TYPEABBREVLEN)
  // function bodies // 
  let a7 = @(addbody(offset, MODABBREVLEN), identity, a6, bodytxts)
  // sym table // 
  let symtabheader = addblockheader(a7, MODABBREVLEN, VALUESYMTABBLOCK, TYPEABBREVLEN)
  let a8 = finishblock(symentries(symtabheader, mapping.llvmconsts, 1), symtabheader, TYPEABBREVLEN)
  // finish module block // data2.align.finishblock(a8, h, MODABBREVLEN)

Function adjust(s:seq.seq.int, adj:seq.int, i:int)seq.seq.int 
 if i > length.adj 
  then subseq(s, i, length.s)
  else let r = s_i 
  [ if length.r < 2 then r else [ r_1, r_2 + adj_i]+ subseq(r, 3, length.r)]+ adjust(s, adj, i + 1)

Function C(s:seq.word)int C(s_1)

Function C(w:word)int encoding.encode(llvmconst(-1, decode.w), llvmconsts) - 1

Function C64(i:int)int encoding.encode(llvmconst(typ.i64, [ CONSTINTEGER, i]), llvmconsts) - 1

Function getllvmconst(i:int) seq.int   { toseq((mapping.llvmconsts)_(i+1)) }

Function C32(i:int)int encoding.encode(llvmconst(typ.i32, [ CONSTINTEGER, i]), llvmconsts) - 1

Function C(t:encoding.llvmtype, s:seq.int)int encoding.encode(llvmconst(typ.t, s), llvmconsts) - 1

Function Cprt(t:int, s:seq.int)int 
// used in print bitcodes tool //
encoding.encode(llvmconst(t, s), llvmconsts) - 1


-----------------------

Function funcname(a:llvmconst)word encodeword.toseq.a

Function symbolrecords2 seq.llvmconst subsym(mapping.llvmconsts, empty:seq.llvmconst, 1)

function subsym(s:seq.llvmconst, result:seq.llvmconst, i:int)seq.llvmconst 
 if i > length.s 
  then result 
  else let l = s_i 
  if typ.l = -1 then subsym(s, result + l, i + 1)else result

Function typerecords seq.seq.int @(+, toseq, empty:seq.seq.int, mapping.llvmtypes)

Function typ(a:encoding.llvmtype)int encoding.a - 1

Function double encoding.llvmtype encode(llvmtype.[ TYPEDOUBLE], llvmtypes)

Function i64 encoding.llvmtype encode(llvmtype.[ TYPEINTEGER, 64], llvmtypes)

Function i32 encoding.llvmtype encode(llvmtype.[ TYPEINTEGER, 32], llvmtypes)

Function i8 encoding.llvmtype encode(llvmtype.[ TYPEINTEGER, 8], llvmtypes)

Function i1 encoding.llvmtype encode(llvmtype.[ TYPEINTEGER, 1], llvmtypes)

Function VOID encoding.llvmtype encode(llvmtype.[ TYPEVOID], llvmtypes)

Function array(size:int, base:encoding.llvmtype)encoding.llvmtype 
 encode(llvmtype.[ TYPEARRAY, size, typ.base], llvmtypes)

Function ptr(base:encoding.llvmtype)encoding.llvmtype 
 encode(llvmtype.[ TYPEPOINTER, typ.base, 0], llvmtypes)

Function function(para:seq.encoding.llvmtype)encoding.llvmtype 
 encode(llvmtype.@(+, typ, [ TYPEFUNCTION, 0], para), llvmtypes)

function ENDBLOCK int 0

function ENTERBLOCK int 1

Function addblockheader(b:bitpackedseq.bit, currentabbrelength:int, blockid:int, abbrevlength:int)bitpackedseq.bit 
 addvbr(align32.addvbr(addvbr(addvbr(b, ENTERBLOCK, currentabbrelength), blockid, 8), abbrevlength, 4), 0, 32)

Function finishblock(current:bitpackedseq.bit, header:bitpackedseq.bit, blockabbrevlength:int)bitpackedseq.bit 
 let bb = align32.addvbr(current, ENDBLOCK, blockabbrevlength)
  let len =(length.bb - length.header)/ 32 
  // assert false report"X"+ toword(length.header-32)+ toword.len // 
  patch(bb, length.header - 31, len)

Function addbody(offset:int, abbrevlen:int, m:bitpackedseq.bit, bodytxt:internalbc)bitpackedseq.bit 
 let header = addblockheader(m, abbrevlen, FUNCTIONBLOCK, 4)
  finishblock(addtobitstream(offset, header, bodytxt), header, 4)

Function addrecords(bits:bitpackedseq.bit, abbrevlength:int, s:seq.seq.int)bitpackedseq.bit 
 addrecords(bits, abbrevlength, s, 1)

function addrecords(bits:bitpackedseq.bit, abbrevlength:int, s:seq.seq.int, i:int)bitpackedseq.bit 
 if i > length.s 
  then bits 
  else let a = s_i 
  let a1 = addvbr(bits, 3, abbrevlength)
  let tp = a_1 
  let a2 = addvbr6(addvbr6(a1, tp), length.a - 1)
  let bs = @(addvbr6, identity, a2, subseq(a, 2, length.a))
  addrecords(bs, abbrevlength, s, i + 1)

Function constrecords(bits:bitpackedseq.bit, lasttype:int, s:seq.llvmconst, i:int)bitpackedseq.bit 
 if i > length.s 
  then bits 
  else let l = s_i 
  if typ.l = -1 
  then constrecords(bits, lasttype, s, i + 1)
  else let abbrevlength = 4 
  let bits2 = if lasttype = typ.l then bits else addvbr6(add(bits, bits((1 * 64 + 1)* 16 + 3), 16), typ.l)
  let tp = toseq(l)_1 
  let bs = if tp = CONSTINTEGER 
   then addvbrsigned6(add(bits2, bits((1 * 64 + CONSTINTEGER)* 16 + 3), 16), toseq(l)_2)
   else let a1 = if length.toseq.l < 32 
    then add(bits2, bits(((length.toseq.l - 1)* 64 + tp)* 16 + 3), 16)
    else addvbr6(addvbr6(addvbr(bits2, 3, abbrevlength), tp), length.toseq.l - 1)
   addvbr6(a1, subseq(toseq.l, 2, length.toseq.l))
  constrecords(bs, typ.l, s, i + 1)

Function symentries(bits:bitpackedseq.bit, s:seq.llvmconst, i:int)bitpackedseq.bit 
 if i > length.s 
  then bits 
  else let l = s_i 
  let bs = if typ.l = -1 
   then let abbrevlength = 4 
    let a1 = addvbr6(addvbr6(addvbr6(addvbr(bits, 3, abbrevlength), ENTRY), length.toseq.l + 1), i - 1)
    addvbr6(a1, toseq.l)
   else bits 
  symentries(bs, s, i + 1)

Function STRUCTNAME int 19

Function BLOCKINFOBLOCK int 0

Function MODULEBLOCK int 8

Function PARABLOCK int 9

Function PARAGRPBLOCK int 10

Function CONSTANTSBLOCK int 11

Function FUNCTIONBLOCK int 12

Function TYPEBLOCK int 17

Function MODULETRIPLE int 2

Function MODULELAYOUT int 3

Function MODULECODEGLOBALVAR int 7

Function MODULECODEFUNCTION int 8

Function VALUESYMTABBLOCK int 14

Function CONSTCECAST int 11

Function CONSTINTEGER int 4

Function CONSTSETTYPE int 1

Function CONSTNULL int 2

Function CONSTDATA int 22

Function CONSTGEP int 20

Function AGGREGATE int 7

Function CSTRING int 9

Function TYPEVOID int 2

Function TYPEDOUBLE int 4

Function TYPEINTEGER int 7

Function TYPEPOINTER int 8

Function TYPEFUNCTION int 21

Function TYPEARRAY int 11

Function OPAQUE int 6

Function ENTRY int 1

Function align4 int 3

Function align8 int 4

Function align16 int 5

