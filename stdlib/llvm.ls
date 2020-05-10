Module llvm

In addition to the llvm bitcode format documentation, an useful file for reference is LLVMBitCodes.h

use UTF8

use seq.bitpackedseq.bit

use bitpackedseq.bit

use seq.seq.bit

use seq.bit

use seq.seq.bits

use seq.bits

use bits

use seq.boolean

use fileio

use blockseq.int

use seq.seq.seq.int

use seq.seq.int

use seq.seq.internalbc

use seq.internalbc

use internalbc

use seq.encoding.llvmconst

use encoding.llvmconst

use seq.llvmconst

use otherseq.llvmtype

use seq.llvmtype

use encoding.llvmtypeele

use seq.seq.llvmtypeele

use seq.llvmtypeele

use mangle

use stacktrace

use stdlib

use deepcopy.trackconst

use seq.trackconst

Function type:llvmtype internaltype export

Function type:llvmconst internaltype export


Function typ(llvmconst)int export

Function toseq(llvmconst)seq.int export

type llvmtypeele is record toseq:seq.int, index:int

type llvmtypes is encoding llvmtypeele

type llvmtype is record index:int

function llvmtypeele(toseq:seq.int)llvmtypeele llvmtypeele(toseq, 0)

function addindex(l:llvmtypeele, i:int)llvmtypeele llvmtypeele(toseq.l, i)

function hash(a:llvmtypeele)int hash.toseq.a

function assignencoding(l:int, a:llvmtypeele) int assignrandom(l,a)


function =(a:llvmtypeele, b:llvmtypeele)boolean toseq.a = toseq.b 

type llvmconst is record typ:int, toseq:seq.int


type llvmconsts is encoding llvmconst

Function listconsts seq.seq.int @(+, toseq, empty:seq.seq.int, orderadded.llvmconsts)

function hash(a:llvmconst)int hash.toseq.a

function assignencoding(l:int, a:llvmconst) int l+1


function =(a:llvmconst, b:llvmconst)boolean toseq.a = toseq.b ∧ typ.a = typ.b

Function getelementptr(type:llvmtype, name:seq.word, i:int)int
 C(ptr.i64, [ CONSTGEP, typ.type, typ.ptr.type, C.name, typ.i32, C32.0, typ.i64, C64.i])

Function llvmconsts erecord.llvmconst export

type machineinfo is record triple:seq.int, datalayout:seq.int

function getmachineinfo machineinfo builtin.usemangle

Function llvm(deflist:seq.seq.int, bodytxts:seq.internalbc, trecords:seq.seq.int)seq.bits
 let MODABBREVLEN = 3
 let TYPEABBREVLEN = 4
 let offset = length.orderadded.llvmconsts
 let h = addblockheader(add(add(add(add(empty:bitpackedseq.bit, bits.66, 8), bits.67, 8), bits.192, 8), bits.222, 8)
 , 2
 , MODULEBLOCK
 , MODABBREVLEN)
 let info = getmachineinfo
 let a = addrecords(h, MODABBREVLEN, [ [ 1, 1], [ MODULETRIPLE] + triple.info, [ MODULELAYOUT] + datalayout.info])
  // type block //
  let typeheader = addblockheader(a, MODABBREVLEN, TYPEBLOCK, TYPEABBREVLEN)
  let a2 = addrecords(typeheader, TYPEABBREVLEN, [ [ ENTRY, length.trecords]] + trecords)
  let a3 = finishblock(a2, length.typeheader, TYPEABBREVLEN)
   // PARAGRPBLOCK //
   let pgh = addblockheader(a3, MODABBREVLEN, PARAGRPBLOCK, TYPEABBREVLEN)
   let pge = finishblock(addrecords(pgh
   , TYPEABBREVLEN
   , [ [ 3, 0, 2^32 - 1, 0, 14, 0, 26, 0, 18] + [ 3]
   + tointseq.@(+, decodeword, empty:seq.char,"no - frame - pointer - elim - non - leaf")
   + [ 0]])
   , length.pgh
   , TYPEABBREVLEN)
    // para block //
    let paraheader = addblockheader(pge, MODABBREVLEN, PARABLOCK, TYPEABBREVLEN)
    let a4 = finishblock(addrecords(paraheader, TYPEABBREVLEN, [ [ 2, 0]]), length.paraheader, TYPEABBREVLEN)
     // def list //
     let a5 = addrecords(a4, MODABBREVLEN, deflist)
      // const block //
      let g = @(constrecords, identity, trackconst(a5, -1, 0), subseq(orderadded.llvmconsts, length.deflist + 1, offset))
      let a6 = finishblock(bits.g, blockstart.g, TYPEABBREVLEN)
       // function bodies //
       // assert length.trecords = length.typerecords report"X"//
       let a7 = @(addbody(offset, MODABBREVLEN), identity, a6, bodytxts)
        // sym table //
        let symtabheader = addblockheader(a7, MODABBREVLEN, VALUESYMTABBLOCK, TYPEABBREVLEN)
        let a8 = finishblock(symentries(symtabheader, orderadded.llvmconsts, 1), length.symtabheader, TYPEABBREVLEN)
         // finish module block // data2.align.finishblock(a8, length.h, MODABBREVLEN)

Function adjust(s:seq.seq.int, adj:seq.int, i:int)seq.seq.int
 // go back and adjust types to fillin the length of arrays that where not known at time of creation of type //
 if i > length.adj then subseq(s, i, length.s)
 else
  let r = s_i
   [ if length.r < 2 then r
   else [ r_1, r_2 + adj_i] + subseq(r, 3, length.r)]
   + adjust(s, adj, i + 1)

Function C(s:seq.word)int C.s_1

Function C(w:word)int valueofencoding.encode(llvmconsts, llvmconst(-1, tointseq.decodeword.w)) - 1

Function C64(i:int)int valueofencoding.encode(llvmconsts, llvmconst(typ.i64, [ CONSTINTEGER, i])) - 1

Function getllvmconst(i:int)seq.int toseq.(orderadded.llvmconsts)_(i + 1)

Function C32(i:int)int valueofencoding.encode(llvmconsts, llvmconst(typ.i32, [ CONSTINTEGER, i])) - 1

Function C(t:llvmtype, s:seq.int)int valueofencoding.encode(llvmconsts, llvmconst(typ.t, s)) - 1

Function Cprt(t:int, s:seq.int)int // used in print bitcodes tool // valueofencoding.encode(llvmconsts, llvmconst(t, s)) - 1

Function constvalue(i:int) int    (toseq.decode( llvmconsts, to:encoding.llvmconst(i+1)))_2

- - - - - - - - - - - - - - - - - - - - - - -

Function funcname(a:llvmconst)word encodeword.tocharseq.toseq.a

Function typerecords seq.seq.int @(+, toseq, empty:seq.seq.int, orderadded.llvmtypes)

Function typ(a:llvmtype)int index.a - 1

Function llvmtype(s:seq.int)llvmtype llvmtype.findindex(llvmtypes, llvmtypeele.s)

Function double llvmtype llvmtype.[ TYPEDOUBLE]

Function i64 llvmtype llvmtype.[ TYPEINTEGER, 64]

Function i32 llvmtype llvmtype.[ TYPEINTEGER, 32]

Function i8 llvmtype llvmtype.[ TYPEINTEGER, 8]

Function i1 llvmtype llvmtype.[ TYPEINTEGER, 1]

Function VOID llvmtype llvmtype.[ TYPEVOID]

Function array(size:int, base:llvmtype)llvmtype llvmtype.[ TYPEARRAY, size, typ.base]

Function ptr(base:llvmtype)llvmtype llvmtype.[ TYPEPOINTER, typ.base, 0]

Function function(para:seq.llvmtype)llvmtype llvmtype.@(+, typ, [ TYPEFUNCTION, 0], para)

function ENDBLOCK int 0

function ENTERBLOCK int 1

Function addblockheader(b:bitpackedseq.bit, currentabbrelength:int, blockid:int, abbrevlength:int)bitpackedseq.bit
 addvbr(align32.addvbr(addvbr(addvbr(b, ENTERBLOCK, currentabbrelength), blockid, 8), abbrevlength, 4), 0, 32)

Function finishblock(current:bitpackedseq.bit, headerplace:int, blockabbrevlength:int)bitpackedseq.bit
 if headerplace = 0 then current
 else
  let bb = align32.addvbr(current, ENDBLOCK, blockabbrevlength)
  let len =(length.bb - headerplace) / 32
   // assert false report"X"+ toword(length.header -32)+ toword.len // patch(bb, headerplace - 31, len)

Function addbody(offset:int, abbrevlen:int, m:bitpackedseq.bit, bodytxt:internalbc)bitpackedseq.bit
 let header = addblockheader(m, abbrevlen, FUNCTIONBLOCK, 4)
  finishblock(addtobitstream(offset, header, bodytxt), length.header, 4)

Function addrecords(bits:bitpackedseq.bit, abbrevlength:int, s:seq.seq.int)bitpackedseq.bit @(addrecord.abbrevlength, identity, bits, s)

function addrecord(abbrevlength:int, bits:bitpackedseq.bit, a:seq.int)bitpackedseq.bit
 let a1 = addvbr(bits, 3, abbrevlength)
 let a2 = addvbr6(addvbr6(a1, a_1), length.a - 1)
  @(addvbr6, identity, a2, subseq(a, 2, length.a))

type trackconst is record bits:bitpackedseq.bit, lasttype:int, blockstart:int

function constrecords(z:trackconst, l:llvmconst)trackconst
// FORCEINLINE
 . // // keep track of type of last const processed and add record when type changes //
 let MODABBREVLEN = 3
 let TYPEABBREVLEN = 4
  if typ.l = -1 then
  let bits = if lasttype.z ≠ -1 then finishblock(bits.z, blockstart.z, TYPEABBREVLEN)else bits.z
    trackconst(addrecord(MODABBREVLEN, bits, [ MODULECODEFUNCTION, typ.getftype.funcname.l, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), typ.l, 0)
  else
   let newblock = lasttype.z = -1 ∧ typ.l ≠ -1
   let bits = if newblock then addblockheader(bits.z, MODABBREVLEN, CONSTANTSBLOCK, TYPEABBREVLEN)else bits.z
   let bits2 = if lasttype.z = typ.l then bits
   else
    addvbr6(add(bits, bits((1 * 64 + 1) * 16 + 3), 16), typ.l)
   let tp =(toseq.l)_1
   let bs = if tp = CONSTINTEGER then
   addvbrsigned6(add(bits2, bits((1 * 64 + CONSTINTEGER) * 16 + 3), 16),(toseq.l)_2)
   else
    let a1 = if length.toseq.l < 32 then
    add(bits2, bits(((length.toseq.l - 1) * 64 + tp) * 16 + 3), 16)
    else addvbr6(addvbr6(addvbr(bits2, 3, TYPEABBREVLEN), tp), length.toseq.l - 1)
     addvbr6(a1, subseq(toseq.l, 2, length.toseq.l))
    trackconst(bs, typ.l, if newblock then length.bits else blockstart.z)

Function symentries(bits:bitpackedseq.bit, s:seq.llvmconst, i:int)bitpackedseq.bit
 if i > length.s then bits
 else
  let l = s_i
  let bs = if typ.l = -1 then
  let abbrevlength = 4
   let a1 = addvbr6(addvbr6(addvbr6(addvbr(bits, 3, abbrevlength), ENTRY), length.toseq.l + 1), i - 1)
    addvbr6(a1, toseq.l)
  else bits
   symentries(bs, s, i + 1)

Function getftype(w:word)llvmtype function.constantseq(manglednopara.w + 2, i64)

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