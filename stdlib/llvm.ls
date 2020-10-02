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


use seq.trackconst


Function type:llvmtype internaltype export

Function type:llvmconst internaltype export

Function type:llvmtypeele internaltype export

Function typ(llvmconst)int export

Function toseq(llvmconst)seq.int export

type llvmtypeele is record toseq:seq.int


type llvmtype is record index:int


function hash(a:llvmtypeele)int hash.toseq.a

Function assignencoding(l:int, a:llvmtypeele) int l+1


function =(a:llvmtypeele, b:llvmtypeele)boolean toseq.a = toseq.b 

type llvmconst is record typ:int, toseq:seq.int

use seq.encodingpair.llvmconst

function cvttorec( a:encodingpair.llvmconst ) seq.int  toseq.data.a

Function listconsts seq.seq.int @(+, cvttorec, empty:seq.seq.int, encoding:seq.encodingpair.llvmconst)

function hash(a:llvmconst)int hash.symtabname.a

Function assignencoding(l:int, a:llvmconst) int l+1


Function =(a:llvmconst, b:llvmconst)boolean  symtabname.a =  symtabname.b ∧ typ.a = typ.b

Function getelementptr(type:llvmtype, name:seq.word, i:int)int
 C(ptr.i64, [ CONSTGEP, typ.type, typ.ptr.type, symboltableentry(name, type), typ.i32, C32.0, typ.i64, C64.i])


type machineinfo is record triple:seq.int, datalayout:seq.int

function getmachineinfo machineinfo builtin.usemangle

Function print(t:llvmtype) seq.word
let a=toseq.decode(to:encoding.llvmtypeele(index.t))
let tp=a_1
let b=@(+,llvmtype,empty:seq.llvmtype,@(+,+.1,empty:seq.int,a))
if tp = TYPEINTEGER then [ merge.("i" + toword.a_2)]
  else if tp = TYPEARRAY then
  "[" + toword.a_2 + "x" + print(b_3) + "]"
  else if tp = TYPEPOINTER then print(b_2) + "*"
  else if tp = TYPEFUNCTION then
    print(b_3)+"(" + @(seperator(","), print,"", subseq(b, 4, length.a))
   + ")"
  else if tp = TYPEVOID then"VOID"
  else if tp = TYPEDOUBLE then "double"
  else"?"


Function llvm(deflist:seq.seq.int, bodytxts:seq.internalbc, trecords:seq.seq.int)seq.bits
 let MODABBREVLEN = 3
 let TYPEABBREVLEN = 4
 let offset = length.encoding:seq.encodingpair.llvmconst
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
      let g = @(constrecords, identity, trackconst(a5, -1, 0), subseq(encoding:seq.encodingpair.llvmconst, length.deflist + 1, offset))
      let a6 = finishblock(bits.g, blockstart.g, TYPEABBREVLEN)
       // function bodies //
       // assert length.trecords = length.typerecords report"X"//
       let a7 = @(addbody(offset, MODABBREVLEN), identity, a6, bodytxts)
        // sym table //
        let symtabheader = addblockheader(a7, MODABBREVLEN, VALUESYMTABBLOCK, TYPEABBREVLEN)
        let a8 = finishblock(symentries(symtabheader, encoding:seq.encodingpair.llvmconst, 1), length.symtabheader, TYPEABBREVLEN)
         // finish module block // data2.align.finishblock(a8, length.h, MODABBREVLEN)

Function adjust(s:seq.seq.int, adj:seq.int, i:int)seq.seq.int
 // go back and adjust types to fillin the length of arrays that were not known at time of creation of type //
 if i > length.adj then subseq(s, i, length.s)
 else
  let r = s_i
   [ if length.r < 2 then r
   else [ r_1, r_2 + adj_i] + subseq(r, 3, length.r)]
   + adjust(s, adj, i + 1)

function symtabname(a:llvmconst)seq.int  subseq(toseq.a,2,length.toseq.a)

function symtabtype(a:llvmconst) int  (toseq.a)_1


Function symboltableentry(name:seq.word,type:llvmtype) int symboltableentry(name_1,type)

Function symboltableentry(name:word,type:llvmtype) int
valueofencoding.encode( llvmconst(-1,  [typ.type]+  tointseq.decodeword.name)) - 1

Function global(name:word,type:llvmtype) int
valueofencoding.encode( llvmconst(-2,  [typ.type]+  tointseq.decodeword.name)) - 1

use seq.encodingpair.llvmtypeele

Function C64(i:int)int valueofencoding.encode( llvmconst(typ.i64, [ CONSTINTEGER, i])) - 1

Function getllvmconst(i:int)seq.int cvttorec.(encoding:seq.encodingpair.llvmconst)_(i + 1)

Function C32(i:int)int valueofencoding.encode( llvmconst(typ.i32, [ CONSTINTEGER, i])) - 1

Function C(t:llvmtype, s:seq.int)int valueofencoding.encode( llvmconst(typ.t, s)) - 1

Function Cprt(t:int, s:seq.int)int // used in print bitcodes tool // valueofencoding.encode( llvmconst(t, s)) - 1

Function constvalue(i:int) int    (toseq.decode(  to:encoding.llvmconst(i+1)))_2

- - - - - - - - - - - - - - - - - - - - - - -

function cvttorec( a:encodingpair.llvmtypeele ) seq.int  toseq.data.a

Function typerecords seq.seq.int @(+, cvttorec, empty:seq.seq.int, encoding:seq.encodingpair.llvmtypeele)

Function typ(a:llvmtype)int index.a - 1

Function llvmtype(s:seq.int)llvmtype 
llvmtype.valueofencoding.encode(llvmtypeele.s) 


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

 function ismoduleblock(l:llvmconst) boolean
   typ.l < 0 
   
function islastmodule (l:trackconst) boolean
   lasttype.l < 0 

function constrecords(z:trackconst, lx:encodingpair.llvmconst)trackconst
 // keep track of type of last const processed and add record when type changes //
 let l=data.lx
 let MODABBREVLEN = 3
 let TYPEABBREVLEN = 4
  if ismoduleblock.l   then
  let bits = if not.islastmodule.z then finishblock(bits.z, blockstart.z, TYPEABBREVLEN)else bits.z
     let rec=if typ.l=-1 then [ MODULECODEFUNCTION, symtabtype.l, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
     else [ MODULECODEGLOBALVAR, symtabtype.l, 2, 1+C64.0, 0, align8 + 1, 0]
     trackconst(addrecord(MODABBREVLEN, bits, rec), typ.l, 0)
  else
   let newblock = islastmodule.z  ∧ not.ismoduleblock.l 
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

Function symentries(bits:bitpackedseq.bit, s:seq.encodingpair.llvmconst, i:int)bitpackedseq.bit
 if i > length.s then bits
 else
  let l = data.s_i
  let bs = if ismoduleblock.l then
  let abbrevlength = 4
  let name=symtabname.l
   let a1 = addvbr6(addvbr6(addvbr6(addvbr(bits, 3, abbrevlength), ENTRY), length.name + 1), i - 1)
    addvbr6(a1, name)
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