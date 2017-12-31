module bitstream

use stdlib

use seq.int

type bits is record toint:int

Function toint(bits) int export

Function bits(int) bits export




Function &or(a:bits,bits) bits  builtin.usemangle

Function &and(a:bits,bits) bits  builtin.usemangle

Function  >>(a:bits,i:int) bits  builtin.usemangle

Function <<(a:bits,i:int) bits  builtin.usemangle 


            
            
__________________

use packedseq.bits


use UTF8


use blockseq.bits

use seq.bit

use byteseq.bit

use blockseq.int


type bit is record toint:int


function sizeinbits(a:bit)  int   1

function tobits(a:bit ) bits bits.toint.a

Function addvbr(b:bitpackedseq.bit , newbits:int,bitcount:int) bitpackedseq.bit 
           let limit=toint( bits(1) << (bitcount-1))
           if  newbits < limit then add(b,bits(newbits),bitcount)
           else   
              let firstchunk =   bits(limit-1) &and bits(newbits) &or bits(limit)
              let secondchunk =  bits(newbits) >> (bitcount-1)
              assert toint.secondchunk < limit report "vbr encoding for value is not handled"+toword.newbits+toword.limit
               add(b, (secondchunk << bitcount &or firstchunk),bitcount * 2 )

       
         
function addvbr6( b:bits, bitstoadd:int, leftover:bits, s:seq.int, r:bitpackedseq.bit,i:int) bitpackedseq.bit
        if bitstoadd > 58 then   addvbr6(bits.0,0,leftover,s,add(r,b,bitstoadd),i) 
        else
        if toint.leftover > 0 then
           if toint.leftover < 32 then
             addvbr6(b  &or leftover << bitstoadd,bitstoadd+6,bits.0,s,r,i)
          else 
             addvbr6(b   &or (( (leftover &and bits(31)) &or bits(32) ) <<  bitstoadd),bitstoadd+6,leftover >> 5,s,r,i)
        else if i > length.s then
           if bitstoadd=0 then r else add(r,b,bitstoadd)
        else
           let v = s_i
           if v < 32 then 
                    addvbr6(b &or bits.v << bitstoadd,bitstoadd+6,bits.0,s,r,i+1)
            else  
            addvbr6(b   &or (( (bits.v &and bits(31)) &or bits(32) ) << bitstoadd),bitstoadd+6,bits.v >> 5, s,r,i+1) 
             
  Function addvbr6(b:bitpackedseq.bit,s:seq.int) bitpackedseq.bit
  addvbr6(bits.0, 0     ,bits.0,s,b,1)
  
Function addvbr6(b:bitpackedseq.bit,v:int) bitpackedseq.bit
   addvbr6(bits.0, 0    ,bits.0,[v],b,1) 
          

Function addvbrsigned6(b:bitpackedseq.bit, val:int)bitpackedseq.bit
 if val < 0 
  then if val > -16 
   then addvbr6(b, 2 *-val + 1)
   else let chunk = bits(32 +-val mod 16 * 2 + 1) 
        addvbr6(  chunk ,  6,bits(-val) >> 4,empty:seq.int,b,1) 
  else if val < 16 
  then addvbr6(b, 2 * val)
  else let chunk = bits(32 + val mod 16 * 2) 
        addvbr6( chunk, 6,bits(val) >> 4,empty:seq.int,b,1) 
       
Function align32(a:bitpackedseq.bit)bitpackedseq.bit
 let k = (length.a  )  mod 32 
  if k = 0  then a 
  else add(a, bits.0, 32 - k  )
  






_____________________







module llvm

In addition to the llvm bicode format documentation, an useful file for reference is LLVMBitCodes.h

use options.bitblock

use options.bitstream

use options.seq.int

use seq.bitblock

use seq.boolean

use seq.encoding.llvmconst

use seq.encoding.llvmtype

use seq.int

use seq.llvmconst

use seq.llvmtype

use seq.seq.int

use seq.seq.seq.int

use stacktrace

use stdlib

use bitstream

Function typ(llvmconst) int export

Function toseq(llvmconst) seq.int export


type llvmtype is record toseq:seq.int

type llvmtypes is encoding llvmtype

function hash(a:llvmtype)int hash.toseq.a

function =(a:llvmtype, b:llvmtype)boolean toseq.a = toseq.b

type llvmconst is record typ:int,toseq:seq.int

type llvmconsts is encoding llvmconst

function hash(a:llvmconst)int hash.toseq.a

function =(a:llvmconst, b:llvmconst)boolean toseq.a = toseq.b &and typ.a=typ.b

Function getelementptr(type:encoding.llvmtype, name:seq.word)int 
 C(ptr.i64, [ CONSTGEP, typ.type, typ.ptr.type, C.name, typ.i32, C32.0, typ.i32, C32.0])

Function llvmconsts erecord.llvmconst export

Function mapping(erecord.llvmconst) seq.llvmconst export
  
use internalbc

use seq.internalbc


   Function llvm(  deflist:seq.seq.int, bodytxts:seq.internalbc, trecords:seq.seq.int) seq.bits
 let  MODABBREVLEN=3 let TYPEABBREVLEN=4
  let offset = length.mapping.llvmconsts
   let  h= addblockheader(add(add(add(add(empty:bitpackedseq.bit,bits.66,8),bits.67,8),bits.192,8),bits.222,8),  2,MODULEBLOCK,MODABBREVLEN)
    let  a=addrecords(h,MODABBREVLEN,[ [ 1, 1]])
   // type block //
   let  typeheader=addblockheader(a,MODABBREVLEN,TYPEBLOCK,TYPEABBREVLEN)
   let  a2=addrecords(typeheader,TYPEABBREVLEN,[ [ ENTRY, length.trecords]]+ trecords)
   let  a3=finishblock(a2,typeheader,TYPEABBREVLEN)
   // para block //
     let   paraheader=addblockheader(a3,MODABBREVLEN,PARABLOCK,TYPEABBREVLEN)
     let   a4=finishblock(addrecords(paraheader,TYPEABBREVLEN,[ [ ENTRY, 2^32 - 1, 32 + 2^14]]),paraheader,TYPEABBREVLEN)
   // def list //
     let a5= addrecords(a4,MODABBREVLEN,deflist)  
       // const block //
       let   constheader=addblockheader(a5,MODABBREVLEN,CONSTANTSBLOCK,TYPEABBREVLEN)
         let a6= finishblock( constrecords(constheader,-1,mapping.llvmconsts,1) ,constheader,TYPEABBREVLEN)
        // function bodies //
   let a7 = @(addbody(offset,MODABBREVLEN), identity, a6, bodytxts)
 // sym table //
      let  symtabheader=addblockheader(a7,MODABBREVLEN,VALUESYMTABBLOCK,TYPEABBREVLEN)
      let a8=finishblock( symentries(symtabheader,mapping.llvmconsts,1) ,symtabheader,TYPEABBREVLEN)
  // finish module block //    
      data2.align.finishblock(a8,h,MODABBREVLEN)
  
   
 

Function adjust(s:seq.seq.int, adj:seq.int, i:int)seq.seq.int 
 if i > length.adj 
  then subseq(s, i, length.s)
  else let r = s_i 
  [ if length.r < 2 then r else [ r_1, r_2 + adj_i]+ subseq(r, 3, length.r)]+ adjust(s, adj, i + 1)

Function C(s:seq.word)int C(s_1)

Function C(w:word)int encoding.encode(llvmconst(-1, decode.w), llvmconsts) - 1

Function C64(i:int)int encoding.encode(llvmconst(typ.i64,[  CONSTINTEGER, i]), llvmconsts) - 1

Function C32(i:int)int encoding.encode(llvmconst(typ.i32,[  CONSTINTEGER, i]), llvmconsts) - 1

Function C(t:encoding.llvmtype, s:seq.int)int 
encoding.encode(llvmconst(typ.t, s), llvmconsts) - 1

-----------------------

Function funcname(a:llvmconst) word encodeword.toseq.a 
 
Function symbolrecords2 seq.llvmconst subsym(mapping.llvmconsts,empty:seq.llvmconst,1 )
  
  
        

  
  
  
  
  
function subsym(s:seq.llvmconst, result:seq.llvmconst, i:int)seq.llvmconst 
 if i > length.s 
  then result 
  else let l=s_i
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




use byteseq.bit

Function addblockheader(b:bitpackedseq.bit,currentabbrelength:int,blockid:int,abbrevlength:int) bitpackedseq.bit
  addvbr(align32.addvbr(addvbr(addvbr(b, ENTERBLOCK, currentabbrelength), blockid, 8), abbrevlength, 4),0,32)

Function finishblock(  current:bitpackedseq.bit, header:bitpackedseq.bit,blockabbrevlength:int) bitpackedseq.bit
    let bb=align32.addvbr(current, ENDBLOCK, blockabbrevlength)
    let len = (length .bb-length.header) / 32
    //  assert false report "X"+toword(length.header -32)+toword.len //
     patch(bb, length.header-31   ,len)
     
 

Function addbody(offset:int, abbrevlen:int, m:bitpackedseq.bit, bodytxt:internalbc) bitpackedseq.bit
     let header=addblockheader(m,abbrevlen,FUNCTIONBLOCK ,4)
         finishblock(addtobitstream(offset,header,bodytxt),header,4)


Function addrecords(bits:bitpackedseq.bit, abbrevlength:int, s:seq.seq.int) bitpackedseq.bit
 addrecords(bits, abbrevlength, s, 1)

function addrecords(bits:bitpackedseq.bit, abbrevlength:int, s:seq.seq.int, i:int) bitpackedseq.bit
   if i > length.s 
  then bits
  else let a = s_i 
  let a1 = addvbr(bits, 3, abbrevlength)
  let tp = a_1 
  let a2 = addvbr6(addvbr6(a1, tp), length.a - 1)
  let bs =  @(addvbr6, identity, a2, subseq(a, 2, length.a))
  addrecords(bs,  abbrevlength, s, i + 1)
  
  
Function  constrecords(bits:bitpackedseq.bit,lasttype:int, s:seq.llvmconst,i:int) bitpackedseq.bit
       if i > length.s then bits else 
       let l = s_i
       let bs =if typ.l=-1 then bits else 
          let abbrevlength = 4
         let bits2 = if lasttype=typ.l then bits else 
                         // addvbr6(addvbr6( addvbr6(addvbr(bits, 3, abbrevlength),1),1),typ.l) //
                         addvbr6 (add(bits,  bits( ( 1 * 64 + 1) * 16 + 3), 16),typ.l)
         let tp=(toseq.l)_1    
         if  tp=CONSTINTEGER  then
                // addvbrsigned6(addvbr6( addvbr6(addvbr(bits2, 3, abbrevlength),tp),1),(toseq.l)_2) //
                  addvbrsigned6(add(bits2,  bits( ( 1 * 64 + tp) * 16 + 3), 16),(toseq.l)_2)
         else  
         let a1 = if length.toseq.l < 32 then
                    add(bits2, bits(((length.toseq.l-1)  * 64 + tp) * 16+ 3) ,16)
             else addvbr6( addvbr6(addvbr(bits2, 3, abbrevlength),tp),length.toseq.l-1)
            addvbr6(  a1, subseq(toseq.l,2,length.toseq.l))
        constrecords(bs, lasttype,s, i + 1)
        
Function  symentries(bits:bitpackedseq.bit, s:seq.llvmconst,i:int) bitpackedseq.bit
       if i > length.s then bits else 
       let l = s_i
       let bs =if typ.l=-1 then  
         let abbrevlength = 4           
         let a1 = addvbr6(addvbr6( addvbr6(addvbr(bits, 3, abbrevlength),ENTRY),length.toseq.l+1),i-1)
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

