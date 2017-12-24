module bitstream

use stdlib

use seq.int

type bits is record toint:int

Function toint(bits) int export

Function bits(int) bits export


type bitstream is record bytes:seq.int,val:bits,nobits:int

Function emptybitstream bitstream bitstream(empty:seq.int,bits.0,0)

Function emptyx bitstream bitstream(empty:seq.int,bits.0,0)

Function bytes(bitstream) seq.int export

Function val(bitstream) bits export

Function nobits(bitstream) int export


Function &or(a:bits,bits) bits  builtin.usemangle

Function &and(a:bits,bits) bits  builtin.usemangle

Function  >>(a:bits,i:int) bits  builtin.usemangle

Function <<(a:bits,i:int) bits  builtin.usemangle 

/function  -(a:bits,i:int)  bits builtin.usemangle

/function  +(a:bits,i:int)  bits builtin.usemangle

Function +(a:bitstream, b:bitstream) bitstream   bitstream ( bytes.a+bytes.b,val.b,nobits.b)

Function bitstream(seq.int,bits,int) bitstream export

Function addvbr6(b:bitstream,s:seq.int) bitstream
  addvbr6((val.b), nobits.b     ,bits.0,s,bytes.b,1)
  
Function addvbr6(b:bitstream,v:int) bitstream
   addvbr6((val.b), nobits.b     ,bits.0,[v],bytes.b,1) 

    
Function addbits(b:bitstream,newbits:int,nonew:int) bitstream
            addbits(val.b,nobits.b,newbits,nonew,bytes.b)

Function addvbr(b:bitstream, newbits:int,bitcount:int) bitstream
           let limit=toint( bits(1) << (bitcount-1))
           if  newbits < limit then addbits(b,newbits,bitcount)
           else   
              let firstchunk =   bits(limit-1) &and bits(newbits) &or bits(limit)
              let secondchunk =  bits(newbits) >> (bitcount-1)
              assert toint.secondchunk < limit report "vbr encoding for value is not handled"+toword.newbits+toword.limit
               addbits(b,toint(secondchunk << bitcount &or firstchunk),bitcount * 2 )


function addbits(b:bits,nobits:int, newbits:int,nonew:int,r:seq.int) bitstream
       if nobits &ge 8 then  
         addbits(b >> 8 ,nobits - 8,newbits,nonew,r+toint( b &and bits(255)))
       else  
         if nonew=0 then 
             bitstream(r,b,nobits)
       else let bitstomove = min(nonew,50) 
            let mask = bits(toint(bits.1 << bitstomove)-1)
            addbits( b &or   ( (bits.newbits &and mask )   <<  nobits), nobits+ bitstomove,toint(bits(newbits) >> bitstomove),nonew-bitstomove,r)
        

function     addvbr6(b:bits,nobits:int, leftover:bits,s:seq.int,r:seq.int,i:int) bitstream
       if nobits &ge 8 then  
         addvbr6(b >> 8 ,nobits - 8,leftover,s,r+toint( b &and bits(255)),i)
       else if toint.leftover > 0 then
          if toint.leftover < 32 then
             addvbr6(b  &or leftover << nobits,nobits+6,bits.0,s,r,i)
          else 
             addvbr6(b   &or (( (leftover &and bits(31)) &or bits(32) ) <<  nobits),nobits+6,leftover >> 5,s,r,i)
       else if i > length.s then bitstream(r,b,  nobits)
       else
         let v = s_i
           if v < 32 then 
                    addvbr6(b &or bits.v << nobits,nobits+6,bits.0,s,r,i+1)
            else  
            addvbr6(b   &or (( (bits.v &and bits(31)) &or bits(32) ) << nobits),nobits+6,bits.v >> 5, s,r,i+1) 
            
            
Function addvbrsigned6(b:bitstream, val:int)bitstream
 if val < 0 
  then if val > -16 
   then addvbr6(b, 2 *-val + 1)
   else let chunk = bits(32 +-val mod 16 * 2 + 1) << nobits.b
        addvbr6( val.b &or (chunk), nobits.b+6,bits(-val) >> 4,empty:seq.int,bytes.b,1) 
  else if val < 16 
  then addvbr6(b, 2 * val)
  else let chunk = bits(32 + val mod 16 * 2) << nobits.b
        addvbr6( val.b &or (chunk), nobits.b+6,bits(val) >> 4,empty:seq.int,bytes.b,1) 
       
Function align(a:bitstream)bitstream
 let k = ( length.bytes.a  * 8 + nobits.a )    mod 32 
  if k = 0  then a 
  else addbits(a, 0, 32 - k  )


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


  
use internalbc

use seq.internalbc

Function llvm(  deflist:seq.seq.int, bodytxts:seq.internalbc, trecords:seq.seq.int)seq.int 
 PROFILE.let m = addrecords(bitblock(emptyx, 3, MODULEBLOCK, 0),[ [ 1, 1]]) 
  let m1 = addblock(m,TYPEBLOCK, 4, [ [ ENTRY, length.trecords]]+ trecords ) 
    let m2 = addblock(m1,PARABLOCK, 4, [ [ ENTRY, 2^32 - 1, 32 + 2^14]] )
  let m3 = addrecords(m2, deflist)
  let constblock = addblock(m3,CONSTANTSBLOCK,4 ,constrecords(emptyx,-1,mapping.llvmconsts,1) )
  let offset = length.mapping.llvmconsts
  let m4 = @(addbody.offset, identity, constblock, bodytxts)
   let n = addblock(block(0, 2), addblock(m4,VALUESYMTABBLOCK,4, symentries(emptyx,mapping.llvmconsts,1)))
  [ 66, 67, 192, 222]+ bytes.bits.n



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
  
  
        
function  symentries(bits:bitstream, s:seq.llvmconst,i:int) bitstream
       if i > length.s then bits else 
       let l = s_i
       let bs =if typ.l=-1 then  
         let abbrevlength = 4           
         let a1 = addvbr6(addvbr6( addvbr6(addvbr(bits, 3, abbrevlength),ENTRY),length.toseq.l+1),i-1)
          addvbr6(a1, toseq.l)
        else bits
        symentries(bs, s, i + 1)
 
 
 use options.bitstream

function  constrecords(bits:bitstream,lasttype:int, s:seq.llvmconst,i:int) bitstream
       if i > length.s then bits else 
       let l = s_i
       let bs =if typ.l=-1 then bits else 
          let abbrevlength = 4
         let bits2 = if lasttype=typ.l then bits else 
                         // addvbr6(addvbr6( addvbr6(addvbr(bits, 3, abbrevlength),1),1),typ.l) //
                         addvbr6 (addbits(bits,  ( 1 * 64 + 1) * 16 + 3, 16),typ.l)
         let tp=(toseq.l)_1    
         if  tp=CONSTINTEGER  then
                // addvbrsigned6(addvbr6( addvbr6(addvbr(bits2, 3, abbrevlength),tp),1),(toseq.l)_2) //
                  addvbrsigned6(addbits(bits2,  ( 1 * 64 + tp) * 16 + 3, 16),(toseq.l)_2)
         else  
         let a1 = if length.toseq.l < 32 then
                    addbits(bits2, ((length.toseq.l-1)  * 64 + tp) * 16+ 3 ,16)
             else addvbr6( addvbr6(addvbr(bits2, 3, abbrevlength),tp),length.toseq.l-1)
            addvbr6(  a1, subseq(toseq.l,2,length.toseq.l))
        constrecords(bs, lasttype,s, i + 1)
  
  
  
  
  
  
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

-------------



type bitblock is record bits:bitstream, abbrevlength:int, blockid:int, slot:int



function addrecords(b:bitblock, s:seq.seq.int)bitblock 
  bitblock(addrecords(bits.b,  abbrevlength.b, s, 1),abbrevlength.b,blockid.b,0)

function addrecords(bits:bitstream, abbrevlength:int, s:seq.seq.int, i:int) bitstream
   if i > length.s 
  then bits
  else let a = s_i 
  let a1 = addvbr(bits, 3, abbrevlength)
  let tp = a_1 
  let a2 = addvbr6(addvbr6(a1, tp), length.a - 1)
  let bs =  @(addvbr6, identity, a2, subseq(a, 2, length.a))
  addrecords(bs,  abbrevlength, s, i + 1)

   
function addbody(offset:int, m:bitblock, bodytxt:internalbc)bitblock 
   addblock(m, bitblock(tobitstream(offset,bodytxt), 4, FUNCTIONBLOCK, 0))



function addblock(a:bitblock, b:bitblock)bitblock 
   addblock(a,blockid.b,abbrevlength.b,bits.b)
    
  
  
 function addblock(a:bitblock, blockid:int,abbrevlength:int,s:seq.seq.int) bitblock 
   addblock(a,blockid,abbrevlength,addrecords(emptyx,abbrevlength,s,1))
    
 function addblock(a:bitblock, blockid:int,abbrevlength:int,bits:bitstream) bitblock 
 let ENDBLOCK = 0 
  let ENTERBLOCK = 1 
  let bb = align.addvbr(bits, ENDBLOCK, abbrevlength)
  let len = length.bytes.bb / 4 
  let c = addvbr(addvbr(addvbr(bits.a, ENTERBLOCK, abbrevlength.a), blockid, 8), abbrevlength, 4)
  bitblock(addvbr(align.c, len, 32)+ bb, abbrevlength.a, blockid.a, slot.a)
 
  
  

function block(kind:int, encodingsize:int)bitblock bitblock(emptyx, encodingsize, kind, 0)

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

