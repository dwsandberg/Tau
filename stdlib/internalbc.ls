Module internalbc

* 64 + 2*3 instead of 64 + 2 * 3 does not give reasonable error message!

use bitpackedseq.bit

use bits

use stdlib

Function BLOCKCOUNT(slot:int, a1:int)internalbc addstartbits(1, 1, add(a1, emptyinternalbc))

Function RET(slot:int, a1:int)internalbc addstartbits(INSTRET, 1, addaddress(slot, a1, emptyinternalbc))

Function RET(slot:int)internalbc addstartbits(INSTRET, 0, emptyinternalbc)

Function CAST(slot:int, a1:int, a2:int, a3:int)internalbc 
 addstartbits(INSTCAST, 3, addaddress(slot, a1, add(a2, add(a3, emptyinternalbc))))

Function BR(slot:int, a1:int, a2:int, a3:int)internalbc 
 addstartbits(INSTBR, 3, add(a1, add(a2, addaddress(slot, a3, emptyinternalbc))))
 
Function ALLOCA(slot:int, a1:int, a2:int,a3:int,a4:int)internalbc 
 addstartbits(INSTALLOCA, 4, add(a1, add(a2,  add(a3, add(a4,emptyinternalbc)))))
 

Function BR(slot:int, a1:int)internalbc addstartbits(INSTBR, 1, add(a1, emptyinternalbc))

Function GEP(slot:int, a1:int, a2:int, a3:int, a4:int)internalbc 
 addstartbits(INSTGEP, 4, add(a1, add(a2, addaddress(slot, a3, addaddress(slot, a4, emptyinternalbc)))))

Function GEP(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int)internalbc 
 addstartbits(INSTGEP, 5, add(a1, add(a2, addaddress(slot, a3, addaddress(slot, a4, addaddress(slot, a5, emptyinternalbc))))))

Function STORE(slot:int, a1:int, a2:int, a3:int, a4:int)internalbc 
 addstartbits(INSTSTORE, 4, addaddress(slot, a1, addaddress(slot, a2, add(a3, add(a4, emptyinternalbc)))))

Function BINOP(slot:int, a1:int, a2:int, a3:int, a4:int)internalbc 
 addstartbits(INSTBINOP, 4, addaddress(slot, a1, addaddress(slot, a2, add(a3, add(a4, emptyinternalbc)))))

Function BINOP(slot:int, a1:int, a2:int, a3:int)internalbc 
 // TESTOPT. // addstartbits(INSTBINOP, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))

Function LOAD(slot:int, a1:int, a2:int, a3:int, a4:int)internalbc 
 addstartbits(INSTLOAD, 4, addaddress(slot, a1, add(a2, add(a3, add(a4, emptyinternalbc)))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int)internalbc 
 addstartbits(INSTCALL, 4, add(a1, add(a2, add(a3, addaddress(slot, a4, emptyinternalbc)))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int)internalbc 
 addstartbits(INSTCALL, 5, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, emptyinternalbc))))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int)internalbc 
 addstartbits(INSTCALL, 6, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, emptyinternalbc)))))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int, a7:int)internalbc 
 addstartbits(INSTCALL, 7, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, emptyinternalbc))))))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int, a7:int, a8:int)internalbc 
 addstartbits(INSTCALL, 8, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, addaddress(slot, a8, emptyinternalbc)))))))))

use seq.internalbc

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int, a7:int, a8:int, a9:int)internalbc 
 // TESTOPT.// addstartbits(INSTCALL, 9, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, addaddress(slot, a8, addaddress(slot, a9, emptyinternalbc))))))))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int, a7:int, a8:int, a9:int,a10:int)internalbc 
 addstartbits(INSTCALL, 10, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, addaddress(slot, a8, addaddress(slot, a9, addaddress(slot, a10,emptyinternalbc)))))))))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, rest:seq.int)internalbc 
 addstartbits(INSTCALL, 5 + length.rest, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, args(slot, emptyinternalbc, rest, length.rest)))))))

Function CALLSTART( slot:int, a1:int, a2:int, a3:int, a4:int,noargs:int) internalbc
 addstartbits(INSTCALL, 4 + noargs, add(a1, add(a2, add(a3, addaddress(slot, a4,emptyinternalbc)))))

Function CALLFINISH(slot:int,rest:seq.int) internalbc
  args(slot, emptyinternalbc, rest, length.rest)
  
function args(slot:int, t:internalbc, rest:seq.int, i:int)internalbc 
 if i = 0 then t else args(slot, addaddress(slot, rest_i, t), rest, i - 1)

Function CMP2(slot:int, a1:int, a2:int, a3:int)internalbc 
 addstartbits(INSTCMP2, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))

Function PHI(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int, a7:int)internalbc 
 addstartbits(INSTPHI, 7, add(a1, addsignedaddress(slot, a2, add(a3, addsignedaddress(slot, a4, add(a5, addsignedaddress(slot, a6, add(a7, emptyinternalbc))))))))

Function PHI(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int)internalbc 
 addstartbits(INSTPHI, 5, add(a1, addsignedaddress(slot, a2, add(a3, addsignedaddress(slot, a4, add(a5, emptyinternalbc))))))

Function PHI(slot:int, a1:int, s:seq.int)internalbc 
 addstartbits(INSTPHI, length.s + 1, add(a1, subphi(slot, emptyinternalbc, s, length.s)))

function subphi(slot:int, b:internalbc, s:seq.int, i:int)internalbc 
 if i > 1 then subphi(slot, addsignedaddress(slot, s_(i - 1), add(s_i, b)), s, i - 2)else b

function addpair(tailphi:seq.int, slot:int, p:int, a:internalbc, b:int)internalbc 
 addsignedaddress(slot, tailphi_(b + p), add(tailphi_b, a))

(block1, p11, p12, p13, block2, p21, p22, p23)phi(p11, block1, p21, block2)

function phiinst(slot:int, typ:int, tailphi:seq.int, nopara:int, p:int)internalbc 
 let t = @(addpair(tailphi, slot + p, p), identity, emptyinternalbc, arithseq(length.tailphi /(nopara + 1),-nopara - 1, length.tailphi - nopara))
  addstartbits(INSTPHI, length.tailphi /(nopara + 1)* 2 + 1, add(typ, t))

Function phiinst(slot:int, typ:int, tailphi:seq.int, nopara:int)internalbc 
 @(+, phiinst(slot, typ, tailphi, nopara), emptyinternalbc, arithseq(nopara, 1, 1))

Function addstartbits(inst:int, noargs:int, c:internalbc)internalbc 
 if noargs > 31 ∨ inst > 31 * 31 
  then internalbc(3, 4, [ vbr6, inst, vbr6, noargs]+ finish.c)
  else if inst < 32 
  then let b = if bitcount.c > 40 then internalbc(0, 0, finish.c)else c 
   internalbc(((bits.b * 64 + noargs)* 64 + inst)* 16 + 3, bitcount.b +(6 + 6 + 4), done.b)
  else let b = if bitcount.c > 34 then internalbc(0, 0, finish.c)else c 
  internalbc((((bits.b * 64 + noargs)* 64 + inst / 32)* 64 + inst mod 32 + 32)* 16 + 3, bitcount.b +(6 + 6 + 6 + 4), done.b)

type internalbc is record bits:int, bitcount:int, done:seq.int

Function done(internalbc) seq.int export

Function bitcount(internalbc) int export

Function bits(internalbc) int export


Function print(a:internalbc) seq.word
 print1(  finish.a,1,"") 
 
function print1(a:seq.int,i:int,result:seq.word) seq.word
  if i > length.a then result else 
   let val=a_i
   if val = vbr6 then  print1(a,i+2,result+"vbr6"+toword(a_(i+1) ))
   else if val=reloc then print1(a,i+2,result+"reloc"+toword(a_(i+1) ))
   else if val=-ibcsub1 then print1(a,i+2,result+"sub11"+toword(a_(i+1) ))
   else if val=-ibcsub2 then  print1(a,i+2,result+"sub22"+toword(a_(i+1) ) )
   else let  nobits =toint(bits.val ∧ bits.63)
   let bits = toint(bits.val >> 6 )
   print1(a,i+1,result+[toword.bits,":"_1,toword.nobits])
   
use seq.int
   
   
 
Function emptyinternalbc internalbc internalbc(0, 0, empty:seq.int)

Function +(a:internalbc, b:internalbc)internalbc 
 if length.done.a > 0 ∨ bitcount.a + bitcount.b > 56 
  then internalbc(bits.a, bitcount.a, done.a + finish.b)
  else internalbc(bits.b * 2^bitcount.a + bits.a, bitcount.a + bitcount.b, done.b)

Function finish(b:internalbc)seq.int 
 if bitcount.b = 0 then done.b else [ bits.b * 64 + bitcount.b]+ done.b

Function addaddress(slot:int, a:int, b:internalbc)internalbc 
 if-a > slot 
  then 
    // assert a in [ibcsub1,ibcsub2,ibcsub3] report "HERE"+toword.a+toword.ibcsub1+toword.ibcsub2+toword.ibcsub3 //
   if a=ibcfirstpara2 then  internalbc(0, 0, [firstpara2]+ finish.b) else
  internalbc(0, 0, [if a=ibcsub1 then sub1 else if a=ibcsub2 then sub2 else assert a=ibcsub3 
   report "unknown code in addaddress"   sub3 , slot]+ finish.b)
  else if a < 0 then add(slot + a, b)else internalbc(0, 0, [ reloc, a - slot + 1]+ finish.b)

Function addsignedaddress(slot:int, a:int, b:internalbc)internalbc 
 if a ≤ 0 
  then let v = slot + a 
   let c = if v ≥ 0 then 2 * v else 2 *-v + 1 
   add(c, b)
  else internalbc(0, 0, [ relocsigned, a - slot + 1]+ finish.b)

Function add(val:int, b:internalbc)internalbc 
 if val > 31 
  then internalbc(0, 0, [ vbr6, val]+ finish.b)
  else let newbitcount = 6 + bitcount.b 
  if newbitcount > 56 then internalbc(val, 6, finish.b)else internalbc(bits.b * 64 + val, newbitcount, done.b)


type  internal2 is record state:int,offset:int,result:bitpackedseq.bit 

use seq.bitpackedseq.bit


Function  addtobitstream(offset:int,bs:bitpackedseq.bit,b:internalbc) bitpackedseq.bit  
result.@(add2.offset,identity,internal2(0,offset,bs),finish.b)

use  seq.internal2

function   add2(offset:int,r:internal2,val:int) internal2
FORCEINLINE.
   let nobits = toint(bits.val ∧ bits.63)
   // assert nobits=63 &or nobits < 59 &or state.r &ne 0 report "XJ"+toword.nobits+toword.state.r //
   let bits = bits.val >> 6 
   let newstate =  if state.r=0 then  if nobits < 60 then 0 else   val
    else     0 
   let newoffset =  if nobits=setoffset &and state.r=0 then offset+toint.bits else   offset.r
   let newresult =  
 if state.r=0 then if nobits < 58 then add(result.r, bits , nobits) else 
   if val=firstpara2 then addvbr6(result.r,offset.r-offset+1) else result.r 
    else      if state.r = relocsigned then addvbrsigned6(result.r, offset.r - val)
  else
     addvbr6(result.r, if state.r= reloc 
   then  offset.r - val 
   else   // if state.r=firstpara2 then
        offset.r-offset+1
   else  //
     assert state.r = vbr6 report"invalid code" + toword.state.r
     val
    )
      internal2(newstate, newoffset, newresult)
      
Function addoffset(b:seq.int,deltaoffset:int) seq.int
  [setoffset+64 * deltaoffset]+ b+[setoffset] 


Function internalbc( bits:int, bitcount:int, done:seq.int  ) internalbc export 

Function isempty(a:internalbc) boolean   bitcount.a=0 &and length.done.a=0  


Function vbr6 int 63 + 64

function relocsigned int 63 + 64 * 3

function newway boolean true

Function reloc int 63  +64 * 7

Function ibcfirstpara2 int // must be big enough value so -ibcirstpart2 > max slot number in function // -(6400000)

Function  sub1 int 60 + 64 * 5001

Function  sub2 int 60 + 64 * 5002

Function  sub3 int 60 + 64 * 5003

Function ibcsub1 int -(6400001)

Function ibcsub2 int -(6400002)

Function ibcsub3 int -(6400003)




function firstpara2 int 58 

function setoffset int 59



// Function ibcsub1 int -(60 + 64 * 5001)

/Function ibcsub2 int -(60 + 64 * 5002)

/Function ibcsub3 int -(60 + 64 * 5003)//

Function ibcsubpara(i:int) int  { (i-60 ) / 64  -5000 }





Function INSTCALL int 34

Function INSTRET int 10

Function INSTCAST int // CAST:[ opcode, ty, opty, opval]// 3

Function INSTSELECT int 5

Function INSTBR int 11

Function INSTPHI int 16

Function INSTCMP2 int 28

Function INSTBINOP int 2

Function INSTBLOCK int 1

Function INSTNOPARA int -1

Function INSTALLOCA int 19

Function INSTLOAD int 20

Function INSTSTORE int 44

Function INSTGEP int 43

