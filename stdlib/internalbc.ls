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
 addstartbits(INSTBINOP, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))

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

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int, a7:int, a8:int, a9:int)internalbc 
 addstartbits(INSTCALL, 9, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, addaddress(slot, a8, addaddress(slot, a9, emptyinternalbc))))))))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int, a7:int, a8:int, a9:int,a10:int)internalbc 
 addstartbits(INSTCALL, 10, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, addaddress(slot, a8, addaddress(slot, a9, addaddress(slot, a10,emptyinternalbc)))))))))))

Function CALL(slot:int, a1:int, a2:int, a3:int, a4:int, a5:int, rest:seq.int)internalbc 
 addstartbits(INSTCALL, 5 + length.rest, add(a1, add(a2, add(a3, addaddress(slot, a4, addaddress(slot, a5, args(slot, emptyinternalbc, rest, length.rest)))))))

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

Function emptyinternalbc internalbc internalbc(0, 0, empty:seq.int)

Function +(a:internalbc, b:internalbc)internalbc 
 if length.done.a > 0 ∨ bitcount.a + bitcount.b > 56 
  then internalbc(bits.a, bitcount.a, done.a + finish.b)
  else internalbc(bits.b * 2^bitcount.a + bits.a, bitcount.a + bitcount.b, done.b)

Function finish(b:internalbc)seq.int 
 if bitcount.b = 0 then done.b else [ bits.b * 64 + bitcount.b]+ done.b

function addaddress(slot:int, a:int, b:internalbc)internalbc 
 if-a > slot 
  then internalbc(0, 0, [-a, slot]+ finish.b)
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


type  internal2 is record state:int,val1:int,val2:int,offset:int,result:bitpackedseq.bit 

use seq.bitpackedseq.bit


Function  addtobitstream(offset:int,bs:bitpackedseq.bit,b:internalbc) bitpackedseq.bit  
result.@(add2,identity,internal2(0,0,0,offset,bs),finish.b)

use  seq.internal2

function   add2(r:internal2,val:int) internal2
FORCEINLINE.
   let nobits = toint(bits.val ∧ bits.63)
   let bits = bits.val >> 6
   let newstate =  if state.r=0 then  if nobits < 58 then 0 else   toint.bits
    else    if state.r > 8 then  state.r-1 else 0 
   let newval1 = if state.r=tocode.setsub then if val ≤ 0 then offset.r - val else val else val1.r
   let newval2 = if state.r=9 then if val ≤ 0 then offset.r - val else val else val2.r
   let newoffset = if state.r=8 then offset.r+val else offset.r
   let newresult = if state.r=0 then if nobits < 58 then add(result.r, bits , nobits) else result.r else 
       if state.r  > 7 then result.r
       else if state.r = tocode.relocsigned then addvbrsigned6(result.r, offset.r - val)
  else
     addvbr6(result.r, if state.r= tocode.reloc 
   then offset.r - val
   else if state.r = tocode.vbr6 
   then val
   else if state.r = tocode.sub11 
   then offset.r - (val1.r - val+ 1)
   else assert state.r = tocode.sub22 report"invalid code" offset.r - (val2.r - val+ 1) )
      internal2(newstate, newval1, newval2,newoffset, newresult)
  

2 - 9  8
8 - 8  7
9 - 7  0

Function usetemplate(deltaoffset:int, t:internalbc, val1:int, val2:int)internalbc 
 internalbc(0, 0, [ setsub, 
 if val1 < 0 then val1 + 1 else val1, 
 if val2 < 0 then val2 + 1 else val2,  deltaoffset]+ finish.t + [ setsub,0,0,-deltaoffset]
)


function tocode(i:int) int  { (i - 63) / 64 }

function reloc int 63+7 * 64

function vbr6 int 63 + 64

Function ibcsub1 int -sub11

Function ibcsub2 int -sub22

function sub11 int 63 + 64 * 5

function sub22 int 63 + 64 * 6

function setsub int 63 + 64 * 10

function relocsigned int 63 + 64 * 3

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

