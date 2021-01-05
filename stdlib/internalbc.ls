x#!/usr/local/bin/tau  ;use data; test2

Module internalbc

use standard

use bits

use seq.bits

use bitstream

use seq.templatepart

use UTF8

use seq.bitstream

use seq.seq.bit

use seq.bit

use seq.seq.bits

use seq.seq.seq.int

use seq.seq.int

use seq.seq.internalbc

use seq.internalbc

use llvm

use llvmconstants

use seq.slot

use seq.slotrecord

use seq.trackconst

type internalbc is record bits:int, bitcount:int, done:seq.int

Function emptyinternalbc internalbc internalbc(0, 0, empty:seq.int)

Function isempty(a:internalbc)boolean bitcount.a = 0 ∧ length.done.a = 0

Function addstartbits(inst:int, noargs:int, b:internalbc)internalbc
 if noargs > 31 ∨ inst > 31 ∨ bitcount.b > 56 - 16 then
 let c = add(inst, add(noargs, b))
   if bitcount.c > 56 - 4 then internalbc(3, 4, finish.c)
   else internalbc(bits.c * 16 + 3, bitcount.c + 4, done.c)
 else
  internalbc(((bits.b * 64 + noargs) * 64 + inst) * 16 + 3, bitcount.b + (6 + 6 + 4), done.b)

Function +(a:internalbc, b:internalbc)internalbc
 if length.done.a > 0 ∨ bitcount.a + bitcount.b > 56 then
 internalbc(bits.a, bitcount.a, done.a + finish.b)
 else
  internalbc(bits.b * 2^(bitcount.a) + bits.a, bitcount.a + bitcount.b, done.b)

function finish(b:internalbc)seq.int
 if bitcount.b = 0 then done.b
 else [ bits.b * 64 + bitcount.b] + done.b
 
Function addaddress(slot:int, a:int, b:internalbc)internalbc  
 if-a > slot then
 if a = ibcfirstpara2 then internalbc(0, 0, [ firstpara2] + finish.b)
  else
   internalbc(0
   , 0
   , [ if a = ibcsub1 then subpara(1,slot)
   else if a = ibcsub2 then subpara(2,slot)
   else
    assert a = ibcsub3 report"unknown code in addaddress"
     subpara(3,slot)
    ]
   + finish.b)
 else if a < 0 then add(slot + a, b)
 else
  internalbc(0, 0, [ reloc + 64 * (relocoffset + a - slot + 1)] + finish.b)

Function addsignedaddress(slot:int, a:int, b:internalbc)internalbc
 if a ≤ 0 then
 let v = slot + a
  let c = if v ≥ 0 then 2 * v else 2 * -v + 1
   add(c, b)
 else internalbc(0, 0, [ relocsigned+64 * (a - slot + 1 )] + finish.b)

Function add(val:int, b:internalbc)internalbc
 if val < 32 ∧ bitcount.b < 51 then
 internalbc(bits.b * 64 + val, bitcount.b + 6, done.b)
 else
  let c = chunks.bits.val
   addvbr6help(bits.b, bitcount.b, done.b, c, length.c)

function chunks(val:bits)seq.bits
 if toint.val < 32 then [ val]
 else [ val ∧ bits.31 ∨ bits.32] + chunks(val >> 5)

function addvbr6help(bits:int, bitcount:int, done:seq.int, c:seq.bits, i:int)internalbc
 let newbitcount = 6 + bitcount
  if newbitcount > 56 then addvbr6help(0, 0, [ bits * 64 + bitcount] + done, c, i)
  else if i = 1 then internalbc(bits * 64 + toint.c_1, newbitcount, done)
  else addvbr6help(bits * 64 + toint.c_i, newbitcount, done, c, i - 1)

 
 
   Function addtobitstream(offset:int, bs:bitstream, b:internalbc)bitstream
add2(finish.b,1,offset,offset,bs) 
  
function  add2(done:seq.int,i:int,offset:int,slot:int,result:bitstream) bitstream
 if i > length.done then result else
   let val=done_i
  let nobits = toint(bits.val ∧ bits.63)
 let bits = bits.val >> 6
  let newoffset = if nobits = setoffset   then offset + toint.bits else slot
 let newresult =  
 if nobits < 58 then add(result, bits, nobits)
  else if nobits = reloc then addvbr6(result, slot - (toint.bits - relocoffset))
  else if val = firstpara2 then addvbr6(result, slot - offset)
    else if nobits=relocsigned then   
     let t=toint.if val < 0 then bits &or 0xFC00000000000000 else bits
        addvbrsigned6(result, slot - t)
  else result
   add2(done,i+1,offset,newoffset,newresult )

Function relocoffset int 1024 * 1024 * 1024 * 1024

 function subpara(parano:int,slot:int) int  61 +64 * parano + 1024 * slot  
 
Function ibcsubpara(i:int)int  (i - 61) / 64 mod 16

Function ibcsubslot(i:int)int   i / 1024

Function ibcfirstpara2 int // must be big enough value so-ibcirstpart2 > max slot number in function // 
   - 6400000
  
  Function ibcsub1 int   - 6400001

Function ibcsub2 int   - 6400002

Function ibcsub3 int  - 6400003

Function firstpara2 int 58

Function setoffset int 59

Function reloc int 60

function relocsigned int 63  



Export type:templatepart

Export type:internalbc

type templatepart is record part:seq.int, val:int

function parano(t:templatepart) int   ibcsubpara.val.t

function loc(t:templatepart) int  ibcsubslot.val.t

Export parano(templatepart)int

 
Function getparts(a:internalbc)seq.templatepart 
subgetparts(finish.a,1,1)

  
function subgetparts(a:seq.int,   lastindex:int, i:int)seq.templatepart
 // finds template parameters and breaks template into parts. //
 if i > length.a then [ templatepart(subseq(a, lastindex, i - 1), 0)]
 else
  let val = a_i
  let bits = toint(bits.val ∧ bits.63)
  if bits = 61 then
      [ templatepart(subseq(a, lastindex, i - 1),  val)]
       + subgetparts(a, i + 1, i + 1)
 else if bits &ge 58 then
       [ templatepart(subseq(a, lastindex, i-1  ), val)]
       + subgetparts(a, i + 1, i + 1)  
  else subgetparts(a,  lastindex, i + 1)
  
  

function processtemplatepart(deltaoffset:int, args:seq.int, t:templatepart)seq.int
   let bits = toint(bits.val.t ∧ bits.63)
  if bits = 61 then
  let arg = args_(parano.t)
  part.t+ (if arg < 0 then finish.add(deltaoffset + loc.t + arg, emptyinternalbc)
   else [ reloc + 64 * (relocoffset + arg - loc.t + 1 )])
  else if bits &in [reloc,relocsigned] then part.t+(val.t )
  else  if bits &ge 58 then part.t+val.t
  else  
    part.t

Function processtemplate(s:seq.templatepart, deltaoffset:int, args:seq.int)internalbc
 internalbc(0, 0,  
    s @ +(  [ setoffset + 64 * deltaoffset]   , processtemplatepart(deltaoffset, args, @e))
   +   setoffset )

_____________________________

Function BLOCKCOUNT(slot:int, a1:int)internalbc addstartbits(1, 1, add(a1, emptyinternalbc))

Function RETURN internalbc addstartbits(toint.RET, 0, emptyinternalbc)

Function RET(slot:slot, a1:slot)internalbc addstartbits(toint.RET, 1, addaddress(slot, a1, emptyinternalbc))

Function CAST(slot:slot, a1:slot, a2:llvmtype, a3:castop)internalbc
 addstartbits(toint.CAST, 3, addaddress(slot, a1, add(typ.a2, add(toint.a3, emptyinternalbc))))

Function BR(slot:slot, a1:int, a2:int, a3:slot)internalbc
 addstartbits(toint.BR, 3, add(a1, add(a2, addaddress(slot, a3, emptyinternalbc))))

Function ALLOCA(slot:slot, a1:llvmtype, a2:llvmtype, a3:slot, a4:int)internalbc
 addstartbits(toint.ALLOCA, 4, add(typ.a1, add(typ.a2, add(toint.a3, add(a4, emptyinternalbc)))))

Function BR(a1:int)internalbc addstartbits(toint.BR, 1, add(a1, emptyinternalbc))

Function GEP(slot:slot, a2:llvmtype, a3:slot)internalbc
 addstartbits(toint.GEP, 3, add(1, add(typ.a2, addaddress(slot, a3, emptyinternalbc))))

Function GEP(slot:slot, a2:llvmtype, a3:slot, a4:slot)internalbc
 addstartbits(toint.GEP, 4, add(1, add(typ.a2, addaddress(slot, a3, addaddress(slot, a4, emptyinternalbc)))))

Function STORE(slot:slot, a1:slot, a2:slot)internalbc
 addstartbits(toint.STORE, 4, addaddress(slot, a1, addaddress(slot, a2, add(toint.align8, add(0, emptyinternalbc)))))

Function LOAD(slot:slot, a1:slot, a2:llvmtype)internalbc
 addstartbits(toint.LOAD, 4, addaddress(slot, a1, add(typ.a2, add(toint.align8, add(0, emptyinternalbc)))))

Function CMP2(slot:slot, a1:slot, a2:slot, a3:int)internalbc
 addstartbits(toint.CMP2, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))


/Function BINOP(slot:int, a1:int, a2:int, a3:int)internalbc addstartbits(toint.BINOP, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))

Function BINOP(slot:slot, a1:slot, a2:slot, a3:binaryop)internalbc
 addstartbits(toint.BINOP, 3, addaddress(slot, a1, addaddress(slot, a2, add(toint.a3, emptyinternalbc))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot)internalbc
 addstartbits(toint.CALL, 4, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, emptyinternalbc)))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot)internalbc
 addstartbits(toint.CALL, 5, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, emptyinternalbc))))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot, a6:slot)internalbc
 addstartbits(toint.CALL, 6, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, emptyinternalbc)))))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot, a6:slot,a7:slot)internalbc
 addstartbits(toint.CALL, 7, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, emptyinternalbc))))))))



Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot, rest:seq.slot)internalbc
 addstartbits(toint.CALL
 , 5 + length.rest
 , add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, args(slot, emptyinternalbc, rest, length.rest)))))))

Function CALLSTART(slot:int, a1:int, a2:int, a3:int, a4:int, noargs:int)internalbc
 addstartbits(toint.CALL, 4 + noargs, add(a1, add(a2, add(a3, addaddress(slot, a4, emptyinternalbc)))))

Function CALLFINISH(slot:int, rest:seq.int)internalbc args(slot, emptyinternalbc, rest, length.rest)

function args(slot:int, t:internalbc, rest:seq.int, i:int)internalbc
 if i = 0 then t else args(slot, addaddress(slot, rest_i, t), rest, i - 1)

function args(slot:slot, t:internalbc, rest:seq.slot, i:int)internalbc
 if i = 0 then t else args(slot, addaddress(slot, rest_i, t), rest, i - 1)

Function PHI(slot:slot, a1:llvmtype, a2:slot, a3:int, a4:slot, a5:int, a6:slot, a7:int)internalbc
 addstartbits(toint.PHI
 , 7
 , add(typ.a1, addsignedaddress(slot, a2, add(a3, addsignedaddress(slot, a4, add(a5, addsignedaddress(slot, a6, add(a7, emptyinternalbc))))))))

Function PHI(slot:slot, a1:llvmtype, a2:slot, a3:int, a4:slot, a5:int)internalbc
 addstartbits(toint.PHI, 5, add(typ.a1, addsignedaddress(slot, a2, add(a3, addsignedaddress(slot, a4, add(a5, emptyinternalbc))))))

Function PHI(slot:int, a1:int, s:seq.int)internalbc
 addstartbits(toint.PHI, length.s + 1, add(a1, subphi(slot, emptyinternalbc, s, length.s)))

function subphi(slot:int, b:internalbc, s:seq.int, i:int)internalbc
 if i > 1 then
 subphi(slot, addsignedaddress(slot, s_(i - 1), add(s_i, b)), s, i - 2)
 else b

function addpair(a:internalbc, tailphi:seq.int, slot:int, p:int, b:int)internalbc
 addsignedaddress(slot, tailphi_(b + p), add(tailphi_b, a))

(block1, p11, p12, p13, block2, p21, p22, p23)phi(p11, block1, p21, block2)

Function phiinst(slot:int, typ:seq.int, tailphi:seq.int, nopara:int)internalbc
 arithseq(nopara, 1, 1) @ +(emptyinternalbc, phiinst(slot, typ, tailphi, nopara, @e))

function phiinst(slot:int, typ:seq.int, tailphi:seq.int, nopara:int, p:int)internalbc
 // let t = @(addpair(tailphi, slot + p, p), identity, emptyinternalbc, arithseq(length.tailphi /(nopara + 1),-nopara-1, length.tailphi-nopara))//
 let t = arithseq(length.tailphi / (nopara + 1),-nopara - 1, length.tailphi - nopara)
 @ addpair(emptyinternalbc, tailphi, slot + p, p, @e)
  addstartbits(toint.PHI, length.tailphi / (nopara + 1) * 2 + 1, add(typ_p, t))

function addsignedaddress(loc:slot, a:slot, bc:internalbc)internalbc addsignedaddress(-toint.loc, toint.a, bc)

function addaddress(locin:slot, a:slot, bc:internalbc)internalbc 
  let slot=-toint.locin 
 addaddress(slot, toint.a, bc) 

 


Function addvbr(b:bitstream, newbits:int, bitcount:int)bitstream
 let limit = toint(bits.1 << (bitcount - 1))
  if newbits < limit then add(b, bits.newbits, bitcount)
  else
   let firstchunk = bits(limit - 1) ∧ bits.newbits ∨ bits.limit
   let secondchunk = bits.newbits >> (bitcount - 1)
    assert toint.secondchunk < limit report"vbr encoding for value is not handled" + toword.newbits + toword.limit
     add(b, secondchunk << bitcount ∨ firstchunk, bitcount * 2)

function addvbr6(b:bits, bitstoadd:int, leftover:bits, s:seq.int, r:bitstream, i:int)bitstream
 if bitstoadd > 58 then addvbr6(bits.0, 0, leftover, s, add(r, b, bitstoadd), i)
 else if toint.leftover > 0 then
 if toint.leftover < 32 then
  addvbr6(b ∨ leftover << bitstoadd, bitstoadd + 6, bits.0, s, r, i)
  else
   addvbr6(b ∨ (leftover ∧ bits.31 ∨ bits.32) << bitstoadd, bitstoadd + 6, leftover >> 5, s, r, i)
 else if i > length.s then if bitstoadd = 0 then r else add(r, b, bitstoadd)
 else
  let v = s_i
   if v < 32 then
   addvbr6(b ∨ bits.v << bitstoadd, bitstoadd + 6, bits.0, s, r, i + 1)
   else
    addvbr6(b ∨ (bits.v ∧ bits.31 ∨ bits.32) << bitstoadd, bitstoadd + 6, bits.v >> 5, s, r, i + 1)

function addvbr6(b:bitstream, s:seq.int)bitstream addvbr6(bits.0, 0, bits.0, s, b, 1)

Function addvbr6(b:bitstream, v:int)bitstream addvbr6(bits.0, 0, bits.0, [ v], b, 1)

  Function addvbrsigned6(b:bitstream, val:int)bitstream
 if val < 0 then
 if val > -16 then addvbr6(b, 2 * -val + 1)
  else
   let tmp= toint( bits.val   &or 0xFFFF << 48  )
   let first6bits=  bits.-tmp << 1 &and 0x1F  &or 0x21 
    addvbr6(first6bits, 6, bits(-(val / 16)), empty:seq.int, b, 1)
 else if val < 16 then addvbr6(b, 2 * val)
 else
   let first6bits=  bits.val << 1 &and 0x1F  &or 0x20 
   addvbr6(first6bits, 6, bits.val >> 4, empty:seq.int, b, 1)


   
Function align32(a:bitstream)bitstream
 let k = length.a mod 32
  if k = 0 then a else add(a, bits.0, 32 - k)

Function addblockheader(b:bitstream, currentabbrelength:int, blockid:int, abbrevlength:int)bitstream
 addvbr(align32.addvbr(addvbr(addvbr(b, ENTERBLOCK, currentabbrelength), blockid, 8), abbrevlength, 4), 0, 32)

Function finishblock(current:bitstream, headerplace:int, blockabbrevlength:int)bitstream
 if headerplace = 0 then current
 else
  let bb = align32.addvbr(current, ENDBLOCK, blockabbrevlength)
  let len =(length.bb - headerplace) / 32
   // assert false report"X"+ toword(length.header-32)+ toword.len //
   patch(bb, headerplace - 31, len)

Function addbody(m:bitstream, offset:int, bodytxt:internalbc)bitstream
 let header = addblockheader(m, MODABBREVLEN, toint.FUNCTIONBLK, FUNCABBRVLEN)
  finishblock(addtobitstream(offset, header, bodytxt), length.header, FUNCABBRVLEN)

Function addbody(m:bitstream, bodytxt:seq.seq.int)bitstream
 let header = addblockheader(m, MODABBREVLEN, toint.FUNCTIONBLK, FUNCABBRVLEN)
  finishblock(addrecords(header, FUNCABBRVLEN, bodytxt), length.header, FUNCABBRVLEN)

Function addrecords(bits:bitstream, abbrevlength:int, s:seq.seq.int)bitstream s @ addrecord(bits, abbrevlength, @e)

function addrecord(bits:bitstream, abbrevlength:int, a:seq.int)bitstream
 let a1 = addvbr(bits, UNABBREVRECORD, abbrevlength)
 let a2 = addvbr6(addvbr6(a1, a_1), length.a - 1)
  subseq(a, 2, length.a) @ addvbr6(a2, @e)

function ENDBLOCK int 0

function ENTERBLOCK int 1

function UNABBREVRECORD int 3

function MODABBREVLEN int 3

function TYPEABBREVLEN int 4

function FUNCABBRVLEN int 4

Function llvm(deflist:seq.seq.int, bodytxts:seq.internalbc, trecords:seq.seq.int)seq.bits
 let p = llvmpartial(deflist, trecords)
 let offset = length.constantrecords
 let a7 = bodytxts @ addbody(a6.p, offset, @e)
  // sym table //
  let symtabheader = addblockheader(a7, MODABBREVLEN, toint.VALUESYMTABLE, TYPEABBREVLEN)
  let a8 = finishblock(symentries(symtabheader, constantrecords, 1), length.symtabheader, TYPEABBREVLEN)
   // finish module block // bits.finishblock(a8, length.h.p, MODABBREVLEN)

Function llvm(trecords:seq.seq.int, bodies:seq.seq.seq.int)seq.bits
 let p = llvmpartial(empty:seq.seq.int, trecords)
 let offset = length.constantrecords
 let a7 = bodies @ addbody(a6.p, @e)
  // sym table //
  let symtabheader = addblockheader(a7, MODABBREVLEN, toint.VALUESYMTABLE, TYPEABBREVLEN)
  let a8 = finishblock(symentries(symtabheader, constantrecords, 1), length.symtabheader, TYPEABBREVLEN)
   // finish module block // bits.finishblock(a8, length.h.p, MODABBREVLEN)

type llvmpartial is record a6:bitstream, h:bitstream

Function llvmpartial(deflist:seq.seq.int, trecords:seq.seq.int)llvmpartial
 let offset = length.constantrecords
 let h = addblockheader(add(add(add(add(empty:bitstream, bits.66, 8), bits.67, 8), bits.192, 8), bits.222, 8)
 , 2
 , toint.MODULE
 , MODABBREVLEN)
 let info = getmachineinfo
 let a = addrecords(h, MODABBREVLEN, [ [ 1, 1], [ toint.TRIPLE] + triple.info @+(empty:seq.int,toint.@e) ,
   [ toint.LAYOUT] + datalayout.info  @+(empty:seq.int,toint.@e)])
  // type block //
  let typeheader = addblockheader(a, MODABBREVLEN, toint.TYPES, TYPEABBREVLEN)
  let a2 = addrecords(typeheader, TYPEABBREVLEN, [ [ toint.NumEle, length.trecords]] + trecords)
  let a3 = finishblock(a2, length.typeheader, TYPEABBREVLEN)
   // PARAGRPBLOCK //
   let pgh = addblockheader(a3, MODABBREVLEN, toint.PARAGRP, TYPEABBREVLEN)
   let pge = finishblock(addrecords(pgh
   , TYPEABBREVLEN
   , [ [ 3, 0, 2^32 - 1, 0, 14, 0, 26, 0, 18] + [ 3]
   + tointseq("no-frame-pointer-elim-non-leaf" @ +(empty:seq.char, decodeword.@e))
   + [ 0]])
   , length.pgh
   , TYPEABBREVLEN)
    // para block //
    let paraheader = addblockheader(pge, MODABBREVLEN, toint.PARA, TYPEABBREVLEN)
    let a4 = finishblock(addrecords(paraheader, TYPEABBREVLEN, [ [ 2, 0]]), length.paraheader, TYPEABBREVLEN)
     // def list //
     let a5 = addrecords(a4, MODABBREVLEN, deflist)
      // const block //
      let g = subseq(constantrecords, length.deflist + 1, offset) @ constrecords(trackconst(a5,-1, 0), @e)
      let a6 = finishblock(bits.g, blockstart.g, TYPEABBREVLEN)
       llvmpartial(a6, h)

function constrecords(z:trackconst, l:slotrecord)trackconst
 // keep track of type of last const processed and add record when type changes //
 if ismoduleblock.l then
 let bits = if not.islastmodule.z then finishblock(bits.z, blockstart.z, TYPEABBREVLEN)else bits.z
   trackconst(addrecord(bits, MODABBREVLEN, record.l), typ.l, 0)
 else
  let newblock = islastmodule.z ∧ not.ismoduleblock.l
  let bits = if newblock then addblockheader(bits.z, MODABBREVLEN, toint.CONSTANTS, TYPEABBREVLEN)else bits.z
  let bits2 = if lasttype.z = typ.l then bits
  else
   addvbr6(add(bits, bits((1 * 64 + 1) * 16 + 3), 16), typ.l)
  let rec = record.l
  let tp = rec_1
  let bs = if tp = toint.CINTEGER then
  addvbrsigned6(add(bits2, bits((1 * 64 + toint.CINTEGER) * 16 + 3), 16), rec_2)
  else
   let a1 = if length.rec < 32 then
   add(bits2, bits(((length.rec - 1) * 64 + tp) * 16 + 3), 16)
   else addvbr6(addvbr6(addvbr(bits2, 3, TYPEABBREVLEN), tp), length.rec - 1)
    addvbr6(a1, subseq(rec, 2, length.rec))
   trackconst(bs, typ.l, if newblock then length.bits else blockstart.z)

Function symentries(bits:bitstream, s:seq.slotrecord, i:int)bitstream
 if i > length.s then bits
 else
  let l = s_i
  let bs = if ismoduleblock.l then
  let abbrevlength = 4
   let name = tointseq.symtablename.l
    if isempty.name then bits
    else
     let a1 = addvbr6(addvbr6(addvbr6(addvbr(bits, 3, abbrevlength), // rec type entry // 1), length.name + 1), i - 1)
      addvbr6(a1, name)
  else bits
   symentries(bs, s, i + 1)

type trackconst is record bits:bitstream, lasttype:int, blockstart:int

function islastmodule(l:trackconst)boolean lasttype.l < 0

type machineinfo is record triple:seq.byte, datalayout:seq.byte

builtin getmachineinfo machineinfo