#!/usr/local/bin/tau

/run llvmconstants generatecode

Module internalbc

* 64 + 2*3 instead of 64 + 2 * 3 does not give reasonable error message!

use seq.bitpackedseq.bit

use bitpackedseq.bit

use seq.bits

use bits

use fileio

use seq.internal2

use seq.internalbc

use stdlib

use seq.templatepart

use llvmconstants

Function BLOCKCOUNT(slot:int, a1:int)internalbc addstartbits(1, 1, add(a1, emptyinternalbc))


Function ret internalbc addstartbits(toint.RET, 0, emptyinternalbc)

Function RET(slot:slot,  a1:slot)internalbc addstartbits(toint.RET, 1, addaddress(slot, a1, emptyinternalbc))

Function CAST(slot:slot, a1:slot, a2:llvmtype, a3:int)internalbc
 addstartbits(toint.CAST, 3, addaddress(slot, a1, add(typ.a2, add(a3, emptyinternalbc))))


Function BR(slot:slot, a1:int, a2:int, a3:slot)internalbc
 addstartbits(toint.BR, 3, add(a1, add(a2, addaddress(slot, a3, emptyinternalbc))))

Function ALLOCA(slot:slot, a1:llvmtype, a2:llvmtype, a3:slot, a4:int)internalbc
 addstartbits(toint.ALLOCA, 4, add(typ.a1, add(typ.a2, add( toint.a3, add(a4, emptyinternalbc)))))

Function BR( a1:int)internalbc addstartbits(toint.BR, 1, add(a1, emptyinternalbc))

Function GEP(slot:slot, a2:llvmtype, a3:slot)internalbc
 addstartbits(toint.GEP, 3, add(1, add(typ.a2, addaddress(slot, a3, emptyinternalbc))))

Function GEP(slot:slot,  a2:llvmtype, a3:slot, a4:slot)internalbc
 addstartbits(toint.GEP, 4, add(1, add(typ.a2, addaddress(slot, a3, addaddress(slot, a4, emptyinternalbc)))))
 
Function STORE(slot:slot,a1:slot, a2:slot) internalbc
addstartbits(toint.STORE, 4, addaddress( slot, a1, addaddress( slot, a2, add(toint.align8, add(0, emptyinternalbc)))))
 
Function LOAD(slot:slot, a1:slot, a2:llvmtype)internalbc
 addstartbits(toint.LOAD, 4, addaddress(slot, a1, add(typ.a2, add(toint.align8, add(0, emptyinternalbc)))))

Function CMP2(slot:slot, a1:slot, a2:slot, a3:int)internalbc
 addstartbits(toint.CMP2, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))

function addaddress(loc:slot,a:slot,bc:internalbc) internalbc
 addaddress(-toint.loc,toint.a,bc)
 
 function addsignedaddress(loc:slot,a:slot,bc:internalbc) internalbc
 addsignedaddress(-toint.loc,toint.a,bc)


/Function BINOP(slot:int, a1:int, a2:int, a3:int)internalbc
 addstartbits(toint.BINOP, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))

Function BINOP(slot:slot, a1:slot, a2:slot, a3:binaryop)internalbc
 addstartbits(toint.BINOP, 3, addaddress(slot, a1, addaddress(slot, a2, add(toint.a3, emptyinternalbc))))

 
 Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot)internalbc
 addstartbits(toint.CALL, 4, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, emptyinternalbc)))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot)internalbc
 addstartbits(toint.CALL, 5, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, emptyinternalbc))))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot, a6:slot)internalbc
 addstartbits(toint.CALL, 6, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, emptyinternalbc)))))))



Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot, rest:seq.slot)internalbc
 addstartbits(toint.CALL, 5 + length.rest, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, args(slot, emptyinternalbc, rest, length.rest)))))))

Function CALLSTART(slot:int, a1:int, a2:int, a3:int, a4:int, noargs:int)internalbc
 addstartbits(toint.CALL, 4 + noargs, add(a1, add(a2, add(a3, addaddress(slot, a4, emptyinternalbc)))))

Function CALLFINISH(slot:int, rest:seq.int)internalbc args(slot, emptyinternalbc, rest, length.rest)

function args(slot:int, t:internalbc, rest:seq.int, i:int)internalbc
 if i = 0 then t else args(slot, addaddress(slot, rest_i, t), rest, i - 1)

use seq.slot

function args(slot:slot, t:internalbc, rest:seq.slot, i:int)internalbc
 if i = 0 then t else args(slot, addaddress(slot, rest_i, t), rest, i - 1)

 
 

Function PHI(slot:slot, a1:llvmtype, a2:slot, a3:int, a4:slot, a5:int, a6:slot, a7:int)internalbc
 addstartbits(toint.PHI, 7, add(typ.a1, addsignedaddress(slot, a2, add(a3, addsignedaddress(slot, a4, add(a5, addsignedaddress(slot, a6, add(a7, emptyinternalbc))))))))

Function PHI(slot:slot, a1:llvmtype, a2:slot, a3:int, a4:slot, a5:int)internalbc
 addstartbits(toint.PHI, 5, add(typ.a1, addsignedaddress(slot, a2, add(a3, addsignedaddress(slot, a4, add(a5, emptyinternalbc))))))

Function PHI(slot:int, a1:int, s:seq.int)internalbc
 addstartbits(toint.PHI, length.s + 1, add(a1, subphi(slot, emptyinternalbc, s, length.s)))

function subphi(slot:int, b:internalbc, s:seq.int, i:int)internalbc
 if i > 1 then
 subphi(slot, addsignedaddress(slot, s_(i - 1), add(s_i, b)), s, i - 2)
 else b

function addpair(tailphi:seq.int, slot:int, p:int, a:internalbc, b:int)internalbc
 addsignedaddress(slot, tailphi_(b + p), add(tailphi_b, a))

(block1, p11, p12, p13, block2, p21, p22, p23)phi(p11, block1, p21, block2)

function phiinst(slot:int, typ:int, tailphi:seq.int, nopara:int, p:int)internalbc
 let t = @(addpair(tailphi, slot + p, p), identity, emptyinternalbc, arithseq(length.tailphi / (nopara + 1), - nopara - 1, length.tailphi - nopara))
  addstartbits(toint.PHI, length.tailphi / (nopara + 1) * 2 + 1, add(typ, t))

Function phiinst(slot:int, typ:int, tailphi:seq.int, nopara:int)internalbc
 @(+, phiinst(slot, typ, tailphi, nopara), emptyinternalbc, arithseq(nopara, 1, 1))

Function addstartbits(inst:int, noargs:int, b:internalbc)internalbc
 if noargs > 31 ∨ inst > 31 ∨ bitcount.b > 56 - 16 then
 let c = add(inst, add(noargs, b))
   if bitcount.c > 56 - 4 then internalbc(3, 4, finish.c)
   else internalbc(bits.c * 16 + 3, bitcount.c + 4, done.c)
 else
  internalbc(((bits.b * 64 + noargs) * 64 + inst) * 16 + 3, bitcount.b + (6 + 6 + 4), done.b)

/ function asbits(k:internalbc)seq.word let s = toseq.addtobitstream(10000, empty:bitpackedseq.bit, k)@(+, toword,"", @(+, toint, empty:seq.int, s))

/use seq.bit

/use bits

type internalbc is record bits:int, bitcount:int, done:seq.int

Function done(internalbc)seq.int export

Function bitcount(internalbc)int export

Function bits(internalbc)int export

Function print(a:internalbc)seq.word print1(finish.a, 1,"")

function print1(a:seq.int, i:int, result:seq.word)seq.word
 if i > length.a then result
 else
  let val = a_i
  let nobits = toint(bits.val ∧ bits.63)
   if nobits = reloc then
   print1(a, i + 1, result + " &br reloc" + toword(toint(bits.val >> 6) - relocoffset))
   else
    // if val = vbr6 then print1(a, i + 2, result +"vbr6"+ toword(a_(i + 1)))else //
    if val = sub1 then
    print1(a, i + 2, result + "sub11" + toword.a_(i + 1))
    else if val = sub2 then
    print1(a, i + 2, result + "sub22" + toword.a_(i + 1))
    else
     let bits = toint(bits.val >> 6)
      print1(a, i + 1, result + [ toword.bits,":"_1, toword.nobits])

Function emptyinternalbc internalbc internalbc(0, 0, empty:seq.int)

Function +(a:internalbc, b:internalbc)internalbc
 if length.done.a > 0 ∨ bitcount.a + bitcount.b > 56 then
 internalbc(bits.a, bitcount.a, done.a + finish.b)
 else
  internalbc(bits.b * 2^(bitcount.a) + bits.a, bitcount.a + bitcount.b, done.b)

Function finish(b:internalbc)seq.int
 if bitcount.b = 0 then done.b
 else [ bits.b * 64 + bitcount.b] + done.b

Function addaddress(slot:int, a:int, b:internalbc)internalbc
 if - a > slot then
 if a = ibcfirstpara2 then internalbc(0, 0, [ firstpara2] + finish.b)
  else
   internalbc(0
   , 0
   , [ if a = ibcsub1 then sub1
   else if a = ibcsub2 then sub2
   else
    assert a = ibcsub3 report"unknown code in addaddress"
     sub3
   , slot]
   + finish.b)
 else if a < 0 then add(slot + a, b)
 else
  internalbc(0, 0, [ reloc + 64 * (relocoffset + a - slot + 1)] + finish.b)

Function addsignedaddress(slot:int, a:int, b:internalbc)internalbc
 if a ≤ 0 then
 let v = slot + a
  let c = if v ≥ 0 then 2 * v else 2 * - v + 1
   add(c, b)
 else internalbc(0, 0, [ relocsigned, a - slot + 1] + finish.b)

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

type internal2 is record state:int, offset:int, result:bitpackedseq.bit

Function addtobitstream(offset:int, bs:bitpackedseq.bit, b:internalbc)bitpackedseq.bit result.@(add2.offset, identity, internal2(0, offset, bs), finish.b)

function add2(offset:int, r:internal2, val:int)internal2
 // FORCEINLINE
 . //
 let nobits = toint(bits.val ∧ bits.63)
 let bits = bits.val >> 6
 let newstate = if state.r = 0 ∧ nobits = 63 then val else 0
 let newoffset = if nobits = setoffset ∧ state.r = 0 then offset + toint.bits else offset.r
 let newresult = if state.r = 0 then
 if nobits < 58 then add(result.r, bits, nobits)
  else if nobits = reloc then addvbr6(result.r, offset.r - (toint.bits - relocoffset))
  else if val = firstpara2 then addvbr6(result.r, offset.r - offset + 1)else result.r
 else
  assert state.r = relocsigned report"invalid code" + toword.state.r
   addvbrsigned6(result.r, offset.r - val)
  internal2(newstate, newoffset, newresult)

Function internalbc(bits:int, bitcount:int, done:seq.int)internalbc export

Function isempty(a:internalbc)boolean bitcount.a = 0 ∧ length.done.a = 0

// Function vbr6 int 63 + 64 //

function relocsigned int 63 + 64 * 3

function reloc int 60

Function ibcfirstpara2 int // must be big enough value so - ibcirstpart2 > max slot number in function // 0 - 6400000

function relocoffset int 1024 * 1024 * 1024 * 1024

Function sub1 int 61 + 64 * 5001

Function sub2 int 61 + 64 * 5002

Function sub3 int 61 + 64 * 5003

Function ibcsub1 int 0 - 6400001

Function ibcsub2 int 0 - 6400002

Function ibcsub3 int 0 - 6400003

function firstpara2 int 58

function setoffset int 59

Function ibcsubpara(i:int)int(i - 61) / 64 - 5000



Function type:templatepart internaltype export

Function type:internalbc internaltype export

type templatepart is record part:seq.int, loc:int, parano:int

Function parano(templatepart)int export

Function getparts(a:internalbc)seq.templatepart subgetparts(finish.a, 0, 0, 1, 1)

function subgetparts(a:seq.int, lastloc:int, lastparano:int, lastindex:int, i:int)seq.templatepart
 // finds template parameters and breaks template into parts. //
 if i > length.a then [ templatepart(subseq(a, lastindex, i - 1), lastloc, lastparano)]
 else
  let val = a_i
  let bits = toint(bits.val ∧ bits.63)
   if bits = 61 then
   let p = ibcsubpara.val
     if p in [ 1, 2, 3]then
     [ templatepart(subseq(a, lastindex, i - 1), lastloc, lastparano)]
      + subgetparts(a, a_(i + 1), p, i + 2, i + 2)
     else subgetparts(a, lastloc, lastparano, lastindex, i + 2)
   else if bits = 63 then subgetparts(a, lastloc, lastparano, lastindex, i + 2)else subgetparts(a, lastloc, lastparano, lastindex, i + 1)

function processtemplatepart(deltaoffset:int, args:seq.int, t:templatepart)seq.int
 if parano.t = 0 then part.t
 else
  let arg = args_(parano.t)
   {(if arg < 0 then
   // [ vbr6, deltaoffset + loc(t)+ arg]//
    finish.add(deltaoffset + loc.t + arg, emptyinternalbc)
   else [ reloc + 64 * (relocoffset + arg - loc.t + 1)])
   + part.t }

Function processtemplate(s:seq.templatepart, deltaoffset:int, args:seq.int)internalbc
 internalbc(0, 0, [ setoffset + 64 * deltaoffset] + @(+, processtemplatepart(deltaoffset, args), empty:seq.int, s)
 + [ setoffset])

_____________________________

Function addvbr(b:bitpackedseq.bit, newbits:int, bitcount:int)bitpackedseq.bit
 let limit = toint(bits.1 << bitcount - 1)
  if newbits < limit then add(b, bits.newbits, bitcount)
  else
   let firstchunk = bits(limit - 1) ∧ bits.newbits ∨ bits.limit
   let secondchunk = bits.newbits >> bitcount - 1
    assert toint.secondchunk < limit report"vbr encoding for value is not handled" + toword.newbits + toword.limit
     add(b, secondchunk << bitcount ∨ firstchunk, bitcount * 2)

function addvbr6(b:bits, bitstoadd:int, leftover:bits, s:seq.int, r:bitpackedseq.bit, i:int)bitpackedseq.bit
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

Function addvbr6(b:bitpackedseq.bit, s:seq.int)bitpackedseq.bit addvbr6(bits.0, 0, bits.0, s, b, 1)

Function addvbr6(b:bitpackedseq.bit, v:int)bitpackedseq.bit addvbr6(bits.0, 0, bits.0, [ v], b, 1)

Function addvbrsigned6(b:bitpackedseq.bit, val:int)bitpackedseq.bit
 if val < 0 then
 if val > -16 then addvbr6(b, 2 * - val + 1)
  else
   let chunk = bits(32 + - val mod 16 * 2 + 1)
    addvbr6(chunk, 6, bits.- val >> 4, empty:seq.int, b, 1)
 else if val < 16 then addvbr6(b, 2 * val)
 else
  let chunk = bits(32 + val mod 16 * 2)
   addvbr6(chunk, 6, bits.val >> 4, empty:seq.int, b, 1)

Function align32(a:bitpackedseq.bit)bitpackedseq.bit
 let k = length.a mod 32
  if k = 0 then a else add(a, bits.0, 32 - k)
  
use seq.bitpackedseq.bit

use bitpackedseq.bit

use seq.seq.bit

use seq.bit

use seq.seq.bits

use seq.bits

use bits


use blockseq.int

use seq.seq.seq.int

use seq.seq.int

use seq.seq.internalbc

use seq.internalbc

use internalbc


use seq.slotrecord


use stdlib

use llvm

use UTF8

use seq.trackconst

use llvmconstants


Function addblockheader(b:bitpackedseq.bit, currentabbrelength:int, blockid:int, abbrevlength:int)bitpackedseq.bit
 addvbr(align32.addvbr(addvbr(addvbr(b, ENTERBLOCK, currentabbrelength), blockid, 8), abbrevlength, 4), 0, 32)

Function finishblock(current:bitpackedseq.bit, headerplace:int, blockabbrevlength:int)bitpackedseq.bit
 if headerplace = 0 then current
 else
  let bb = align32.addvbr(current, ENDBLOCK, blockabbrevlength)
  let len =(length.bb - headerplace) / 32
   // assert false report"X"+ toword(length.header -32)+ toword.len // patch(bb, headerplace - 31, len)

Function addbody(offset:int, abbrevlen:int, m:bitpackedseq.bit, bodytxt:internalbc)bitpackedseq.bit
 let header = addblockheader(m, abbrevlen, toint.FUNCTIONBLK, 4)
  finishblock(addtobitstream(offset, header, bodytxt), length.header, 4)

Function addrecords(bits:bitpackedseq.bit, abbrevlength:int, s:seq.seq.int)bitpackedseq.bit @(addrecord.abbrevlength, identity, bits, s)

function addrecord(abbrevlength:int, bits:bitpackedseq.bit, a:seq.int)bitpackedseq.bit
 let a1 = addvbr(bits, 3, abbrevlength)
 let a2 = addvbr6(addvbr6(a1, a_1), length.a - 1)
  @(addvbr6, identity, a2, subseq(a, 2, length.a))

function ENDBLOCK int 0

function ENTERBLOCK int 1

Function llvm(deflist:seq.seq.int, bodytxts:seq.internalbc, trecords:seq.seq.int)seq.bits
 let MODABBREVLEN = 3
 let TYPEABBREVLEN = 4
 let offset = length.constantrecords
 let h = addblockheader(add(add(add(add(empty:bitpackedseq.bit, bits.66, 8), bits.67, 8), bits.192, 8), bits.222, 8)
 , 2
 , toint.MODULE
 , MODABBREVLEN)
 let info = getmachineinfo
 let a = addrecords(h, MODABBREVLEN, [ [ 1, 1], [  toint.TRIPLE] + triple.info, [  toint.LAYOUT] + datalayout.info])
  // type block //
  let typeheader = addblockheader(a, MODABBREVLEN, toint.TYPES, TYPEABBREVLEN)
  let a2 = addrecords(typeheader, TYPEABBREVLEN, [ [ toint.NumEle, length.trecords]] + trecords)
  let a3 = finishblock(a2, length.typeheader, TYPEABBREVLEN)
   // PARAGRPBLOCK //
   let pgh = addblockheader(a3, MODABBREVLEN, toint.PARAGRP, TYPEABBREVLEN)
   let pge = finishblock(addrecords(pgh
   , TYPEABBREVLEN
   , [ [ 3, 0, 2^32 - 1, 0, 14, 0, 26, 0, 18] + [ 3]
   + tointseq.@(+, decodeword, empty:seq.char,"no - frame - pointer - elim - non - leaf")
   + [ 0]])
   , length.pgh
   , TYPEABBREVLEN)
    // para block //
    let paraheader = addblockheader(pge, MODABBREVLEN, toint.PARA, TYPEABBREVLEN)
    let a4 = finishblock(addrecords(paraheader, TYPEABBREVLEN, [ [ 2, 0]]), length.paraheader, TYPEABBREVLEN)
     // def list //
     let a5 = addrecords(a4, MODABBREVLEN, deflist)
      // const block //
      let g = @(constrecords, identity, trackconst(a5, -1, 0), subseq(constantrecords, length.deflist + 1, offset))
      let a6 = finishblock(bits.g, blockstart.g, TYPEABBREVLEN)
       // function bodies //
       // assert length.trecords = length.typerecords report"X"//
       let a7 = @(addbody(offset, MODABBREVLEN), identity, a6, bodytxts)
        // sym table //
        let symtabheader = addblockheader(a7, MODABBREVLEN, toint.VALUESYMTABLE, TYPEABBREVLEN)
        let a8 = finishblock(symentries(symtabheader, constantrecords, 1), length.symtabheader, TYPEABBREVLEN)
         // finish module block // data2.align.finishblock(a8, length.h, MODABBREVLEN)

function constrecords(z:trackconst, l:slotrecord)trackconst
 // keep track of type of last const processed and add record when type changes //
 let MODABBREVLEN = 3
 let TYPEABBREVLEN = 4
  if ismoduleblock.l   then
  let bits = if not.islastmodule.z then finishblock(bits.z, blockstart.z, TYPEABBREVLEN)else bits.z
      trackconst(addrecord(MODABBREVLEN, bits, record.l), typ.l, 0)
  else
   let newblock = islastmodule.z  ∧ not.ismoduleblock.l 
   let bits = if newblock then addblockheader(bits.z, MODABBREVLEN, toint.CONSTANTS , TYPEABBREVLEN)else bits.z
   let bits2 = if lasttype.z = typ.l then bits
   else
    addvbr6(add(bits, bits((1 * 64 + 1) * 16 + 3), 16), typ.l)
    let rec=record.l
   let tp =rec_1
   let bs = if tp = toint.CINTEGER then
   addvbrsigned6(add(bits2, bits((1 * 64 + toint.CINTEGER) * 16 + 3), 16),rec_2)
   else
    let a1 = if length.rec < 32 then
    add(bits2, bits(((length.rec - 1) * 64 + tp) * 16 + 3), 16)
    else addvbr6(addvbr6(addvbr(bits2, 3, TYPEABBREVLEN), tp), length.rec - 1)
     addvbr6(a1, subseq(rec, 2, length.rec))
    trackconst(bs, typ.l, if newblock then length.bits else blockstart.z)
    
    use seq.int

Function symentries(bits:bitpackedseq.bit, s:seq.slotrecord, i:int)bitpackedseq.bit
 if i > length.s then bits
 else
  let l = s_i
  let bs = if ismoduleblock.l  then
  let abbrevlength = 4
  let name=tointseq.symtablename.l
  if isempty.name then bits
  else 
   let a1 = addvbr6(addvbr6(addvbr6(addvbr(bits, 3, abbrevlength),// rec type entry // 1), length.name + 1), i - 1)
    addvbr6(a1, name)
  else bits
   symentries(bs, s, i + 1)

type trackconst is record bits:bitpackedseq.bit, lasttype:int, blockstart:int

function islastmodule (l:trackconst) boolean
   lasttype.l < 0 

type machineinfo is record triple:seq.int, datalayout:seq.int

function getmachineinfo machineinfo builtin.usemangle




module llvmconstants 

use stdlib

 function generatecode seq.word
 // generates code in this module beyond --------- //
   enumerate("align","unspecified  ? ? ? align8 align16 align32 align64")
   +enumerate("instop","? BLOCK BINOP CAST ? SELECT ? ? ? ?   RET BR ? ? ? ? PHI ? ? ALLOCA LOAD
? ? ?  ? ? ? ?  CMP2 ? ? ? ? ? CALL ? ? ? ? ? ? ? ?  GEP STORE")
   +enumerate( "typeop","? NumEle TVOID ? DOUBLE ? OPAQUE INTEGER POINTER ? ? ARRAY ? ? ? ? ? ? ? ? ? FUNCTION")
   +enumerate( "blockop",
    "INFOBLOCK ? ? ? ? ? ? ? MODULE PARA PARAGRP CONSTANTS FUNCTIONBLK ? VALUESYMTABLE ? ? TYPES")
   +enumerate("moduleop","? Version TRIPLE LAYOUT ? ? ? GLOBALVAR FUNCTIONDEC")
   +enumerate("constop", "? SETTYPE CNULL CUNDEF CINTEGER CWIDEINTEGER CFLOAT  CAGGREGATE CSTRING2 CSTRING0 CBINOP CCAST 
 ? ? ? ? ? ? ? ? CGEP ? CDATA")
    +enumerate("castop","trunc zext sext fptoui fptosi uitofp sitofp fptrunc fpext ptrtoint inttoptr bitcast")
    +enumerate("binaryop","add sub mul udiv sdiv urem srem shl lshr ashr and or xor")
    +enumerate("cmp2op" ,"? ? ? ? ? ? ? ? ? ?
   ? ? ? ? ? ? ? ? ? ?
     ? ? ? ? ? ? ? ? ? ? ? ?
    eq ? ? ? ? ?  sgt")

  

   
function enumerate(type:seq.word,codes:seq.word) seq.word
 "type"+type+"is record toint:int"+
  "&br &br Function decode(code:" +type+ ") seq.word" 
 +"&br let i=toint.code if between(i+ 1,1,"+toword.length.codes+")  then "
 +   ' &br let r=[" ' +codes+ ' "_(i+1)]  if not(r= "?") then r else " ' + type+ ' " +toword.i '  
 +  ' &br  else " ' + type+ ' " +toword.i ' 
 +"&br &br function toint("+type+") int export"
 +"&br &br function "+type+"(i:int) "+type+" export"
+"&br &br function type:"+type+" internaltype export"
+"&br &br Function =(a:"+type+",b:"+type+") boolean  toint.a=toint.b"
 + @(+,dd(type,codes),"",arithseq(length.codes,1,1))
+"&br &br"

 function dd(type:seq.word,w:seq.word,i:int) seq.word
   if w_i ="?"_1 then "" else
   "&br &br Function "+w_i +type + type+"."+toword.(i-1)



--------------------------

type align is record toint:int 

Function decode(code:align)seq.word 
let i = toint.code if between(i + 1, 1, 8)then 
let r = ["unspecified ? ? ? align8 align16 align32 align64"_(i + 1)]if not(r ="?")then r else"align"+ toword.i 
else"align"+ toword.i 

function toint(align)int export 

function align(i:int)align export 

function type:align internaltype export 

Function =(a:align, b:align)boolean toint.a = toint.b 

Function unspecified align align.0 

Function align8 align align.4 

Function align16 align align.5 

Function align32 align align.6 

Function align64 align align.7 

type instop is record toint:int 

Function decode(code:instop)seq.word 
let i = toint.code if between(i + 1, 1, 45)then 
let r = ["? BLOCK BINOP CAST ? SELECT ? ? ? ? RET BR ? ? ? ? PHI ? ? ALLOCA LOAD ? ? ? ? ? ? ? CMP2 ? ? ? ? ? CALL ? ? ? ? ? ? ? ? GEP STORE"_(i + 1)]if not(r ="?")then r else"instop"+ toword.i 
else"instop"+ toword.i 

function toint(instop)int export 

function instop(i:int)instop export 

function type:instop internaltype export 

Function =(a:instop, b:instop)boolean toint.a = toint.b 

Function BLOCK instop instop.1 

Function BINOP instop instop.2 

Function CAST instop instop.3 

Function SELECT instop instop.5 

Function RET instop instop.10 

Function BR instop instop.11 

Function PHI instop instop.16 

Function ALLOCA instop instop.19 

Function LOAD instop instop.20 

Function CMP2 instop instop.28 

Function CALL instop instop.34 

Function GEP instop instop.43 

Function STORE instop instop.44 

type typeop is record toint:int 

Function decode(code:typeop)seq.word 
let i = toint.code if between(i + 1, 1, 22)then 
let r = ["? NumEle TVOID ? DOUBLE ? OPAQUE INTEGER POINTER ? ? ARRAY ? ? ? ? ? ? ? ? ? FUNCTION"_(i + 1)]if not(r ="?")then r else"typeop"+ toword.i 
else"typeop"+ toword.i 

function toint(typeop)int export 

function typeop(i:int)typeop export 

function type:typeop internaltype export 

Function =(a:typeop, b:typeop)boolean toint.a = toint.b 

Function NumEle typeop typeop.1 

Function TVOID typeop typeop.2 

Function DOUBLE typeop typeop.4 

Function OPAQUE typeop typeop.6 

Function INTEGER typeop typeop.7 

Function POINTER typeop typeop.8 

Function ARRAY typeop typeop.11 

Function FUNCTION typeop typeop.21 

type blockop is record toint:int 

Function decode(code:blockop)seq.word 
let i = toint.code if between(i + 1, 1, 18)then 
let r = ["INFOBLOCK ? ? ? ? ? ? ? MODULE PARA PARAGRP CONSTANTS FUNCTIONBLK ? VALUESYMTABLE ? ? TYPES"_(i + 1)]if not(r ="?")then r else"blockop"+ toword.i 
else"blockop"+ toword.i 

function toint(blockop)int export 

function blockop(i:int)blockop export 

function type:blockop internaltype export 

Function =(a:blockop, b:blockop)boolean toint.a = toint.b 

Function INFOBLOCK blockop blockop.0 

Function MODULE blockop blockop.8 

Function PARA blockop blockop.9 

Function PARAGRP blockop blockop.10 

Function CONSTANTS blockop blockop.11 

Function FUNCTIONBLK blockop blockop.12 

Function VALUESYMTABLE blockop blockop.14 

Function TYPES blockop blockop.17 

type moduleop is record toint:int 

Function decode(code:moduleop)seq.word 
let i = toint.code if between(i + 1, 1, 9)then 
let r = ["? Version TRIPLE LAYOUT ? ? ? GLOBALVAR FUNCTIONDEC"_(i + 1)]if not(r ="?")then r else"moduleop"+ toword.i 
else"moduleop"+ toword.i 

function toint(moduleop)int export 

function moduleop(i:int)moduleop export 

function type:moduleop internaltype export 

Function =(a:moduleop, b:moduleop)boolean toint.a = toint.b 

Function Version moduleop moduleop.1 

Function TRIPLE moduleop moduleop.2 

Function LAYOUT moduleop moduleop.3 

Function GLOBALVAR moduleop moduleop.7 

Function FUNCTIONDEC moduleop moduleop.8 

type constop is record toint:int 

Function decode(code:constop)seq.word 
let i = toint.code if between(i + 1, 1, 23)then 
let r = ["? SETTYPE CNULL CUNDEF CINTEGER CWIDEINTEGER CFLOAT CAGGREGATE CSTRING2 CSTRING0 CBINOP CCAST ? ? ? ? ? ? ? ? CGEP ? CDATA"_(i + 1)]if not(r ="?")then r else"constop"+ toword.i 
else"constop"+ toword.i 

function toint(constop)int export 

function constop(i:int)constop export 

function type:constop internaltype export 

Function =(a:constop, b:constop)boolean toint.a = toint.b 

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

type castop is record toint:int 

Function decode(code:castop)seq.word 
let i = toint.code if between(i + 1, 1, 12)then 
let r = ["trunc zext sext fptoui fptosi uitofp sitofp fptrunc fpext ptrtoint inttoptr bitcast"_(i + 1)]if not(r ="?")then r else"castop"+ toword.i 
else"castop"+ toword.i 

function toint(castop)int export 

function castop(i:int)castop export 

function type:castop internaltype export 

Function =(a:castop, b:castop)boolean toint.a = toint.b 

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

type binaryop is record toint:int 

Function decode(code:binaryop)seq.word 
let i = toint.code if between(i + 1, 1, 13)then 
let r = ["add sub mul udiv sdiv urem srem shl lshr ashr and or xor"_(i + 1)]if not(r ="?")then r else"binaryop"+ toword.i 
else"binaryop"+ toword.i 

function toint(binaryop)int export 

function binaryop(i:int)binaryop export 

function type:binaryop internaltype export 

Function =(a:binaryop, b:binaryop)boolean toint.a = toint.b 

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

type cmp2op is record toint:int 

Function decode(code:cmp2op)seq.word 
let i = toint.code if between(i + 1, 1, 39)then 
let r = ["? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? eq ? ? ? ? ? sgt"_(i + 1)]if not(r ="?")then r else"cmp2op"+ toword.i 
else"cmp2op"+ toword.i 

function toint(cmp2op)int export 

function cmp2op(i:int)cmp2op export 

function type:cmp2op internaltype export 

Function =(a:cmp2op, b:cmp2op)boolean toint.a = toint.b 

Function eq cmp2op cmp2op.32 

Function sgt cmp2op cmp2op.38 
