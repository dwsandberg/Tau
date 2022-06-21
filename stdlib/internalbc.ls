Module internalbc

use UTF8

use bits

use bitstream

use llvm

use llvmconstants

use standard

use seq.slot

use seq.slotrecord

use seq.templatepart

use seq.seq.int

type templatepart is val:bits

function bits(b:templatepart)bits val.b >> 6

function bitcount(b:templatepart)int toint(val.b ∧ 0x3F)

function templatepart(bits:int, bitcount:int)templatepart templatepart(tobits.bits << 6 ∨ bits.bitcount)

function templatepart(para:int, slot:int, bitcount:int)templatepart templatepart(tobits.para << 6 ∨ bits.bitcount ∨ bits.slot << 10)

function signedvalue(valx:templatepart)int
toint.if toint.val.valx < 0 then bits.valx ∨ 0xFC00000000000000 else bits.valx

function ibcsubpara(a:templatepart)int toint(val.a >> 6 ∧ 0xF)

function ibcsubslot(a:templatepart)int toint(val.a >> 10)

function Reloc int 60

function Substitue int 61

function Firstpara int 62

function Relocsigned int 63

Function ibcfirstpara2 int toint(0x1 << 40)

Function ibcsub(i:int)slot slot(ibcfirstpara2 + i)

type internalbc is parts:seq.templatepart

Function print(bc:internalbc)seq.word
for acc = "", e ∈ parts.bc do acc + print.val.e /for(acc)

function tail(b:internalbc)seq.templatepart parts.b << 1

function val(b:internalbc)templatepart first.parts.b

Function emptyinternalbc internalbc internalbc.empty:seq.templatepart

function bits(b:internalbc)bits if isempty.parts.b then 0x0 else bits.val.b

function bitcount(b:internalbc)int if isempty.parts.b then 0 else bitcount.val.b

function internalbc(bits:int, bitcount:int, tail:seq.templatepart)internalbc internalbc([templatepart(bits, bitcount)] + tail)

function internalbc(bits:bits, bitcount:int, tail:seq.templatepart)internalbc
internalbc([templatepart(toint.bits, bitcount)] + tail)

Function +(a:internalbc, b:internalbc)internalbc
if length.parts.a > 1 ∨ bitcount.a + bitcount.b > 56 then internalbc(bits.a, bitcount.a, tail.a + parts.b)
else internalbc(bits.b << bitcount.a ∨ bits.a, bitcount.a + bitcount.b, tail.b)

function addplaceholder(t:templatepart, b:internalbc)internalbc internalbc([t] + parts.b)

function add6bits(val:int, b:internalbc)internalbc
if bitcount.b > 56 - 6 then internalbc(val, 6, parts.b)
else internalbc(bits.b << 6 ∨ tobits.val, bitcount.b + 6, tail.b)

function add4bits(val:int, b:internalbc)internalbc
if bitcount.b > 56 - 4 then internalbc(val, 4, parts.b)
else internalbc(bits.b << 4 ∨ tobits.val, bitcount.b + 4, tail.b)

Function addtobitstream(offset:int, bs:bitstream, b:internalbc)bitstream
for acc = bs, @e ∈ parts.b do add2(acc, offset, @e)/for(acc)

function add2(result:bitstream, offset:int, valx:templatepart)bitstream
let nobits = bitcount.valx
if nobits < 58 then add(result, bits.valx, nobits)
else if nobits = Reloc then addvbr6(result, offset - signedvalue.valx)
else if nobits = Firstpara then addvbr6(result, toint.bits.valx)
else if nobits = Relocsigned then addvbrsigned6(result, offset - signedvalue.valx)else result

function add(val:int, b:internalbc)internalbc
if val < 32 then add6bits(val, b)
else add6bits(toint(bits.val ∧ bits.31 ∨ bits.32), add(val / 32, b))

function addstartbits(inst:int, noargs:int, b:internalbc)internalbc add4bits(3, add(inst, add(noargs, b)))

function processtemplatepart(deltaoffset:int, args:seq.int, t:templatepart)seq.templatepart
let bits = bitcount.t
if bits < 58 then[t]
else if bits = Substitue then
 let arg = args_(ibcsubpara.t)
 if arg < 0 then parts.add(deltaoffset + ibcsubslot.t + arg, emptyinternalbc)
 else[templatepart(arg - ibcsubslot.t - deltaoffset + 1, Reloc)]
else if bits = Reloc then[templatepart.tobits(toint.val.t - 64 * deltaoffset)]
else
 assert bits = Firstpara report"Problem with code templates"
 [templatepart.tobits(toint.val.t + 64 * deltaoffset)]

Function processtemplate(s:internalbc, deltaoffset:int, args:seq.int)internalbc
internalbc.for acc = empty:seq.templatepart, @e ∈ parts.s do acc + processtemplatepart(deltaoffset, args, @e)/for(acc)

function addaddress(slot:int, a:int, b:internalbc)internalbc
if a < 0 then add(slot + a, b)
else
 let d = a - ibcfirstpara2
 if d < 0 then addplaceholder(templatepart(a - slot + 1, Reloc), b)
 else if d = 0 then addplaceholder(templatepart(slot - 1, Firstpara), b)
 else addplaceholder(templatepart(d, slot, Substitue), b)

function addsignedaddress(slot:int, a:int, b:internalbc)internalbc
if a ≤ 0 then
 let v = slot + a
 let c = if v ≥ 0 then 2 * v else 2 * -v + 1
 add(c, b)
else addplaceholder(templatepart(a - slot + 1, Relocsigned), b)

Export type:internalbc

Export type:templatepart

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
addstartbits(toint.GEP
, 4
, add(1, add(typ.a2, addaddress(slot, a3, addaddress(slot, a4, emptyinternalbc))))
)

Function STORE(slot:slot, a1:slot, a2:slot)internalbc
addstartbits(toint.STORE
, 4
, addaddress(slot, a1, addaddress(slot, a2, add(toint.align8, add(0, emptyinternalbc))))
)

Function LOAD(slot:slot, a1:slot, a2:llvmtype)internalbc
addstartbits(toint.LOAD
, 4
, addaddress(slot, a1, add(typ.a2, add(toint.align8, add(0, emptyinternalbc))))
)

Function CMP2(slot:slot, a1:slot, a2:slot, a3:int)internalbc
addstartbits(toint.CMP2, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))

Function BINOP(slot:slot, a1:slot, a2:slot, a3:binaryop)internalbc
addstartbits(toint.BINOP, 3, addaddress(slot, a1, addaddress(slot, a2, add(toint.a3, emptyinternalbc))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot)internalbc
addstartbits(toint.CALL, 4, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, emptyinternalbc)))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot)internalbc
addstartbits(toint.CALL
, 5
, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, emptyinternalbc)))))
)

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot, a6:slot)internalbc
addstartbits(toint.CALL
, 6
, add(a1
, add(a2
, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, emptyinternalbc))))
)
)
)

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot, a6:slot, a7:slot)internalbc
addstartbits(toint.CALL
, 7
, add(a1
, add(a2
, add(typ.a3
, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, emptyinternalbc))))
)
)
)
)

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot, rest:seq.slot)internalbc
addstartbits(toint.CALL
, 5 + length.rest
, add(a1
, add(a2
, add(typ.a3
, addaddress(slot, a4, addaddress(slot, a5, args(slot, emptyinternalbc, rest, length.rest)))
)
)
)
)

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
, add(typ.a1
, addsignedaddress(slot
, a2
, add(a3
, addsignedaddress(slot, a4, add(a5, addsignedaddress(slot, a6, add(a7, emptyinternalbc))))
)
)
)
)

Function PHI(slot:slot, a1:llvmtype, a2:slot, a3:int, a4:slot, a5:int)internalbc
addstartbits(toint.PHI
, 5
, add(typ.a1
, addsignedaddress(slot, a2, add(a3, addsignedaddress(slot, a4, add(a5, emptyinternalbc))))
)
)

Function PHI(slot:int, a1:int, s:seq.int)internalbc
addstartbits(toint.PHI, length.s + 1, add(a1, subphi(slot, emptyinternalbc, s, length.s)))

function subphi(slot:int, b:internalbc, s:seq.int, i:int)internalbc
if i > 1 then subphi(slot, addsignedaddress(slot, s_(i - 1), add(s_i, b)), s, i - 2)else b

function addpair(a:internalbc, tailphi:seq.int, slot:int, p:int, b:int)internalbc
addsignedaddress(slot, tailphi_(b + p), add(tailphi_b, a))

(block1, p11, p12, p13, block2, p21, p22, p23)phi(p11, block1, p21, block2)

Function phiinst(slot:int, typ:seq.int, tailphi:seq.int, nopara:int)internalbc
for acc = emptyinternalbc, @e ∈ arithseq(nopara, 1, 1)do acc + phiinst(slot, typ, tailphi, nopara, @e)/for(acc)

function phiinst(slot:int, typ:seq.int, tailphi:seq.int, nopara:int, p:int)internalbc
{let t=@(addpair(tailphi, slot+p, p), identity, emptyinternalbc, arithseq(length.tailphi /(nopara+1), -nopara 
-1, length.tailphi-nopara))}
let t = 
 for acc = emptyinternalbc
 , @e ∈ arithseq(length.tailphi / (nopara + 1), -nopara - 1, length.tailphi - nopara)
 do addpair(acc, tailphi, slot + p, p, @e)/for(acc)
addstartbits(toint.PHI, length.tailphi / (nopara + 1) * 2 + 1, add(typ_p, t))

function addsignedaddress(loc:slot, a:slot, bc:internalbc)internalbc addsignedaddress(-toint.loc, toint.a, bc)

function addaddress(locin:slot, a:slot, bc:internalbc)internalbc
let slot = -toint.locin
addaddress(slot, toint.a, bc)

Function addvbr(b:bitstream, newbits:int, bitcount:int)bitstream
let limit = toint(bits.1 << (bitcount - 1))
if newbits < limit then add(b, bits.newbits, bitcount)
else
 let firstchunk = bits(limit - 1) ∧ bits.newbits ∨ bits.limit
 let secondchunk = bits.newbits >> (bitcount - 1)
 assert toint.secondchunk < limit
 report"vbr encoding for value is not handled" + toword.newbits + toword.limit
 add(b, secondchunk << bitcount ∨ firstchunk, bitcount * 2)

function addvbr6(b:bits, bitstoadd:int, leftover:bits, s:seq.int, r:bitstream, i:int)bitstream
if bitstoadd > 58 then addvbr6(bits.0, 0, leftover, s, add(r, b, bitstoadd), i)
else if toint.leftover > 0 then
 if toint.leftover < 32 then addvbr6(b ∨ leftover << bitstoadd, bitstoadd + 6, bits.0, s, r, i)
 else addvbr6(b ∨ (leftover ∧ bits.31 ∨ bits.32) << bitstoadd, bitstoadd + 6, leftover >> 5, s, r, i)
else if i > length.s then if bitstoadd = 0 then r else add(r, b, bitstoadd)
else
 let v = s_i
 if v < 32 then addvbr6(b ∨ bits.v << bitstoadd, bitstoadd + 6, bits.0, s, r, i + 1)
 else addvbr6(b ∨ (bits.v ∧ bits.31 ∨ bits.32) << bitstoadd, bitstoadd + 6, bits.v >> 5, s, r, i + 1)

function addvbr6(b:bitstream, s:seq.int)bitstream addvbr6(bits.0, 0, bits.0, s, b, 1)

Function addvbr6(b:bitstream, v:int)bitstream addvbr6(bits.0, 0, bits.0, [v], b, 1)

Function addvbrsigned6(b:bitstream, val:int)bitstream
if val < 0 then
 if val > -16 then addvbr6(b, 2 * -val + 1)
 else
  let tmp = toint(bits.val ∨ 0xFFFF << 48)
  let first6bits = bits.-tmp << 1 ∧ 0x1F ∨ 0x21
  addvbr6(first6bits, 6, bits.-(val / 16), empty:seq.int, b, 1)
else if val < 16 then addvbr6(b, 2 * val)
else
 let first6bits = bits.val << 1 ∧ 0x1F ∨ 0x20
 addvbr6(first6bits, 6, bits.val >> 4, empty:seq.int, b, 1)

Function align32(a:bitstream)bitstream
let k = length.a mod 32
if k = 0 then a else add(a, bits.0, 32 - k)

Function addblockheader(b:bitstream, currentabbrelength:int, blockid:int, abbrevlength:int)bitstream
addvbr(align32.addvbr(addvbr(addvbr(b, ENTERBLOCK, currentabbrelength), blockid, 8), abbrevlength, 4)
, 0
, 32
)

Function finishblock(current:bitstream, headerplace:int, blockabbrevlength:int)bitstream
if headerplace = 0 then current
else
 let bb = align32.addvbr(current, ENDBLOCK, blockabbrevlength)
 let len = (length.bb - headerplace) / 32
 {assert false report"X"+toword(length.header-32)+toword.len}patch(bb, headerplace - 31, len)

Function addbody(m:bitstream, offset:int, bodytxt:internalbc)bitstream
let header = addblockheader(m, MODABBREVLEN, toint.FUNCTIONBLK, FUNCABBRVLEN)
finishblock(addtobitstream(offset, header, bodytxt), length.header, FUNCABBRVLEN)

Function addbody(m:bitstream, bodytxt:seq.seq.int)bitstream
let header = addblockheader(m, MODABBREVLEN, toint.FUNCTIONBLK, FUNCABBRVLEN)
finishblock(addrecords(header, FUNCABBRVLEN, bodytxt), length.header, FUNCABBRVLEN)

Function addrecords(bits:bitstream, abbrevlength:int, s:seq.seq.int)bitstream
for acc = bits, @e ∈ s do addrecord(acc, abbrevlength, @e)/for(acc)

function addrecord(bits:bitstream, abbrevlength:int, a:seq.int)bitstream
let a1 = addvbr(bits, UNABBREVRECORD, abbrevlength)
let a2 = addvbr6(addvbr6(a1, a_1), length.a - 1)
for acc = a2, @e ∈ subseq(a, 2, length.a)do addvbr6(acc, @e)/for(acc)

function ENDBLOCK int 0

function ENTERBLOCK int 1

function UNABBREVRECORD int 3

function MODABBREVLEN int 3

function TYPEABBREVLEN int 4

function FUNCABBRVLEN int 4

Function llvm(deflist:seq.seq.int, bodytxts:seq.internalbc, trecords:seq.seq.int)seq.bits
let p = llvmpartial(deflist, trecords)
let offset = length.constantrecords
let a7 = for acc = a6.p, @e ∈ bodytxts do addbody(acc, offset, @e)/for(acc)
{sym table}
let symtabheader = addblockheader(a7, MODABBREVLEN, toint.VALUESYMTABLE, TYPEABBREVLEN)
let a8 = finishblock(symentries(symtabheader, constantrecords, 1), length.symtabheader, TYPEABBREVLEN)
{finish module block}bits.finishblock(a8, length.h.p, MODABBREVLEN)

Function llvm(trecords:seq.seq.int, bodies:seq.seq.seq.int)seq.bits
let p = llvmpartial(empty:seq.seq.int, trecords)
let offset = length.constantrecords
let a7 = for acc = a6.p, @e ∈ bodies do addbody(acc, @e)/for(acc)
{sym table}
let symtabheader = addblockheader(a7, MODABBREVLEN, toint.VALUESYMTABLE, TYPEABBREVLEN)
let a8 = finishblock(symentries(symtabheader, constantrecords, 1), length.symtabheader, TYPEABBREVLEN)
{finish module block}bits.finishblock(a8, length.h.p, MODABBREVLEN)

type llvmpartial is a6:bitstream, h:bitstream

function llvmpartial(deflist:seq.seq.int, trecords:seq.seq.int)llvmpartial
let offset = length.constantrecords
let h = 
 addblockheader(add(add(add(add(empty:bitstream, bits.66, 8), bits.67, 8), bits.192, 8), bits.222, 8)
 , 2
 , toint.MODULE
 , MODABBREVLEN
 )
let info = getmachineinfo
let a = 
 addrecords(h
 , MODABBREVLEN
 , [[1, 1]
 , [toint.TRIPLE]
 + for acc = empty:seq.int, @e ∈ triple.info do acc + toint.@e /for(acc)
 , [toint.LAYOUT]
 + for acc = empty:seq.int, @e ∈ datalayout.info do acc + toint.@e /for(acc)
 ]
 )
{type block}
let typeheader = addblockheader(a, MODABBREVLEN, toint.TYPES, TYPEABBREVLEN)
let a2 = addrecords(typeheader, TYPEABBREVLEN, [[toint.NumEle, length.trecords]] + trecords)
let a3 = finishblock(a2, length.typeheader, TYPEABBREVLEN)
{PARAGRPBLOCK}
let pgh = addblockheader(a3, MODABBREVLEN, toint.PARAGRP, TYPEABBREVLEN)
let pge = 
 finishblock(addrecords(pgh
 , TYPEABBREVLEN
 , [[3, 0, 2^32 - 1, 0, 14, 0, 26, 0, 18] + [3]
 + tointseq.for acc = empty:seq.char, @e ∈"no-frame-pointer-elim-non-leaf"do acc + decodeword.@e /for(acc)
 + [0]
 ]
 )
 , length.pgh
 , TYPEABBREVLEN
 )
{para block}
let paraheader = addblockheader(pge, MODABBREVLEN, toint.PARA, TYPEABBREVLEN)
let a4 = 
 finishblock(addrecords(paraheader, TYPEABBREVLEN, [[2, 0]]), length.paraheader, TYPEABBREVLEN)
{def list}
let a5 = addrecords(a4, MODABBREVLEN, deflist)
{const block}
let g = 
 for acc = trackconst(a5, -1, 0), @e ∈ subseq(constantrecords, length.deflist + 1, offset)do constrecords(acc, @e)/for(acc)
let a6 = finishblock(bits.g, blockstart.g, TYPEABBREVLEN)
llvmpartial(a6, h)

function constrecords(z:trackconst, l:slotrecord)trackconst
{keep track of type of last const processed and add record when type changes}
if ismoduleblock.l then
 let bits = 
  if not.islastmodule.z then finishblock(bits.z, blockstart.z, TYPEABBREVLEN)else bits.z
 trackconst(addrecord(bits, MODABBREVLEN, record.l), typ.l, 0)
else
 let newblock = islastmodule.z ∧ not.ismoduleblock.l
 let bits = 
  if newblock then addblockheader(bits.z, MODABBREVLEN, toint.CONSTANTS, TYPEABBREVLEN)else bits.z
 let bits2 = 
  if lasttype.z = typ.l then bits else addvbr6(add(bits, bits((1 * 64 + 1) * 16 + 3), 16), typ.l)
 let rec = record.l
 let tp = rec_1
 let bs = 
  if tp = toint.CINTEGER then addvbrsigned6(add(bits2, bits((1 * 64 + toint.CINTEGER) * 16 + 3), 16), rec_2)
  else
   let a1 = 
    if length.rec < 32 then add(bits2, bits(((length.rec - 1) * 64 + tp) * 16 + 3), 16)
    else addvbr6(addvbr6(addvbr(bits2, 3, TYPEABBREVLEN), tp), length.rec - 1)
   addvbr6(a1, subseq(rec, 2, length.rec))
 trackconst(bs, typ.l, if newblock then length.bits else blockstart.z)

Function symentries(bits:bitstream, s:seq.slotrecord, i:int)bitstream
if i > length.s then bits
else
 let l = s_i
 let bs = 
  if ismoduleblock.l then
   let abbrevlength = 4
   let name = tointseq.symtablename.l
   if isempty.name then bits
   else
    let a1 = 
     addvbr6(addvbr6(addvbr6(addvbr(bits, 3, abbrevlength), {rec type entry}1), length.name + 1)
     , i - 1
     )
    addvbr6(a1, name)
  else bits
 symentries(bs, s, i + 1)

type trackconst is bits:bitstream, lasttype:int, blockstart:int

function islastmodule(l:trackconst)boolean lasttype.l < 0

type machineinfo is triple:seq.byte, datalayout:seq.byte

builtin getmachineinfo machineinfo 