Module internalbc

use UTF8

use bits

use seq.bits

use bitstream

use seq.instop

use otherseq.int

use seq.seq.int

use llvm

use seq.slot

use seq.slotrecord

use standard

use seq.templatepart

Export type:internalbc

Export type:templatepart

type templatepart is val:bits

function bits(b:templatepart) bits val.b >> 6

function bitcount(b:templatepart) int toint(val.b ∧ 0x3F)

function templatepart(bits:int, bitcount:int) templatepart
templatepart(tobits.bits << 6 ∨ bits.bitcount)

function templatepart(para:int, slot:int, bitcount:int) templatepart
templatepart(tobits.para << 6 ∨ bits.bitcount ∨ bits.slot << 10)

function signedvalue(valx:templatepart) int
toint.if toint.val.valx < 0 then bits.valx ∨ 0xFC00000000000000 else bits.valx

function ibcsubpara(a:templatepart) int toint(val.a >> 6 ∧ 0xF)

function ibcsubslot(a:templatepart) int toint(val.a >> 10)

function Reloc int 60

function Substitue int 61

function Firstpara int 62

function Relocsigned int 63

Function ibcfirstpara2 int toint(0x1 << 40)

Function ibcsub(i:int) slot slot(ibcfirstpara2 + i)

type internalbc is parts:seq.templatepart

Function %(bc:internalbc) seq.word
for acc = "", e ∈ parts.bc
do
 let nobits = bitcount.e,
  acc
  + "/br"
  + 
   if nobits = Reloc then
   "Reloc^(signedvalue.e)"
   else if nobits = Firstpara then
   "Firstpara^(toint.bits.e)"
   else if nobits = Relocsigned then
   "Relocsigned^(signedvalue.e)"
   else "^(nobits)^(bits.e)",
acc

function +(a:seq.templatepart, b:bitstream) seq.templatepart
assert length.b ≤ 56 report "NOT handled",
a + templatepart(toint.1_bits.b, length.b)

Function %2(bc:internalbc, nopara:int) seq.word
let offset = n.constantrecords
for acc1 = empty:seq.templatepart, valx ∈ parts.bc
do
 let nobits = bitcount.valx,
  if nobits < 58 then
  acc1 + valx
  else if nobits = Reloc then
  acc1 + addvbr6(empty:bitstream, offset - signedvalue.valx)
  else if nobits = Firstpara then
  acc1 + addvbr6(empty:bitstream, toint.bits.valx)
  else if nobits = Relocsigned then
  acc1 + addvbrsigned6(empty:bitstream, offset - signedvalue.valx)
  else acc1
for
 placein = pbc(0, 0x0, 1, parts.{bc} internalbc.acc1, 0x0)
 , resultin = ""
 , slotin = offset + nopara
 , block = 0
while nobits.placein > 0 ∨ idx.placein ≤ n.parts.placein
do
 let start = getbits(placein, 4)
 assert r1.start = 0x3
 report "?? {^(nobits.placein)^(idx.placein)}^(r1.start)^(resultin)^(dumpslots)"
 let op = getvbr6.start
 let args = getvbr6.op
 let inst = instop.toint.r1.op
 let slotinc = if inst ∈ [LOAD, ALLOCA, CALL, GEP, CAST, CMP2, BINOP, PHI] then 1 else 0
 let slot = slotinc + slotin
 let slottxt = if slotinc = 1 then "% /nosp^(slot - offset) =" else ""
 for
  acc = resultin + "/br^(slottxt)^(decode.inst)"
  , place = args
  , i ∈ arithseq(toint.r1.args, 1, 1)
 do
  if nobits.place > 0 ∨ idx.place < n.parts.place ∧ bitcount.(idx.place)_parts.place < 58 then
   let tmp = getvbr6.place
   let argval = toint.r1.tmp
   let more =
    if i = 3 ∧ inst = CAST then
    decode.castop.argval
    else if i = 3 ∧ inst = CMP2 then
    decode.cmp2op.argval
    else if i = 3 ∧ inst = BINOP then
    decode.binaryop.argval
    else if
     {type} i = 1 ∧ inst ∈ [PHI, SWITCH]
     ∨ i = 2 ∧ inst ∈ [LOAD, CAST, GEP]
     ∨ i = 3 ∧ inst = CALL
    then
    %.llvmtype.argval
    else if
     i = 1 ∧ inst ∈ [CAST, CMP2, BINOP, LOAD, STORE, RET]
     ∨ i = 2 ∧ inst ∈ [CMP2, BINOP, STORE, SWITCH]
     ∨ i = 3 ∧ inst ∈ [BR, GEP]
     ∨ i = 4 ∧ inst = GEP
     ∨ i > 3 ∧ inst = CALL
    then
     let a = slotin + 1 - argval,
     if a ≥ offset then "% /nosp^(a - offset)" else "^(slot.a)"
    else if inst = PHI ∧ i mod 2 = 0 then
     let sign = if argval mod 2 = 0 then 1 else -1
     let a = slot - argval / 2 * sign,
     if a ≥ offset then ", % /nosp^(a - offset)" else ",^(slot.a)"
    else if i = 3 ∧ inst = LOAD then
    decode.align.argval
    else %.argval,
   next(acc + more, tmp)
  else
   assert idx.place < n.parts.place report "unexpected end"
   let e = (idx.place)_parts.place
   let nobits = bitcount.e,
   next(
    acc
    + 
     if nobits = Reloc then
     "# /nosp^(slotin + 1 + signedvalue.e))"
     else if nobits = Firstpara then
     "'%^(slotin + 1 - toint.bits.e)"
     else
      assert nobits = Relocsigned report "SDF^(idx.args)^(acc)",
      "## /nosp^({slotin+1-} {offset-} signedvalue.e)"
    , pbc(0, 0x0, idx.place + 1, parts.place, 0x0)
   ),
  if inst ∈ [BR, SWITCH] then
  next(place, acc + "/br^(block + 1):", slot, block + 1)
  else next(place, acc, slot, block),
%.offset + %.n.constantrecords + dumpslots + resultin

type pbc is nobits:int, bits:bits, idx:int, parts:seq.templatepart, r1:bits

Function getbits(p:pbc, size:int) pbc
if nobits.p ≥ size then
 let mask = tobits.-1 << size ⊻ tobits.-1,
 pbc(nobits.p - size, bits.p >> size, idx.p, parts.p, bits.p ∧ mask)
else
 let part = (idx.p)_parts.p
 assert bitcount.part < 58
 report "PROBLEM getbits^(bitcount.part)^(idx.p)^(internalbc.parts.p)",
 getbits(
  pbc(nobits.p + bitcount.part, bits.part << nobits.p ∨ bits.part, idx.p + 1, parts.p, 0x0)
  , size
 )

Function getvbr6(p:pbc) pbc
for b = getbits(p, 6), val = 0x0, shift = 0
while (r1.b ∧ 0x20) = 0x20
do next(getbits(b, 6), (r1.b ∧ 0x1F) << shift ∨ val, shift + 5),
if shift = 0 then b else pbc(nobits.b, bits.b, idx.b, parts.b, r1.b << shift ∨ val)

function tail(b:internalbc) seq.templatepart parts.b << 1

function val(b:internalbc) templatepart 1_parts.b

Function emptyinternalbc internalbc internalbc.empty:seq.templatepart

function bits(b:internalbc) bits if isempty.parts.b then 0x0 else bits.val.b

function bitcount(b:internalbc) int if isempty.parts.b then 0 else bitcount.val.b

function internalbc(bits:int, bitcount:int, tail:seq.templatepart) internalbc
internalbc([templatepart(bits, bitcount)] + tail)

function internalbc(bits:bits, bitcount:int, tail:seq.templatepart) internalbc
internalbc([templatepart(toint.bits, bitcount)] + tail)

Function +(a:internalbc, b:internalbc) internalbc
if n.parts.a > 1 ∨ bitcount.a + bitcount.b > 56 then
internalbc(bits.a, bitcount.a, tail.a + parts.b)
else internalbc(bits.b << bitcount.a ∨ bits.a, bitcount.a + bitcount.b, tail.b)

function addplaceholder(t:templatepart, b:internalbc) internalbc
internalbc([t] + parts.b)

function add6bits(val:int, b:internalbc) internalbc
if bitcount.b > 56 - 6 then
internalbc(val, 6, parts.b)
else internalbc(bits.b << 6 ∨ tobits.val, bitcount.b + 6, tail.b)

function add4bits(val:int, b:internalbc) internalbc
if bitcount.b > 56 - 4 then
internalbc(val, 4, parts.b)
else internalbc(bits.b << 4 ∨ tobits.val, bitcount.b + 4, tail.b)

Function addtobitstream(offset:int, bs:bitstream, b:internalbc) bitstream
for result = bs, valx ∈ parts.b
do
 let nobits = bitcount.valx,
  if nobits < 58 then
  add(result, bits.valx, nobits)
  else if nobits = Reloc then
  addvbr6(result, offset - signedvalue.valx)
  else if nobits = Firstpara then
  addvbr6(result, toint.bits.valx)
  else if nobits = Relocsigned then
  addvbrsigned6(result, offset - signedvalue.valx)
  else result,
result

function add(val:int, b:internalbc) internalbc
if val < 32 then
add6bits(val, b)
else add6bits(toint(bits.val ∧ bits.31 ∨ bits.32), add(val / 32, b))

function addstartbits(inst:int, noargs:int, b:internalbc) internalbc
add4bits(3, add(inst, add(noargs, b)))

function processtemplatepart(
 deltaoffset:int
 , args:seq.int
 , t:templatepart
) seq.templatepart
let bits = bitcount.t,
if bits < 58 then
[t]
else if bits = Substitue then
 let arg = (ibcsubpara.t)_args,
  if arg < 0 then
  parts.add(deltaoffset + ibcsubslot.t + arg, emptyinternalbc)
  else [templatepart(arg - ibcsubslot.t - deltaoffset + 1, Reloc)]
else if bits = Reloc then
[templatepart.tobits(toint.val.t - 64 * deltaoffset)]
else
 assert bits = Firstpara report "Problem with code templates",
 [templatepart.tobits(toint.val.t + 64 * deltaoffset)]

Function processtemplate(s:internalbc, deltaoffset:int, args:seq.int) internalbc
internalbc(
 for acc = empty:seq.templatepart, @e ∈ parts.s
 do acc + processtemplatepart(deltaoffset, args, @e),
 acc
)

function addaddress(slot:int, a:int, b:internalbc) internalbc
if a < 0 then
add(slot + a, b)
else
 let d = a - ibcfirstpara2,
  if d < 0 then
  addplaceholder(templatepart(a - slot + 1, Reloc), b)
  else if d = 0 then
  addplaceholder(templatepart(slot - 1, Firstpara), b)
  else addplaceholder(templatepart(d, slot, Substitue), b)

function addsignedaddress(slot:int, a:int, b:internalbc) internalbc
if a ≤ 0 then
let v = slot + a let c = if v ≥ 0 then 2 * v else 2 * -v + 1, add(c, b)
else addplaceholder(templatepart(a - slot + 1, Relocsigned), b)

_____________________________

Function BLOCKCOUNT(slot:int, a1:int) internalbc
addstartbits(1, 1, add(a1, emptyinternalbc))

Function RETURN internalbc addstartbits(toint.RET, 0, emptyinternalbc)

Function RET(slot:slot, a1:slot) internalbc
addstartbits(toint.RET, 1, addaddress(slot, a1, emptyinternalbc))

Function CAST(slot:slot, a1:slot, a2:llvmtype, a3:castop) internalbc
addstartbits(toint.CAST, 3, addaddress(slot, a1, add(typ.a2, add(toint.a3, emptyinternalbc))))

Function BR(slot:slot, a1:int, a2:int, a3:slot) internalbc
addstartbits(toint.BR, 3, add(a1, add(a2, addaddress(slot, a3, emptyinternalbc))))

Function ALLOCA(slot:slot, a1:llvmtype, a2:llvmtype, a3:slot, a4:int) internalbc
addstartbits(toint.ALLOCA, 4, add(typ.a1, add(typ.a2, add(toint.a3, add(a4, emptyinternalbc)))))

Function BR(a1:int) internalbc addstartbits(toint.BR, 1, add(a1, emptyinternalbc))

Function GEP(slot:slot, a2:llvmtype, a3:slot) internalbc
addstartbits(toint.GEP, 3, add(1, add(typ.a2, addaddress(slot, a3, emptyinternalbc))))

Function GEP(slot:slot, a2:llvmtype, a3:slot, a4:slot) internalbc
addstartbits(toint.GEP, 4, add(1, add(typ.a2, addaddress(slot, a3, addaddress(slot, a4, emptyinternalbc)))))

Function STORE(slot:slot, a1:slot, a2:slot) internalbc
addstartbits(
 toint.STORE
 , 4
 , addaddress(slot, a1, addaddress(slot, a2, add(toint.align8, add(0, emptyinternalbc))))
)

Function LOAD(slot:slot, a1:slot, a2:llvmtype) internalbc
addstartbits(toint.LOAD, 3, addaddress(slot, a1, add(typ.a2, add(toint.align8, emptyinternalbc))))

Function CMP2(slot:slot, a1:slot, a2:slot, a3:int) internalbc
addstartbits(toint.CMP2, 3, addaddress(slot, a1, addaddress(slot, a2, add(a3, emptyinternalbc))))

Function BINOP(slot:slot, a1:slot, a2:slot, a3:binaryop) internalbc
addstartbits(toint.BINOP, 3, addaddress(slot, a1, addaddress(slot, a2, add(toint.a3, emptyinternalbc))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot) internalbc
addstartbits(toint.CALL, 4, add(a1, add(a2, add(typ.a3, addaddress(slot, a4, emptyinternalbc)))))

Function CALL(slot:slot, a1:int, a2:int, a3:llvmtype, a4:slot, a5:slot) internalbc
addstartbits(
 toint.CALL
 , 5
 , add(a1, add(a2, add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, emptyinternalbc)))))
)

Function CALL(
 slot:slot
 , a1:int
 , a2:int
 , a3:llvmtype
 , a4:slot
 , a5:slot
 , a6:slot
) internalbc
addstartbits(
 toint.CALL
 , 6
 , add(
  a1
  , add(
   a2
   , add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, emptyinternalbc))))
  )
 )
)

Function CALL(
 slot:slot
 , a1:int
 , a2:int
 , a3:llvmtype
 , a4:slot
 , a5:slot
 , a6:slot
 , a7:slot
) internalbc
addstartbits(
 toint.CALL
 , 7
 , add(
  a1
  , add(
   a2
   , add(
    typ.a3
    , addaddress(slot, a4, addaddress(slot, a5, addaddress(slot, a6, addaddress(slot, a7, emptyinternalbc))))
   )
  )
 )
)

Function CALL(
 slot:slot
 , a1:int
 , a2:int
 , a3:llvmtype
 , a4:slot
 , a5:slot
 , rest:seq.slot
) internalbc
addstartbits(
 toint.CALL
 , 5 + n.rest
 , add(
  a1
  , add(
   a2
   , add(typ.a3, addaddress(slot, a4, addaddress(slot, a5, args(slot, emptyinternalbc, rest, n.rest))))
  )
 )
)

Function CALLSTART(slot:int, a1:int, a2:int, a3:int, a4:int, noargs:int) internalbc
addstartbits(toint.CALL, 4 + noargs, add(a1, add(a2, add(a3, addaddress(slot, a4, emptyinternalbc)))))

Function CALLFINISH(slot:int, rest:seq.int) internalbc
args(slot, emptyinternalbc, rest, n.rest)

function args(slot:int, t:internalbc, rest:seq.int, i:int) internalbc
if i = 0 then t else args(slot, addaddress(slot, i_rest, t), rest, i - 1)

function args(slot:slot, t:internalbc, rest:seq.slot, i:int) internalbc
if i = 0 then t else args(slot, addaddress(slot, i_rest, t), rest, i - 1)

Function PHI(
 slot:slot
 , a1:llvmtype
 , a2:slot
 , a3:int
 , a4:slot
 , a5:int
 , a6:slot
 , a7:int
) internalbc
addstartbits(
 toint.PHI
 , 7
 , add(
  typ.a1
  , addsignedaddress(
   slot
   , a2
   , add(a3, addsignedaddress(slot, a4, add(a5, addsignedaddress(slot, a6, add(a7, emptyinternalbc)))))
  )
 )
)

Function PHI(slot:slot, a1:llvmtype, a2:slot, a3:int, a4:slot, a5:int) internalbc
addstartbits(
 toint.PHI
 , 5
 , add(
  typ.a1
  , addsignedaddress(slot, a2, add(a3, addsignedaddress(slot, a4, add(a5, emptyinternalbc))))
 )
)

Function SWITCH(slot:slot, a1:llvmtype, a2:slot, default:int, s:seq.int) internalbc
for code = emptyinternalbc, i ∈ reverse.s do add(i, code),
addstartbits(toint.SWITCH, n.s + 3, add(typ.a1, addaddress(slot, a2, add(default, code))))

Function PHI(slot:int, a1:int, s:seq.int) internalbc
addstartbits(toint.PHI, n.s + 1, add(a1, subphi(slot, emptyinternalbc, s, n.s)))

function subphi(slot:int, b:internalbc, s:seq.int, i:int) internalbc
if i > 1 then
subphi(slot, addsignedaddress(slot, (i - 1)_s, add(i_s, b)), s, i - 2)
else b

function addpair(a:internalbc, tailphi:seq.int, slot:int, p:int, b:int) internalbc
addsignedaddress(slot, (b + p)_tailphi, add(b_tailphi, a))

Function phiinst(slot:int, typ:seq.int, tailphi:seq.int, nopara:int) internalbc
for acc = emptyinternalbc, @e ∈ arithseq(nopara, 1, 1)
do acc + phiinst(slot, typ, tailphi, nopara, @e),
acc

function phiinst(slot:int, typ:seq.int, tailphi:seq.int, nopara:int, p:int) internalbc
let t =
 for
  acc = emptyinternalbc
  , @e ∈ arithseq(n.tailphi / (nopara + 1),-nopara - 1, n.tailphi - nopara)
 do addpair(acc, tailphi, slot + p, p, @e),
 acc,
addstartbits(toint.PHI, n.tailphi / (nopara + 1) * 2 + 1, add(p_typ, t))

function addsignedaddress(loc:slot, a:slot, bc:internalbc) internalbc
addsignedaddress(-toint.loc, toint.a, bc)

function addaddress(locin:slot, a:slot, bc:internalbc) internalbc
let slot =-toint.locin,
addaddress(slot, toint.a, bc)

Function addvbr(b:bitstream, newbits:int, bitcount:int) bitstream
let limit = toint(bits.1 << (bitcount - 1)),
if newbits < limit then
add(b, bits.newbits, bitcount)
else
 let firstchunk = bits(limit - 1) ∧ bits.newbits ∨ bits.limit
 let secondchunk = bits.newbits >> (bitcount - 1)
 assert toint.secondchunk < limit
 report "vbr encoding for value is not handled" + toword.newbits + toword.limit,
 add(b, secondchunk << bitcount ∨ firstchunk, bitcount * 2)

function addvbr6(
 b:bits
 , bitstoadd:int
 , leftover:bits
 , s:seq.int
 , r:bitstream
 , i:int
) bitstream
if bitstoadd > 58 then
addvbr6(bits.0, 0, leftover, s, add(r, b, bitstoadd), i)
else if toint.leftover > 0 then
 if toint.leftover < 32 then
 addvbr6(b ∨ leftover << bitstoadd, bitstoadd + 6, bits.0, s, r, i)
 else addvbr6(b ∨ (leftover ∧ bits.31 ∨ bits.32) << bitstoadd, bitstoadd + 6, leftover >> 5, s, r, i)
else if i > n.s then
if bitstoadd = 0 then r else add(r, b, bitstoadd)
else
 let v = i_s,
  if v < 32 then
  addvbr6(b ∨ bits.v << bitstoadd, bitstoadd + 6, bits.0, s, r, i + 1)
  else addvbr6(
   b ∨ (bits.v ∧ bits.31 ∨ bits.32) << bitstoadd
   , bitstoadd + 6
   , bits.v >> 5
   , s
   , r
   , i + 1
  )

function addvbr6(b:bitstream, s:seq.int) bitstream addvbr6(bits.0, 0, bits.0, s, b, 1)

Function addvbr6(b:bitstream, v:int) bitstream addvbr6(bits.0, 0, bits.0, [v], b, 1)

Function addvbrsigned6(b:bitstream, val:int) bitstream
if val < 0 then
 if val > -16 then
 addvbr6(b, 2 * -val + 1)
 else
  let tmp = toint(bits.val ∨ 0xFFFF << 48)
  let first6bits = bits.-tmp << 1 ∧ 0x1F ∨ 0x21,
  addvbr6(first6bits, 6, bits.-(val / 16), empty:seq.int, b, 1)
else if val < 16 then
addvbr6(b, 2 * val)
else
 let first6bits = bits.val << 1 ∧ 0x1F ∨ 0x20,
 addvbr6(first6bits, 6, bits.val >> 4, empty:seq.int, b, 1)

Function align32(a:bitstream) bitstream
let k = length.a mod 32,
if k = 0 then a else add(a, bits.0, 32 - k)

Function addblockheader(
 b:bitstream
 , currentabbrelength:int
 , blockid:int
 , abbrevlength:int
) bitstream
addvbr(
 align32.addvbr(addvbr(addvbr(b, ENTERBLOCK, currentabbrelength), blockid, 8), abbrevlength, 4)
 , 0
 , 32
)

Function finishblock(current:bitstream, headerplace:int, blockabbrevlength:int) bitstream
if headerplace = 0 then
current
else
 let bb = align32.addvbr(current, ENDBLOCK, blockabbrevlength)
 let len = (length.bb - headerplace) / 32,
 patch(bb, headerplace - 31, len)

function addrecords(bits:bitstream, abbrevlength:int, s:seq.seq.int) bitstream
for acc = bits, @e ∈ s do addrecord(acc, abbrevlength, @e),
acc

function addrecord(bits:bitstream, abbrevlength:int, a:seq.int) bitstream
let a1 = addvbr(bits, UNABBREVRECORD, abbrevlength)
let a2 = addvbr6(addvbr6(a1, 1_a), n.a - 1)
for acc = a2, @e ∈ subseq(a, 2, n.a) do addvbr6(acc, @e),
acc

function ENDBLOCK int 0

function ENTERBLOCK int 1

function UNABBREVRECORD int 3

function MODABBREVLEN int 3

function TYPEABBREVLEN int 4

function FUNCABBRVLEN int 4

Function llvm(
 deflist:seq.seq.int
 , bodytxts:seq.internalbc
 , trecords:seq.seq.int
) seq.seq.byte
let header = llvmheader
let a6 = llvmpartial(deflist, trecords, header)
let offset = n.constantrecords
let a7 =
 for acc = a6, bodytxt ∈ bodytxts
 do
  let fheader = addblockheader(acc, MODABBREVLEN, toint.FUNCTIONBLK, FUNCABBRVLEN),
  finishblock(addtobitstream(offset, fheader, bodytxt), length.fheader, FUNCABBRVLEN),
 acc
{sym table}
let symtabheader = addblockheader(a7, MODABBREVLEN, toint.VALUESYMTABLE, TYPEABBREVLEN)
let a8 = finishblock(symentries(symtabheader, constantrecords, 1), length.symtabheader, TYPEABBREVLEN)
{finish module block}
toseqseqbyte.finishblock(a8, length.header, MODABBREVLEN)

Function llvm(trecords:seq.seq.int, bodies:seq.seq.seq.int) seq.seq.byte
let header = llvmheader
let a6 = llvmpartial(empty:seq.seq.int, trecords, header)
let a7 =
 for acc = a6, bodytxt ∈ bodies
 do
  let fheader = addblockheader(acc, MODABBREVLEN, toint.FUNCTIONBLK, FUNCABBRVLEN),
  finishblock(addrecords(fheader, FUNCABBRVLEN, bodytxt), length.fheader, FUNCABBRVLEN),
 acc
{sym table}
let symtabheader = addblockheader(a7, MODABBREVLEN, toint.VALUESYMTABLE, TYPEABBREVLEN)
let a8 = finishblock(symentries(symtabheader, constantrecords, 1), length.symtabheader, TYPEABBREVLEN)
{finish module block}
toseqseqbyte.finishblock(a8, length.header, MODABBREVLEN)

function llvmheader bitstream
addblockheader(
 add(add(add(add(empty:bitstream, bits.66, 8), bits.67, 8), bits.192, 8), bits.222, 8)
 , 2
 , toint.MODULE
 , MODABBREVLEN
)

function llvmpartial(deflist:seq.seq.int, trecords:seq.seq.int, h:bitstream) bitstream
let info = getmachineinfo
let a = addrecords(
 h
 , MODABBREVLEN
 , [
  [1, 1]
  , (for acc = [toint.TRIPLE], @e ∈ triple.info do acc + toint.@e, acc)
  , (for acc = [toint.LAYOUT], @e ∈ datalayout.info do acc + toint.@e, acc)
 ]
)
{type block}
let typeheader = addblockheader(a, MODABBREVLEN, toint.TYPES, TYPEABBREVLEN)
let a2 = addrecords(typeheader, TYPEABBREVLEN, [[toint.NumEle, n.trecords]] + trecords)
let a3 = finishblock(a2, length.typeheader, TYPEABBREVLEN)
{PARAGRPBLOCK}
let pgh = addblockheader(a3, MODABBREVLEN, toint.PARAGRP, TYPEABBREVLEN)
let pge = finishblock(
 addrecords(
  pgh
  , TYPEABBREVLEN
  , [
   [3, 0, 2^32 - 1, 0, 14, 0, 26, 0, 18]
   + [3]
   + 
    for acc = empty:seq.char, @e ∈ "no-frame-pointer-elim-non-leaf"
    do acc + decodeword.@e,
    tointseq.acc + [0]
  ]
 )
 , length.pgh
 , TYPEABBREVLEN
)
{para block}
let paraheader = addblockheader(pge, MODABBREVLEN, toint.PARA, TYPEABBREVLEN)
let a4 = finishblock(addrecords(paraheader, TYPEABBREVLEN, [[2, 0]]), length.paraheader, TYPEABBREVLEN)
{def list}
let a5 = addrecords(a4, MODABBREVLEN, deflist)
{const block}
let g =
 for acc = trackconst(a5,-1, 0), @e ∈ constantrecords << n.deflist do constrecords(acc, @e),
 acc,
finishblock(bits.g, blockstart.g, TYPEABBREVLEN)

function constrecords(z:trackconst, l:slotrecord) trackconst
{keep track of type of last const processed and add record when type changes}
if ismoduleblock.l then
 let bits = if not.islastmodule.z then finishblock(bits.z, blockstart.z, TYPEABBREVLEN) else bits.z,
 trackconst(addrecord(bits, MODABBREVLEN, record.l), typ.l, 0)
else
 let newblock = islastmodule.z ∧ not.ismoduleblock.l
 let bits =
  if newblock then
  addblockheader(bits.z, MODABBREVLEN, toint.CONSTANTS, TYPEABBREVLEN)
  else bits.z
 let bits2 =
  if lasttype.z = typ.l then
  bits
  else addvbr6(add(bits, bits((1 * 64 + 1) * 16 + 3), 16), typ.l)
 let rec = record.l
 let tp = 1_rec
 let bs =
  if tp = toint.CINTEGER then
  addvbrsigned6(add(bits2, bits((1 * 64 + toint.CINTEGER) * 16 + 3), 16), 2_rec)
  else
   let a1 =
    if n.rec < 32 then
    add(bits2, bits(((n.rec - 1) * 64 + tp) * 16 + 3), 16)
    else addvbr6(addvbr6(addvbr(bits2, 3, TYPEABBREVLEN), tp), n.rec - 1),
   addvbr6(a1, subseq(rec, 2, n.rec)),
 trackconst(bs, typ.l, if newblock then length.bits else blockstart.z)

Function symentries(bits:bitstream, s:seq.slotrecord, i:int) bitstream
if i > n.s then
bits
else
 let l = i_s
 let bs =
  if ismoduleblock.l then
   let abbrevlength = 4
   let name = tointseq.symtablename.l,
    if isempty.name then
    bits
    else
     let a1 = addvbr6(addvbr6(addvbr6(addvbr(bits, 3, abbrevlength), {rec type entry} 1), n.name + 1), i - 1),
     addvbr6(a1, name)
  else bits,
 symentries(bs, s, i + 1)

type trackconst is bits:bitstream, lasttype:int, blockstart:int

function islastmodule(l:trackconst) boolean lasttype.l < 0

type machineinfo is triple:seq.byte, datalayout:seq.byte

builtin getmachineinfo machineinfo 