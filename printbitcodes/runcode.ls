Module runcode

use bitcodesupport

use seq.instop

use seq1.int

use seq.seq.int

use sparseseq.int

use llvm

use seq.llvmtype

use seq.slot

use seq.slotrecord

use standard

use seq.track

use seq1.word

Export type:track

function print(types:seq.seq.int, a:slotrecord) seq.word
if typ.a ≥ 0 then printtype([[0]] + types, typ.a, false) + printrecord(CONSTANTS, record.a)
else [encodeword.symtablename.a] + printrecord(MODULE, record.a)

Function conststype llvmtype array(-2, i64)

Function CGEP(typ:llvmtype, p:slot, a:slot, b:slot, org:seq.int) slot
{need to figure out types}
let t1 = consttype.p
let new = [toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.consttype.a, toint.a, typ.consttype.b, toint.b]
assert new = org report "DIFF:(printrecord(CONSTANTS, org)) /br new:(printrecord(CONSTANTS, new))"
let typa =
 if typ.t1 ∈ [1, 2] then i64
 else llvmtype.typerecords sub (last.typerecords sub (typ.t1 + 1) + 1),
C(ptr.typa, new)

Function modulerecord(name:seq.word, rec:seq.int, org:seq.int) slot
assert rec = org report "DIFF:(printrecord(MODULE, org)) /br new:(printrecord(MODULE, rec))",
modulerecord(name, rec)

Function ptrtoint(i:slot, typ:llvmtype, org:seq.int) slot
let new = [toint.CCAST, 9, typ.typ, toint.i]
assert new = org report "DIFF:(printrecord(CONSTANTS, org)) /br new:(printrecord(CONSTANTS, new))",
C(i64, new)

Function ptrtoint(i:slot, typ:llvmtype) slot
let new = [toint.CCAST, 9, typ.typ, toint.i],
C(i64, new)

Function C(t:llvmtype, r:seq.int) slot constantrecord(t, r)

Function slot(w:seq.word) slot modulerecord(w, [0])

Function getelementptr(reg:slot, t:llvmtype, base:slot) instruction
instruction([toint.GEP, 1, typ.t, toint.base], "L T A", reg)

Function getelementptr(reg:slot, t:llvmtype, base:slot, arg1:slot) instruction
instruction([toint.GEP, 1, typ.t, toint.base, toint.arg1], "L T A A", reg)

Function store(arg1:slot, arg2:slot, align:align) instruction
instruction([toint.STORE, toint.arg1, toint.arg2, toint.align, 0], "A A L L", slot.0)

Function load(reg:slot, arg1:slot, typ:llvmtype, align:align) instruction
instruction([toint.LOAD, toint.arg1, typ.typ, toint.align, 0], "A T L L", reg)

Function call(reg:slot, typ:llvmtype, callee:slot) instruction
instruction([toint.CALL, 0, 32768, typ.typ, toint.callee], "L L T A", reg)

Function call(reg:slot, typ:llvmtype, callee:slot, args:seq.slot) instruction
for acc = [toint.CALL, 0, 32768, typ.typ, toint.callee], @e ∈ args
do acc + toint.@e,
instruction(acc, "L L T A:(constantseq(n.args, "A" sub 1))", reg)

Function binaryop(reg:slot, op:binaryop, a:slot, b:slot) instruction
instruction([toint.BINOP, toint.a, toint.b, toint.op], "A A L", reg)

Function cast(reg:slot, b:castop, c:slot, d:llvmtype) instruction
instruction([toint.CAST, toint.c, typ.d, toint.b], "A T L", reg)

Function getelementptr(reg:slot, a:slot, b:slot) instruction
instruction([toint.GEP, 1, typ.i64, toint.a, toint.b], "L L A A", reg)

Function cmp2(reg:slot, tp:cmp2op, a:slot, b:slot) instruction
instruction([toint.CMP2, toint.a, toint.b, toint.tp], "A A L", reg)

Function ret(i:slot) instruction instruction([toint.RET, toint.i], "A", slot.0)

Function ret instruction instruction([toint.RET], "", slot.0)

Function br(op:slot, t:int, f:int) instruction
instruction([toint.BR, t, f, toint.op], "L L", slot.0)

Function br(a:int) instruction instruction([toint.BR, a], "L", slot.0)

Function /(a:slot, b:int) seq.int [toint.a, b]

Function phi(reg:slot, typ:llvmtype, a:seq.int) instruction
instruction([toint.PHI, typ.typ] + a, repeat(n.a / 2, "T"), reg)

function repeat(i:int, result:seq.word) seq.word
if i = 0 then result else repeat(i - 1, result + "P L")

Function alloca(reg:slot, a1:llvmtype, a2:llvmtype, a3:slot) instruction
instruction([toint.ALLOCA, typ.a1, typ.a2, toint.a3, 0], "T T A L", reg)

Function label(i:int) instruction instruction([-1], "label", slot.i)

Function finish(t:track) seq.seq.int
let offset = offset.t
let labels = labels.t
{fill in block numbers}
let new =
 for new = empty:seq.seq.int, rec ∈ recs.t
 do
  let inst = instop.rec sub 1,
  new
   + if inst = BR then
   if n.rec = 2 then [rec sub 1, getblock(labels, rec sub 2)]
   else [rec sub 1, getblock(labels, rec sub 2), getblock(labels, rec sub 3), 1]
  else if inst = PHI then
   for acc = subseq(rec, 1, 2), isblock = false, e ∈ subseq(rec, 3, n.rec - 1)
   do
    let this =
     if isblock then getblock(labels, e)
     else
      let slot = last.rec
      let t2 = if e > 0 then slot - e - 1 + 1 else slot - (offset + labels sub (-e + 1)) - 1,
      if t2 ≥ 0 then t2 * 2 else-t2 * 2 + 1,
    next(acc + this, not.isblock),
   acc
  else rec,
 new
let chk = check(orgrecs.t, new, 1, "")
assert chk = "" report "ERROR:(chk) labels::(%n.labels.t)",
[[1, blockno.t - 1]] + new

Function check(old:seq.seq.int, new:seq.seq.int, i:int, result:seq.word) seq.word
if i > n.old then result
else if old sub i = new sub i then check(old, new, i + 1, result)
else
 check(
  old
  , new
  , i + 1
  , result
   + "/br old"
   + printrecord(FUNCTIONBLK, old sub i)
   + "/br new"
   + printrecord(FUNCTIONBLK, new sub i)
 )

function getblock(labels:seq.int, i:int) int labels sub (i + 1)

Function functionbody(s:slot, i:int, nopara:int) track
track(
 i
 , i + nopara
 , empty:seq.seq.int
 , empty:seq.seq.int
 , replaceS(addpara(nopara, sparseseq.-10000), nopara + 1, [0])
 , 1
)

function addpara(i:int, result:seq.int) seq.int
if i = 0 then result else addpara(i - 1, replaceS(result, i, [i - 1]))

type track is
offset:int
, slot:int
, recs:seq.seq.int
, orgrecs:seq.seq.int
, labels:seq.int
, blockno:int

type instruction is data:seq.int, argtypes:seq.word, label:slot

Function +(t:track, next:instruction) track
if argtypes.next = "label" then
 let newlabels = replaceS(labels.t, toint.label.next + 1, [blockno.t - 1]),
 track(offset.t, slot.t, recs.t, orgrecs.t, newlabels, blockno.t)
else
 let tp = instop.(data.next) sub 1
 let slotinc = if tp ∈ [LOAD, ALLOCA, CALL, GEP, CAST, CMP2, BINOP, PHI] then 1 else 0
 let blockinc = if tp ∈ [BR, RET] then 1 else 0
 let newlabels =
  if slotinc = 1 ∧ toint.label.next ≠ 0 then replaceS(labels.t,-toint.label.next + 1, [slot.t - offset.t])
  else if blockinc = 1 ∧ toint.label.next ≠ 0 then replaceS(labels.t,-toint.label.next + 1, [blockno.t + 1])
  else if blockinc = 1 then replaceS(labels.t, n.labels.t + 1, [blockno.t])
  else labels.t,
 let newrec =
  if tp = PHI then data.next + (slot.t + 1)
  else doargs(labels.t, offset.t, slot.t + 1, data.next, argtypes.next),
 track(offset.t, slot.t + slotinc, recs.t + newrec, orgrecs.t, newlabels, blockinc + blockno.t)

Function +(t:track, s:seq.int) track
track(offset.t, slot.t, recs.t, orgrecs.t + s, labels.t, blockno.t)

function doargs(
labels:seq.int
, offset:int
, slot:int
, data:seq.int
, argtypes:seq.word
) seq.int
for i = 2, result = [data sub 1], arg ∈ argtypes
while i ≤ n.data
do
 let val =
  if arg ∈ "L T" then data sub i
  else if data sub i > 0 then slot - data sub i - 1 + 1
  else slot - (offset + labels sub (-data sub i + 1)) - 1,
 next(i + 1, result + val),
result 
