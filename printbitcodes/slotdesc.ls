Module slotdesc

/use sparseseq.codefreq

use UTF8

use bitcodesupport

use bits

use encoding.seq.char

use seq.encodingpair.seq.char

use seq.constop

use otherseq.int

use set.int

use llvm

use otherseq.objectfldslots

use seq.slotdesc

use standard

use otherseq.word

use process.word

use seq.word

use sparseseq.seq.word

use set.word

use sparseseq.word

use words

type slotdesc is typ:int, rec:seq.int

Export type:slotdesc

Export typ(slotdesc) int

Export rec(slotdesc) seq.int

Export slotdesc(int, seq.int) slotdesc

Function check(slots:seq.slotdesc, types:seq.seq.word) seq.seq.word
for result = empty:seq.seq.word, k ∈ slots
do
 if typ.k < 0 then
 result + printrecord(MODULE, rec.k)
 else
  let rec = rec.k
  let z = printrecord(CONSTANTS, rec.k),
   if 1_rec = toint.CAGGREGATE then
    let eletypes = for acc = empty:set.int, @e ∈ subseq(rec.k, 2, n.rec.k) do acc + findtype(slots, @e), acc,
     if n.eletypes > 1 then
     result + "^(z) ERROR: multiple types" + %.toseq.eletypes
     else result + z
   else if 1_rec = toint.CGEP ∧ n.rec = 8 then
    let a = (typ.k + 1)_types
    let b0 = (3_rec + 1)_types
    let b = if b0 = "ptr.conststype" then "ptr.i64)" else b0
    let c = a << 2 + ")"
    let d = b << (n.b - n.c),
     if
      findtype(slots, 6_rec) = 5_rec
      ∧ findtype(slots, 8_rec) = 7_rec
      ∧ 1_a ∈ "ptr"
      ∧ 1_b ∈ "ptr"
      ∧ c = d
     then
     result + z
     else
      result
      + "^(z) ERROR: ^(findtype(slots, 6_rec)) =^(5_rec)^(findtype(slots, 8_rec))"
      + "=^(7_rec)"
   else if 1_rec = toint.CCAST then
    if
     (2_rec = 9 ∧ typ.k = 0 ∨ 2_rec = 11 ∧ (typ.k + 1)_types = "double")
     ∧ findtype(slots, 4_rec) ∈ [3_rec,-1]
    then
    result + z
    else
     result
     + "^(z) ERROR^((typ.k + 1)_types + %.findtype(slots, 4_rec) + %.3_rec)"
   else if 1_rec.k = toint.CINTEGER then
    if (typ.k + 1)_types ∈ ["i64", "i32"] then
    result + z
    else result + "^(z) ERROR^((typ.k + 1)_types)"
   else result + z,
result

function findtype(slots:seq.slotdesc, i:int) int
assert between(i, 0, n.slots - 1) report "PRo",
typ.(i + 1)_slots

Function lookupconst(consts:seq.seq.word, i:int) seq.word
let t = (i + 1)_consts,
if 1_t = 1_"modulerecord" then
 let a = findindex(t, 1_",")
 let b = subseq(t, 3, a - 1),
 if b = dq + dq then t else "slot.^(b)"
else t

Function descslot(
 check:boolean
 , objects:boolean
 , s:seq.slotdesc
 , names:seq.word
 , types:seq.seq.word
) seq.seq.word
for result = empty:seq.seq.word, sd ∈ s
do
 let a = rec.sd,
  if typ.sd = -1 then
   let typ = (2_a + 1)_types
   let name1 = (n.result + 1)_names
   let name = if name1 = 1_"undefinedname" then "" else [name1]
   let kk = n.result
   let new =
    if 1_a = toint.GLOBALVAR then
     assert n.a > 5 report "Bad format"
     let init =
      if 4_a = 0 then
      "0,"
      else if 4_a - 1 > n.result then
      "toint.slot (" + toword(4_a - 1) + ")+1,"
      else "toint.^((4_a)_result)+1,",
      "modulerecord (^(dq)^(name)^(dq + ", [toint.GLOBALVAR, typ.")^(typ),"
      + toword.3_a
      + ","
      + init
      + %(",", subseq(a, 5, n.a)) >> 1
      + "]"
    else "modulerecord (^(dq)^(name)^(dq + ", [toint.FUNCTIONDEC, typ.")^(typ),
     ^(%(",", subseq(a, 3, n.a)) >> 1)]",
   result + if check then new + "," + printrecord(MODULE, a) + ")" else new + ")"
  else
   let currenttype = (typ.sd + 1)_types
   let b =
    if 1_a = toint.CINTEGER then
     if currenttype = "i64" then
     "C64." + toword.2_a
     else if currenttype = "i32" then
     "C32." + toword.2_a
     else currenttype + [toword.2_a]
    else
     {if a_1 = AGGREGATE then let eletype = subseq (currenttype, 4, n.currenttype-1)" ["+@
      (seperator.",", lookupconst.result,"", subseq (a, 2, n.a))+"]" else}
     (
      if 1_a = toint.CCAST ∧ castop.2_a = ptrtoint then
       let objno = checkobjref(s, types, sd),
        if objno ≥ 0 ∧ objects then
        "obj.^(objno)"
        else
         assert currenttype = "i64"
         report "not expecting type in prttoint^(currenttype)^((3_a + 1)_types)",
         "ptrtoint (^(lookupconst(result, 4_a)),^((3_a + 1)_types)
          ^(if check then ",^(printrecord(CONSTANTS, a)))" else ")")"
      else if 1_a = toint.CGEP ∧ n.a = 8 ∧ check then
      "CGEP (^(if 2_a = 1 then "conststype" else (3_a + 1)_types),
       ^(
        lookupconst(result, 4_a)
        + ","
        + lookupconst(result, 6_a)
        + ","
        + lookupconst(result, 8_a)
        + ","
        + printrecord(CONSTANTS, a)
        + ")")"
      else if 1_a = toint.CGEP ∧ n.a = 8 then
       let a8 = lookupconst(result, 8_a)
       let a6 = lookupconst(result, 6_a),
        (if currenttype = "ptr.i8" then "CGEPi8 (" else "CGEP (")
        + lookupconst(result, 4_a)
        + ","
        + (if a6 = "C32.0" ∧ subseq(a8, 1, 2) = "C64." then [3_a8] else a6 + "," + a8)
        + if check then ",^(printrecord(CONSTANTS, a)))" else ")"
      else
       assert constop.1_a ∈ [CAGGREGATE, CNULL, CDATA, CCAST]
       report "KL^(decode.constop.1_a)" + toword.1_a,
       "C (^(currenttype),^(printrecord(CONSTANTS, a)))"
     ),
   result + b,
result

function checkobjref(slots:seq.slotdesc, types:seq.seq.word, slot:slotdesc) int
{if object then return objno else returns-1}
let a = rec.slot,
if 1_a = toint.CCAST ∧ castop.2_a = ptrtoint then
 let gep = rec.(4_a + 1)_slots,
  if
   1_gep = toint.CGEP
   ∧ n.gep = 8
   ∧ {assume list is first slot} 4_gep = 0
   ∧ (5_gep + 1)_types = "i32"
   ∧ (7_gep + 1)_types = "i64"
   ∧ rec.(6_gep + 1)_slots = [toint.CINTEGER, 0]
   ∧ 1_rec.(8_gep + 1)_slots = toint.CINTEGER
  then
  2_rec.(8_gep + 1)_slots
  else -1
else -1

Function obj2txt(objects:seq.objectfldslots, slots:seq.seq.word) seq.word
for acc = "", e ∈ objects
do
 for acc2 = acc + %.objno.e + ":", fld ∈ slots.e
 do
  let a = (fld + 1)_slots
  let b = if subseq(a, 1, 2) = "C64." then a << 2 else a,
  acc2 + b + ",",
 acc2 >> 1 + "/br",
acc

type objectfldslots is objno:int, slots:seq.int

function %(a:objectfldslots) seq.word %.objno.a + %.slots.a

Function objectfldslots(slots:seq.slotdesc, types:seq.seq.word) seq.objectfldslots
let listinit = 4_rec.1_slots
let objarray = rec.listinit_slots
for acc = empty:seq.objectfldslots, lastt = 0, e ∈ slots
do
 let gep = rec.e,
  if
   1_gep = toint.CGEP
   ∧ n.gep = 8
   ∧ {assume list is first slot} 4_gep = 0
   ∧ (5_gep + 1)_types = "i32"
   ∧ (7_gep + 1)_types = "i64"
   ∧ rec.(6_gep + 1)_slots = [toint.CINTEGER, 0]
   ∧ 1_rec.(8_gep + 1)_slots = toint.CINTEGER
  then
   let t = 2_rec.(8_gep + 1)_slots,
   next(acc + objectfldslots(lastt, subseq(objarray, lastt + 2, t + 2 - 1)), t)
  else next(acc, lastt),
acc << 1 + objectfldslots(lastt, subseq(objarray, lastt + 2, n.objarray)) 