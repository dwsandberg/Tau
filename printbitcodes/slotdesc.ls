module slotdesc

use UTF8

use bitcodesupport

use bits

use llvmconstants

use standard

use words

use seq.constop

use set.int

use seq.slotdesc

use otherseq.word

use process.word

use seq.word

use set.word

use sparseseq.word

use encoding.seq.char

use sparseseq.seq.word

use seq.encodingpair.seq.char

/use sparseseq.codefreq

type slotdesc is typ:int, rec:seq.int

Export type:slotdesc

Export typ(slotdesc) int

Export rec(slotdesc) seq.int

Export slotdesc(int, seq.int) slotdesc

Function check(slots:seq.slotdesc, types:seq.seq.word) seq.seq.word
for result = empty:seq.seq.word, k ∈ slots do
 if typ.k < 0 then
  result + printrecord(MODULE, rec.k)
 else
  let rec = rec.k
  let z = printrecord(CONSTANTS, rec.k),
  if rec_1 = toint.CAGGREGATE then
   let eletypes = 
    for acc = empty:set.int, @e ∈ subseq(rec.k, 2, length.rec.k) do
     acc + findtype(slots, @e)
    /do acc
   ,
   if cardinality.eletypes > 1 then
    result + "$(z) ERROR: multiple types" + %.toseq.eletypes
   else
    result + z
  else if rec_1 = toint.CGEP ∧ length.rec = 8 then
   let a = types_(typ.k + 1)
   let b0 = types_(rec_3 + 1)
   let b = if b0 = "ptr.conststype" then "ptr.i64)" else b0
   let c = a << 2 + ")"
   let d = b << (length.b - length.c),
   if findtype(slots, rec_6) = rec_5 ∧ findtype(slots, rec_8) = rec_7
   ∧ first.a ∈ "ptr"
   ∧ first.b ∈ "ptr"
   ∧ c = d then
    result + z
   else
    result
    + "$(z) ERROR: $(findtype(slots, rec_6)) = $(rec_5) $(findtype(slots, rec_8)) =
     $(rec_7)"
  else if rec_1 = toint.CCAST then
   if (rec_2 = 9 ∧ typ.k = 0 ∨ rec_2 = 11 ∧ types_(typ.k + 1) = "double")
   ∧ findtype(slots, rec_4) ∈ [rec_3,-1] then
    result + z
   else
    result + "$(z) ERROR $(types_(typ.k + 1) + %.findtype(slots, rec_4) + %.rec_3)"
  else if (rec.k)_1 = toint.CINTEGER then
   if types_(typ.k + 1) ∈ ["i64", "i32"] then
    result + z
   else
    result + "$(z) ERROR $(types_(typ.k + 1))"
  else
   result + z
/do result

function findtype(slots:seq.slotdesc, i:int) int
assert between(i, 0, length.slots - 1) report "PRo",
typ.slots_(i + 1)

Function lookupconst(consts:seq.seq.word, i:int) seq.word
let t = consts_(i + 1),
if t_1 = "modulerecord"_1 then
 let a = findindex(t, ","_1)
 let b = subseq(t, 3, a - 1),
 if b = dq + dq then t else "slot.$(b)"
else
 t

Function descslot(check:boolean, objects:boolean, s:seq.slotdesc, names:seq.word, types:seq.seq.word) seq.seq.word
for result = empty:seq.seq.word, sd ∈ s do
 let a = rec.sd,
 if typ.sd = -1 then
  let typ = types_(a_2 + 1)
  let name1 = names_(length.result + 1)
  let name = if name1 = "undefinedname"_1 then "" else [name1]
  let kk = length.result
  let new = 
   if a_1 = toint.GLOBALVAR then
    assert length.a > 5 report "Bad format"
    let init = 
     if a_4 = 0 then
      "0,"
     else if a_4 - 1 > length.result then
      "toint.slot (" + toword(a_4 - 1) + ")+1,"
     else
      "toint.$(result_(a_4))+1,"
    ,
    "modulerecord ($(dq) $(name) $(dq + ", [toint.GLOBALVAR, typ.") $(typ)," + toword.a_3
    + ","
    + init
    + %(",", subseq(a, 5, length.a)) >> 1
    + "]"
   else
    "modulerecord ($(dq) $(name) $(dq + ", [toint.FUNCTIONDEC, typ.") $(typ),
     $(%(",", subseq(a, 3, length.a)) >> 1)]"
  ,
  result + if check then new + "," + printrecord(MODULE, a) + ")" else new + ")"
 else
  let currenttype = types_(typ.sd + 1)
  let b = 
   if a_1 = toint.CINTEGER then
    if currenttype = "i64" then
     "C64." + toword.a_2
    else if currenttype = "i32" then "C32." + toword.a_2 else currenttype + [toword.a_2]
   else
    {if a_1 = AGGREGATE then let eletype = subseq (currenttype, 4, length.currenttype-1)" ["+@ (
     seperator.",", lookupconst.result,"", subseq (a, 2, length.a))+"]" else}
    if a_1 = toint.CCAST ∧ castop.a_2 = ptrtoint then
     let objno = checkobjref(s, types, sd),
     if objno ≥ 0 ∧ objects then
      "obj.$(objno)"
     else
      assert currenttype = "i64"
      report "not expecting type in prttoint $(currenttype) $(types_(a_3 + 1))",
      "ptrtoint ($(lookupconst(result, a_4)), $(types_(a_3 + 1))
       $(if check then ", $(printrecord(CONSTANTS, a)))" else ")")"
    else if a_1 = toint.CGEP ∧ length.a = 8 ∧ check then
     "CGEP ($(if a_2 = 1 then "conststype" else types_(a_3 + 1)),
      $(lookupconst(result, a_4) + "," + lookupconst(result, a_6) + ","
     + lookupconst(result, a_8)
     + ","
     + printrecord(CONSTANTS, a)
     + ")")
      "
    else if a_1 = toint.CGEP ∧ length.a = 8 then
     let a8 = lookupconst(result, a_8)
     let a6 = lookupconst(result, a_6),
     if currenttype = "ptr.i8" then "CGEPi8 (" else "CGEP (" /if + lookupconst(result, a_4)
     + ","
     + if a6 = "C32.0" ∧ subseq(a8, 1, 2) = "C64." then
      [a8_3]
     else
      a6 + "," + a8
     /if
     + if check then ", $(printrecord(CONSTANTS, a)))" else ")"
    else
     assert constop.a_1 ∈ [CAGGREGATE, CNULL, CDATA, CCAST]
     report "KL $(decode.constop.a_1)" + toword.a_1,
     "C ($(currenttype), $(printrecord(CONSTANTS, a)))"
  ,
  result + b
/do result

function checkobjref(slots:seq.slotdesc, types:seq.seq.word, slot:slotdesc) int
{if object then return objno else returns-1}
let a = rec.slot,
if a_1 = toint.CCAST ∧ castop.a_2 = ptrtoint then
 let gep = rec.slots_(a_4 + 1),
 if gep_1 = toint.CGEP ∧ length.gep = 8 ∧ {assume list is first slot} gep_4 = 0
 ∧ types_(gep_5 + 1) = "i32"
 ∧ types_(gep_7 + 1) = "i64"
 ∧ rec.slots_(gep_6 + 1) = [toint.CINTEGER, 0]
 ∧ (rec.slots_(gep_8 + 1))_1 = toint.CINTEGER then
  (rec.slots_(gep_8 + 1))_2
 else
  -1
else
 -1

use otherseq.int

Function obj2txt(objects:seq.objectfldslots, slots:seq.seq.word) seq.word
for acc = "", e ∈ objects do
 for acc2 = acc + %.objno.e + ":", fld ∈ slots.e do
  let a = slots_(fld + 1)
  let b = if subseq(a, 1, 2) = "C64." then a << 2 else a,
  acc2 + b + ","
 /do acc2 >> 1 + "/br"
/do acc

type objectfldslots is objno:int, slots:seq.int

use otherseq.objectfldslots

function %(a:objectfldslots) seq.word %.objno.a + %.slots.a

Function objectfldslots(slots:seq.slotdesc, types:seq.seq.word) seq.objectfldslots
let listinit = (rec.slots_1)_4
let objarray = rec.slots_listinit,
for acc = empty:seq.objectfldslots, lastt = 0, e ∈ slots do
 let gep = rec.e,
 if gep_1 = toint.CGEP ∧ length.gep = 8 ∧ {assume list is first slot} gep_4 = 0
 ∧ types_(gep_5 + 1) = "i32"
 ∧ types_(gep_7 + 1) = "i64"
 ∧ rec.slots_(gep_6 + 1) = [toint.CINTEGER, 0]
 ∧ (rec.slots_(gep_8 + 1))_1 = toint.CINTEGER then
  let t = (rec.slots_(gep_8 + 1))_2,
  next(acc + objectfldslots(lastt, subseq(objarray, lastt + 2, t + 2 - 1)), t)
 else
  next(acc, lastt)
/do acc << 1 + objectfldslots(lastt, subseq(objarray, lastt + 2, length.objarray)) 