Module slotdesc

/use sparseseq.codefreq

use UTF8

use bitcodesupport

use bits

use encoding.seq.char

use seq.encodingpair.seq.char

use seq.constop

use seq1.int

use set.int

use llvm

use seq1.objectfldslots

use seq.slotdesc

use standard

use seq1.word

use process.word

use seq.word

use sparseseq.seq.word

use set.word

use sparseseq.word

type slotdesc is typ:int, rec:seq.int

Export type:slotdesc

Export typ(slotdesc) int

Export rec(slotdesc) seq.int

Export slotdesc(int, seq.int) slotdesc

Function check(slots:seq.slotdesc, types:seq.seq.word) seq.seq.word
for result = empty:seq.seq.word, k ∈ slots
do
 if typ.k < 0 then result + printrecord(MODULE, rec.k)
 else
  let rec = rec.k
  let z = printrecord(CONSTANTS, rec.k),
  if rec sub 1 = toint.CAGGREGATE then
   let eletypes =
    for acc = empty:set.int, @e ∈ subseq(rec.k, 2, n.rec.k)
    do acc + findtype(slots, @e),
    acc,
   if n.eletypes > 1 then result + (z + "ERROR: multiple types") + %.toseq.eletypes
   else result + z
  else if rec sub 1 = toint.CGEP ∧ n.rec = 8 then
   let a = types sub (typ.k + 1)
   let b0 = types sub (rec sub 3 + 1)
   let b = if b0 = "ptr.conststype" then "ptr.i64)" else b0
   let c = a << 2 + ")",
   let d = b << (n.b - n.c),
   if findtype(slots, rec sub 6) = rec sub 5
   ∧ findtype(slots, rec sub 8) = rec sub 7
   ∧ a sub 1 ∈ "ptr"
   ∧ b sub 1 ∈ "ptr"
   ∧ c = d then result + z
   else
    result
     + (z
     + "ERROR: "
     + %.findtype(slots, rec sub 6)
     + "="
     + %.rec sub 5
     + %.findtype(slots, rec sub 8))
     + "=:(rec sub 7)"
  else if rec sub 1 = toint.CCAST then
   if (rec sub 2 = 9 ∧ typ.k = 0 ∨ rec sub 2 = 11 ∧ types sub (typ.k + 1) = "double")
   ∧ findtype(slots, rec sub 4) ∈ [rec sub 3,-1] then result + z
   else
    result
     + (z + "ERROR" + (types sub (typ.k + 1) + %.findtype(slots, rec sub 4) + %.rec sub 3))
  else if (rec.k) sub 1 = toint.CINTEGER then
   if types sub (typ.k + 1) ∈ ["i64", "i32"] then result + z
   else result + (z + "ERROR" + types sub (typ.k + 1))
  else result + z,
result

function findtype(slots:seq.slotdesc, i:int) int
assert between(i, 0, n.slots - 1) report "PRo",
typ.slots sub (i + 1)

Function lookupconst(consts:seq.seq.word, i:int) seq.word
let t = consts sub (i + 1),
if t sub 1 = "modulerecord" sub 1 then
 let a = findindex(t, "," sub 1)
 let b = subseq(t, 3, a - 1),
 if b = dq + dq then t else "slot.:(b)"
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
 if typ.sd =-1 then
  let typ = types sub (a sub 2 + 1)
  let name1 = names sub (n.result + 1)
  let name = if name1 = "undefinedname" sub 1 then "" else [name1]
  let kk = n.result,
  let new =
   if a sub 1 = toint.GLOBALVAR then
    assert n.a > 5 report "Bad format"
    let init =
     if a sub 4 = 0 then "0,"
     else if a sub 4 - 1 > n.result then "toint.slot (" + toword(a sub 4 - 1) + ")+1,"
     else "toint.:(result sub (a sub 4))+1,",
    "modulerecord (:(dq):(name):(dq + ", [toint.GLOBALVAR, typ."):(typ),"
     + toword.a sub 3
     + ","
     + init
     + %(",", subseq(a, 5, n.a)) >> 1
     + "]"
   else "modulerecord (:(dq):(name):(dq + ", [toint.FUNCTIONDEC, typ."):(typ),:(%(",", subseq(a, 3, n.a)) >> 1)]",
  result
   + (if check then new + "," + printrecord(MODULE, a) + ")" else new + ")")
 else
  let currenttype = types sub (typ.sd + 1)
  let b =
   if a sub 1 = toint.CINTEGER then
    if currenttype = "i64" then "C64." + toword.a sub 2
    else if currenttype = "i32" then "C32." + toword.a sub 2
    else currenttype + [toword.a sub 2]
   else
    {if a # 1 = AGGREGATE then let eletype = subseq (currenttype, 4, n.currenttype-1)" ["+@ (seperator.",", lookupconst.result,"", subseq (a, 2, n.a))+"]" else}
    if a sub 1 = toint.CCAST ∧ castop.a sub 2 = ptrtoint then
     let objno = checkobjref(s, types, sd),
     if objno ≥ 0 ∧ objects then "obj.:(objno)"
     else
      assert currenttype = "i64" report "not expecting type in prttoint:(currenttype):(types sub (a sub 3 + 1))",
      "ptrtoint (:(lookupconst(result, a sub 4)),:(types sub (a sub 3 + 1)):(if check then ",:(printrecord(CONSTANTS, a)))" else ")")"
    else if a sub 1 = toint.CGEP ∧ n.a = 8 ∧ check then
     "CGEP (:(if a sub 2 = 1 then "conststype" else types sub (a sub 3 + 1)),:(lookupconst(result, a sub 4)
      + ","
      + lookupconst(result, a sub 6)
      + ","
      + lookupconst(result, a sub 8)
      + ","
      + printrecord(CONSTANTS, a)
      + ")")"
    else if a sub 1 = toint.CGEP ∧ n.a = 8 then
     let a8 = lookupconst(result, a sub 8)
     let a6 = lookupconst(result, a sub 6),
     (if currenttype = "ptr.i8" then "CGEPi8 (" else "CGEP (")
      + lookupconst(result, a sub 4)
      + ","
      + (if a6 = "C32.0" ∧ subseq(a8, 1, 2) = "C64." then [a8 sub 3] else a6 + "," + a8)
      + (if check then ",:(printrecord(CONSTANTS, a)))" else ")")
    else
     assert constop.a sub 1 ∈ [CAGGREGATE, CNULL, CDATA, CCAST] report "KL:(decode.constop.a sub 1)" + toword.a sub 1,
     "C (:(currenttype),:(printrecord(CONSTANTS, a)))",
  result + b,
result

function checkobjref(slots:seq.slotdesc, types:seq.seq.word, slot:slotdesc) int
{if object then return objno else returns-1}
let a = rec.slot,
if a sub 1 = toint.CCAST ∧ castop.a sub 2 = ptrtoint then
 let gep = rec.slots sub (a sub 4 + 1),
 if gep sub 1 = toint.CGEP
 ∧ n.gep = 8
 ∧ {assume list is first slot} gep sub 4 = 0
 ∧ types sub (gep sub 5 + 1) = "i32"
 ∧ types sub (gep sub 7 + 1) = "i64"
 ∧ rec.slots sub (gep sub 6 + 1) = [toint.CINTEGER, 0]
 ∧ (rec.slots sub (gep sub 8 + 1)) sub 1 = toint.CINTEGER then (rec.slots sub (gep sub 8 + 1)) sub 2
 else-1
else-1

Function obj2txt(objects:seq.objectfldslots, slots:seq.seq.word) seq.word
for acc = "", e ∈ objects
do
 for acc2 = acc + %.objno.e + ":", fld ∈ slots.e
 do
  let a = slots sub (fld + 1)
  let b = if subseq(a, 1, 2) = "C64." then a << 2 else a,
  acc2 + b + ",",
 acc2 >> 1 + "/br",
acc

type objectfldslots is objno:int, slots:seq.int

function %(a:objectfldslots) seq.word %.objno.a + %.slots.a

Function objectfldslots(slots:seq.slotdesc, types:seq.seq.word) seq.objectfldslots
let listinit = (rec.slots sub 1) sub 4
let objarray = rec.slots sub listinit
for acc = empty:seq.objectfldslots, lastt = 0, e ∈ slots
do
 let gep = rec.e,
 if gep sub 1 = toint.CGEP
 ∧ n.gep = 8
 ∧ {assume list is first slot} gep sub 4 = 0
 ∧ types sub (gep sub 5 + 1) = "i32"
 ∧ types sub (gep sub 7 + 1) = "i64"
 ∧ rec.slots sub (gep sub 6 + 1) = [toint.CINTEGER, 0]
 ∧ (rec.slots sub (gep sub 8 + 1)) sub 1 = toint.CINTEGER then
  let t = (rec.slots sub (gep sub 8 + 1)) sub 2,
  next(acc + objectfldslots(lastt, subseq(objarray, lastt + 2, t + 2 - 1)), t)
 else next(acc, lastt),
acc << 1 + objectfldslots(lastt, subseq(objarray, lastt + 2, n.objarray)) 
