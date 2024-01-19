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
  if 1#rec = toint.CAGGREGATE then
   let eletypes =
    for acc = empty:set.int, @e ∈ subseq(rec.k, 2, n.rec.k)
    do acc + findtype(slots, @e),
    acc,
   if n.eletypes > 1 then result + (z + "ERROR: multiple types") + %.toseq.eletypes
   else result + z
  else if 1#rec = toint.CGEP ∧ n.rec = 8 then
   let a = (typ.k + 1)#types
   let b0 = (3#rec + 1)#types
   let b = if b0 = "ptr.conststype" then "ptr.i64)" else b0
   let c = a << 2 + ")",
   let d = b << (n.b - n.c),
   if findtype(slots, 6#rec) = 5#rec
   ∧ findtype(slots, 8#rec) = 7#rec
   ∧ 1#a ∈ "ptr"
   ∧ 1#b ∈ "ptr"
   ∧ c = d then result + z
   else
    result
     + (z
     + "ERROR: "
     + %.findtype(slots, 6#rec)
     + "="
     + %.5#rec
     + %.findtype(slots, 8#rec))
     + "=^(7#rec)"
  else if 1#rec = toint.CCAST then
   if (2#rec = 9 ∧ typ.k = 0 ∨ 2#rec = 11 ∧ (typ.k + 1)#types = "double")
   ∧ findtype(slots, 4#rec) ∈ [3#rec,-1] then result + z
   else result + (z + "ERROR" + ((typ.k + 1)#types + %.findtype(slots, 4#rec) + %.3#rec))
  else if 1#rec.k = toint.CINTEGER then
   if (typ.k + 1)#types ∈ ["i64", "i32"] then result + z
   else result + (z + "ERROR" + (typ.k + 1)#types)
  else result + z,
result

function findtype(slots:seq.slotdesc, i:int) int
assert between(i, 0, n.slots - 1) report "PRo",
typ.(i + 1)#slots

Function lookupconst(consts:seq.seq.word, i:int) seq.word
let t = (i + 1)#consts,
if 1#t = 1#"modulerecord" then
 let a = findindex(t, 1#",")
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
 if typ.sd =-1 then
  let typ = (2#a + 1)#types
  let name1 = (n.result + 1)#names
  let name = if name1 = 1#"undefinedname" then "" else [name1]
  let kk = n.result,
  let new =
   if 1#a = toint.GLOBALVAR then
    assert n.a > 5 report "Bad format"
    let init =
     if 4#a = 0 then "0,"
     else if 4#a - 1 > n.result then "toint.slot (" + toword(4#a - 1) + ")+1,"
     else "toint.^((4#a)#result)+1,",
    "modulerecord (^(dq)^(name)^(dq + ", [toint.GLOBALVAR, typ.")^(typ),"
     + toword.3#a
     + ","
     + init
     + %(",", subseq(a, 5, n.a)) >> 1
     + "]"
   else "modulerecord (^(dq)^(name)^(dq + ", [toint.FUNCTIONDEC, typ.")^(typ),^(%(",", subseq(a, 3, n.a)) >> 1)]",
  result
   + (if check then new + "," + printrecord(MODULE, a) + ")" else new + ")")
 else
  let currenttype = (typ.sd + 1)#types
  let b =
   if 1#a = toint.CINTEGER then
    if currenttype = "i64" then "C64." + toword.2#a
    else if currenttype = "i32" then "C32." + toword.2#a
    else currenttype + [toword.2#a]
   else
    {if a#1 = AGGREGATE then let eletype = subseq (currenttype, 4, n.currenttype-1)" ["+@ (seperator.",", lookupconst.result,"", subseq (a, 2, n.a))+"]" else}
    if 1#a = toint.CCAST ∧ castop.2#a = ptrtoint then
     let objno = checkobjref(s, types, sd),
     if objno ≥ 0 ∧ objects then "obj.^(objno)"
     else
      assert currenttype = "i64" report "not expecting type in prttoint^(currenttype)^((3#a + 1)#types)",
      "ptrtoint (^(lookupconst(result, 4#a)),^((3#a + 1)#types)^(if check then ",^(printrecord(CONSTANTS, a)))" else ")")"
    else if 1#a = toint.CGEP ∧ n.a = 8 ∧ check then
     "CGEP (^(if 2#a = 1 then "conststype" else (3#a + 1)#types),^(lookupconst(result, 4#a)
      + ","
      + lookupconst(result, 6#a)
      + ","
      + lookupconst(result, 8#a)
      + ","
      + printrecord(CONSTANTS, a)
      + ")")"
    else if 1#a = toint.CGEP ∧ n.a = 8 then
     let a8 = lookupconst(result, 8#a)
     let a6 = lookupconst(result, 6#a),
     (if currenttype = "ptr.i8" then "CGEPi8 (" else "CGEP (")
      + lookupconst(result, 4#a)
      + ","
      + (if a6 = "C32.0" ∧ subseq(a8, 1, 2) = "C64." then [3#a8] else a6 + "," + a8)
      + (if check then ",^(printrecord(CONSTANTS, a)))" else ")")
    else
     assert constop.1#a ∈ [CAGGREGATE, CNULL, CDATA, CCAST] report "KL^(decode.constop.1#a)" + toword.1#a,
     "C (^(currenttype),^(printrecord(CONSTANTS, a)))",
  result + b,
result

function checkobjref(slots:seq.slotdesc, types:seq.seq.word, slot:slotdesc) int
{if object then return objno else returns-1}
let a = rec.slot,
if 1#a = toint.CCAST ∧ castop.2#a = ptrtoint then
 let gep = rec.(4#a + 1)#slots,
 if 1#gep = toint.CGEP
 ∧ n.gep = 8
 ∧ {assume list is first slot} 4#gep = 0
 ∧ (5#gep + 1)#types = "i32"
 ∧ (7#gep + 1)#types = "i64"
 ∧ rec.(6#gep + 1)#slots = [toint.CINTEGER, 0]
 ∧ 1#rec.(8#gep + 1)#slots = toint.CINTEGER then 2#rec.(8#gep + 1)#slots
 else-1
else-1

Function obj2txt(objects:seq.objectfldslots, slots:seq.seq.word) seq.word
for acc = "", e ∈ objects
do
 for acc2 = acc + %.objno.e + ":", fld ∈ slots.e
 do
  let a = (fld + 1)#slots
  let b = if subseq(a, 1, 2) = "C64." then a << 2 else a,
  acc2 + b + ",",
 acc2 >> 1 + "/br",
acc

type objectfldslots is objno:int, slots:seq.int

function %(a:objectfldslots) seq.word %.objno.a + %.slots.a

Function objectfldslots(slots:seq.slotdesc, types:seq.seq.word) seq.objectfldslots
let listinit = 4#rec.1#slots
let objarray = rec.listinit#slots
for acc = empty:seq.objectfldslots, lastt = 0, e ∈ slots
do
 let gep = rec.e,
 if 1#gep = toint.CGEP
 ∧ n.gep = 8
 ∧ {assume list is first slot} 4#gep = 0
 ∧ (5#gep + 1)#types = "i32"
 ∧ (7#gep + 1)#types = "i64"
 ∧ rec.(6#gep + 1)#slots = [toint.CINTEGER, 0]
 ∧ 1#rec.(8#gep + 1)#slots = toint.CINTEGER then
  let t = 2#rec.(8#gep + 1)#slots,
  next(acc + objectfldslots(lastt, subseq(objarray, lastt + 2, t + 2 - 1)), t)
 else next(acc, lastt),
acc << 1 + objectfldslots(lastt, subseq(objarray, lastt + 2, n.objarray)) 