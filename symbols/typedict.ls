Module typedict

use mytype

use seq.mytype

use seq.seq.mytype

use set.mytype

use standard

use set.symbol

use symbol

use seq.typeentry

use set.typeentry

Export type:typedict

Export type:typeentry

type typeentry is totypeseq:seq.mytype

type typedict is totypedict:set.typeentry

Function typepacked2 mytype typeref."packed2 tausupport *"

Function typepacked3 mytype typeref."packed3 tausupport *"

Function typepacked4 mytype typeref."packed4 tausupport *"

Function typepacked5 mytype typeref."packed5 tausupport *"

Function typepacked6 mytype typeref."packed6 tausupport *"

Function emptytypedict typedict typedict.empty:set.typeentry

function >1(a:typeentry, b:typeentry) ordering
(totypeseq.a) sub 1 >1 (totypeseq.b) sub 1

function type(a:typeentry) mytype (totypeseq.a) sub 1

function flatflds(a:typeentry) seq.mytype totypeseq.a << 1

function typeentry(t:mytype, flat:seq.mytype) typeentry typeentry([t] + flat)

Function addtype(alltypes:typedict, type:mytype) typedict
if iscore4.type ∨ type = typeT then alltypes
else if isseq.type then addtype(alltypes, parameter.type)
else
 let t = lookup(totypedict.alltypes, typeentry(type, empty:seq.mytype)),
 if not.isempty.t then alltypes
 else
  let flatflds = expandflat(type, empty:seq.mytype, totypedict.alltypes)
  let newtr = typeentry(type, flatflds),
  if isflat.newtr then
   {add to typedict and then check to make sure parameters are in typedict}
   for acc = typedict(totypedict.alltypes + newtr), subfld ∈ flatflds
   do if isseq.subfld ∨ isencoding.subfld then addtype(acc, subfld) else acc,
   acc
  else
   {add types not in typedict and try again}
   for acc = alltypes, subfld ∈ flatflds
   do
    if iscore4.subfld ∨ subfld = typeT ∨ isseq.subfld ∨ isencoding.subfld then acc
    else addtype(acc, subfld)
   assert n.totypedict.alltypes < n.totypedict.acc report
    "PROBLEM:(type)flat::(for txt = "", g ∈ flatflds do txt + %.g,
    txt + "/br"):(acc)",
   addtype(acc, type)

Function buildtypedict(syms:set.symbol, types:seq.seq.mytype) typedict
for typesused = empty:seq.mytype, sym ∈ toseq.syms do typesused + typesused.sym
for typesyms = empty:set.typeentry, tp ∈ types do typesyms + typeentry(tp sub 1, tp << 1)
for acc3 = toseq.typesyms, q ∈ toseq.asset.typesused
do
 let z = typeentry(q, empty:seq.mytype),
 if z ∈ typesyms then acc3 else acc3 + z,
resolvetypesize.acc3

function typesused(sym:symbol) seq.mytype
{only includes parameter of seq and encoding and excludes types int, real, boolea, ptr, and T}
for acc = empty:seq.mytype, t ∈ types.sym
do
 let typ = if isseq.t ∨ isencoding.t then parameter.t else t,
 if iscore4.typ ∨ typ = typeT then acc else acc + typ,
acc

function resolvetypesize(prg1:seq.typeentry) typedict
let bx5 = checkflat(empty:set.typeentry, prg1)
assert isempty.unknown.bx5 report
 "recursive type problem:/br:(for acc10 = "", h ∈ unknown.bx5
 do acc10 + "type:(type.h)is:(%(",", flatflds.h))" >> 1 + "/br",
 acc10)"
for acc = emptytypedict, d ∈ toseq.known.bx5 do add(acc, type.d, flatflds.d),
acc

use seq1.mytype

function checkflat(types:set.typeentry, unknown:seq.typeentry) checkflatresult2
for known = types, notflat = empty:seq.typeentry, p ∈ unknown
do
 if isflat.p ∨ type.p = type? then next(known + p, notflat)
 else
  let new = expandflat(p, types),
  if isflat.new then next(known + new, notflat) else next(known, notflat + new),
if isempty.notflat ∨ n.unknown = n.notflat then checkflatresult2(known, notflat)
else checkflat(known, notflat)

type checkflatresult2 is known:set.typeentry, unknown:seq.typeentry

function isflat(p:typeentry) boolean
if isseq.type.p then true
else if isempty.flatflds.p then false
else
 for state = true, t ∈ flatflds.p
 while state
 do iscore4.t ∨ t ∈ [typeT, typeword] ∨ isseq.t ∨ isencoding.t,
 state

function expandflat(p:typeentry, types:set.typeentry) typeentry
let newflat = expandflat(type.p, flatflds.p, types),
if newflat = flatflds.p then p else typeentry(type.p, newflat)

function expandflat(type:mytype, flatflds:seq.mytype, types:set.typeentry) seq.mytype
if isempty.flatflds then
 let f3 = lookup(types, typeentry(abstracttype.type, empty:seq.mytype)),
 if isempty.f3 then flatflds
 else expandflat(type, replaceT(parameter.type, flatflds.f3 sub 1), types)
else
 for acc = empty:seq.mytype, unchanged = true, t ∈ flatflds
 do
  if iscore4.t ∨ t ∈ [typeT, typeword] ∨ isseq.t ∨ isencoding.t then next(acc + t, unchanged)
  else
   let f = lookup(types, typeentry(t, empty:seq.mytype)),
   if isempty.f then
    let t2 = abstracttype.t,
    if t2 = t then next(acc + t, unchanged)
    else
     let f3 = lookup(types, typeentry(t2, empty:seq.mytype)),
     if isempty.f3 then next(acc + t, unchanged)
     else next(acc + replaceT(parameter.t, flatflds.f3 sub 1), false)
   else next(acc + flatflds.f sub 1, false),
 if unchanged then flatflds else expandflat(type, acc, types)

function replaceT(with:mytype, typs:seq.mytype) seq.mytype
for acc = empty:seq.mytype, t ∈ typs do acc + replaceT(with, t),
acc

Function asseqseqmytype(dict:typedict) seq.seq.mytype
for acc = empty:seq.seq.mytype, tr ∈ toseq.totypedict.dict do acc + totypeseq.tr,
acc

Function %(dict:typedict) seq.word
for txt = "", tr ∈ toseq.totypedict.dict
do
 for acc2 = txt, t ∈ totypeseq.tr do acc2 + %.t,
 acc2 + "/br",
txt

Function add(alltypes:typedict, t:mytype, flatflds:seq.mytype) typedict
typedict(totypedict.alltypes + typeentry(t, flatflds))

Function flatflds(alltypes:typedict, type:mytype) seq.mytype
let t = lookup(totypedict.alltypes, typeentry(type, empty:seq.mytype)),
if isempty.t then empty:seq.mytype else flatflds.t sub 1

Function subdict(all:typedict, t:mytype) typedict
let sub = typedict.lookup(totypedict.all, typeentry(t, empty:seq.mytype)),
closedict(all, sub)

function closedict(all:typedict, subdict:typedict) typedict
for acc = empty:set.mytype, have = empty:set.mytype, te ∈ toseq.totypedict.subdict
do
 next(
  for acc2 = acc, t ∈ flatflds.te do if isseq.t then acc2 + parameter.t else acc2 + t,
  acc2
  , have + type.te
 )
let need = acc \ (asset.[typeint, typeboolean, typeptr, typereal, typeword] ∪ have)
for new = empty:set.typeentry, t ∈ toseq.need
do
 let x = lookup(totypedict.all, typeentry(t, empty:seq.mytype)),
 if isempty.x ∧ isseq.t then new + typeentry(t, [t]) else new ∪ x,
if isempty.new then subdict else closedict(all, typedict(totypedict.subdict ∪ new))

Function basetype(a:seq.mytype, alltypes:typedict) seq.mytype
for acc = empty:seq.mytype, e ∈ a do acc + basetype(e, alltypes),
acc

Function basetype(typ:mytype, alltypes:typedict) mytype
if isseq.typ then
 let para = parameter.typ,
 if para = typebyte ∨ iscore4.typ ∨ typ = typeT then typ
 else seqof.coretype(parameter.typ, alltypes, false)
else coretype(typ, alltypes, true)

function coretype(typ:mytype, alltypes:typedict, nopacked:boolean) mytype
let maxsize =
 if nopacked then empty:seq.mytype
 else [typepacked2, typepacked3, typepacked4, typepacked5, typepacked6],
if iscore4.typ ∨ typ = typeT then typ
else if isencoding.typ then typeint
else if isseq.typ then typeptr
else
 let flatflds1 = flatflds(alltypes, typ)
 let flatflds =
  if isempty.flatflds1 then
   for j = empty:seq.mytype, t ∈ flatflds(alltypes, abstracttype.typ)
   do j + replaceT(parameter.typ, t),
   j
  else flatflds1,
 let fldsize = n.flatflds,
 if fldsize = 1 then coretype(flatflds sub 1, alltypes, nopacked)
 else if fldsize = 0 then typ
 else if fldsize - 1 > n.maxsize then typeptr
 else maxsize sub (fldsize - 1)
 