Module typedict

use mytype

use standard

use symbol

use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use set.symdef

use seq.typeentry

use set.typeentry

use seq.seq.mytype

Export type:typeentry

Export type:typedict

type typeentry is totypeseq:seq.mytype

type typedict is totypedict:set.typeentry

Function emptytypedict typedict typedict.empty:set.typeentry

function ?(a:typeentry, b:typeentry)ordering first.totypeseq.a ? first.totypeseq.b

function type(a:typeentry)mytype first.totypeseq.a

function flatflds(a:typeentry)seq.mytype totypeseq.a << 1

function typeentry(t:mytype, flat:seq.mytype)typeentry typeentry([t] + flat)

Function buildtypedict(zz1:set.symdef, types:seq.seq.mytype)typedict
for acc = empty:set.symbol, p ∈ toseq.zz1 do acc + sym.p /for(buildtypedict(acc, types))

Function addtypes(alltypes:typedict, syms:set.symbol)typedict
let typesused = 
 for acc = empty:seq.mytype, sym ∈ toseq.syms do
  if isstart.sym ∨ isSequence.sym then acc + typesused.sym
  else if isconst.sym ∨ isGlobal.sym ∨ isInternal.sym ∨ sym = Optionsym ∨ inModFor.sym ∨ isspecial.sym then acc
  else if issimple.module.sym then acc else acc + para.module.sym /if + typesused.sym
 /for(acc)
for acc = alltypes, d ∈ toseq.asset.typesused do
 if d = type? ∨ abstracttypename.d ∈ "$base"then acc else addtype(acc, d)
/for(acc)

function print(t:seq.mytype)seq.word for txt = "", a ∈ t do txt + print.a /for(txt)

Function addtype(alltypes:typedict, type:mytype)typedict
if iscore4.type ∨ type = typeT then alltypes
else if isseq.type then addtype(alltypes, parameter.type)
else
 let t = lookup(totypedict.alltypes, typeentry(type, empty:seq.mytype))
 if not.isempty.t then alltypes
 else
  let flatflds = expandflat(type, empty:seq.mytype, totypedict.alltypes)
  let newtr = typeentry(type, flatflds)
  if isflat.newtr then
   {add to typedict and then check to make sure parameters are in typedict}
   for acc = typedict(totypedict.alltypes + newtr), subfld ∈ flatflds do
    if isseq.subfld ∨ isencoding.subfld then addtype(acc, subfld)else acc
   /for(acc)
  else
   {add types not in typedict and try again}
   for acc = alltypes, subfld ∈ flatflds do
    if iscore4.subfld ∨ subfld = typeT ∨ isseq.subfld ∨ isencoding.subfld then acc
    else addtype(acc, subfld)
   /for(assert cardinality.totypedict.alltypes < cardinality.totypedict.acc
   report"PROBLEM" + print.type + "flat:"
   + for txt = "", g ∈ flatflds do txt + print.g /for(txt + EOL)
   + print.acc
   addtype(acc, type))

Function check(smalldict:typedict, bigdict:typedict)typedict
for small = smalldict, atyprep ∈ toseq.totypedict.bigdict do
 let t = type.atyprep
 let new = addtype(smalldict, t)
 assert isseq.t ∨ flatwithtype(new, t) = flatwithtype(bigdict, t)
 report"check" + print.t + "flat:"
 + for txt = "", g ∈ flatwithtype(bigdict, t)do txt + print.g /for(txt + EOL)
 + "flat:"
 + for txt = "", g ∈ flatwithtype(new, t)do txt + print.g /for(txt + EOL)
 new
/for(small)

Function buildtypedict(syms:set.symbol, types:seq.seq.mytype)typedict
let typesused = for acc = empty:seq.mytype, sym ∈ toseq.syms do acc + typesused.sym /for(acc)
let typesyms = 
 for acc = empty:set.typeentry, tp ∈ types do acc + typeentry(first.tp, tp << 1)/for(acc)
for acc3 = toseq.typesyms, q ∈ toseq.asset.typesused do
 let z = typeentry(q, empty:seq.mytype)
 if z ∈ typesyms then acc3 else acc3 + z
/for(resolvetypesize.acc3)

function typesused(sym:symbol)seq.mytype
{only includes parameter of seq and encoding and excludes types int, real, boolea, ptr, and T}
for acc = empty:seq.mytype, t ∈ types.sym do
 let typ = if isseq.t ∨ isencoding.t then parameter.t else t
 if iscore4.typ ∨ typ = typeT then acc else acc + typ
/for(acc)

function resolvetypesize(prg1:seq.typeentry)typedict
let bx5 = checkflat(empty:set.typeentry, prg1)
assert isempty.unknown.bx5
report"recursive type problem: /br"
+ for acc10 = "", h ∈ unknown.bx5 do acc10 + print2.h + EOL /for(acc10)
{+" /p  /p known types  /p"+for acc10="", h=toseq.known.bx5 do acc10+print.h+EOL /for(acc10)}
for acc = emptytypedict, d ∈ toseq.known.bx5 do add(acc, type.d, flatflds.d)/for(acc)

function print(s:symdef)seq.word print.sym.s + print.code.s

function print(h:typeentry)seq.word for acc = print.type.h, z ∈ flatflds.h do acc + print.z /for(acc)

function print2(h:typeentry)seq.word
for acc = "type" + print.type.h + "is", z ∈ flatflds.h do acc + print.z + ", "/for(acc >> 1)

function checkflat(types:set.typeentry, unknown:seq.typeentry)checkflatresult2
for known = types, notflat = empty:seq.typeentry, p ∈ unknown do
 if isflat.p ∨ abstracttypename.type.p = "$base"_1 ∨ type.p = type? then
  next(known + p, notflat)
 else
  let new = expandflat(p, types)
  if isflat.new then next(known + new, notflat)else next(known, notflat + new)
/for(if isempty.notflat ∨ length.unknown = length.notflat then checkflatresult2(known, notflat)
else checkflat(known, notflat)/if)

type checkflatresult2 is known:set.typeentry, unknown:seq.typeentry

function isflat(p:typeentry)boolean
if isseq.type.p then true
else if isempty.flatflds.p then false
else
 for state = true, t ∈ flatflds.p while state do iscore4.t ∨ t ∈ [typeT, typeword] ∨ isseq.t ∨ isencoding.t /for(state)

function expandflat(p:typeentry, types:set.typeentry)typeentry
let newflat = expandflat(type.p, flatflds.p, types)
if newflat = flatflds.p then p else typeentry(type.p, newflat)

function expandflat(type:mytype, flatflds:seq.mytype, types:set.typeentry)seq.mytype
if isempty.flatflds then
 let f3 = lookup(types, typeentry(abstracttype.type, empty:seq.mytype))
 if isempty.f3 then flatflds else expandflat(type, replaceT(parameter.type, flatflds.f3_1), types)
else
 for acc = empty:seq.mytype, unchanged = true, t ∈ flatflds do
  if iscore4.t ∨ t ∈ [typeT, typeword] ∨ isseq.t ∨ isencoding.t then next(acc + t, unchanged)
  else
   let f = lookup(types, typeentry(t, empty:seq.mytype))
   if isempty.f then
    let t2 = abstracttype.t
    if t2 = t then next(acc + t, unchanged)
    else
     let f3 = lookup(types, typeentry(t2, empty:seq.mytype))
     {assert{print.t /ne"set.arc.T"}isempty.f3 report"K"+print.t+"K"+print.t2}
     if isempty.f3 then next(acc + t, unchanged)
     else next(acc + replaceT(parameter.t, flatflds.f3_1), false)
   else next(acc + flatflds.f_1, false)
 /for(if unchanged then flatflds else expandflat(type, acc, types)/if)

function replaceT(with:mytype, typs:seq.mytype)seq.mytype
for acc = empty:seq.mytype, t ∈ typs do acc + replaceT(with, t)/for(acc)

Function asseqseqmytype(dict:typedict)seq.seq.mytype
for acc = empty:seq.seq.mytype, tr ∈ toseq.totypedict.dict do acc + totypeseq.tr /for(acc)

Function print(dict:typedict)seq.word
for txt = "", tr ∈ toseq.totypedict.dict do
 for acc2 = txt, t ∈ totypeseq.tr do acc2 + print.t /for(acc2 + EOL)
/for(txt)

Function add(alltypes:typedict, t:mytype, flatflds:seq.mytype)typedict
typedict(totypedict.alltypes + typeentry(t, flatflds))

Function flatflds(alltypes:typedict, type:mytype)seq.mytype
{assert not.isseq.type /or parameter.type=typeT report"flattype"+print.type+stacktrace}
let t = lookup(totypedict.alltypes, typeentry(type, empty:seq.mytype))
if isempty.t then empty:seq.mytype else flatflds.t_1

Function subdict(all:typedict, t:mytype)typedict
let sub = typedict.lookup(totypedict.all, typeentry(t, empty:seq.mytype))
closedict(all, sub)

function closedict(all:typedict, subdict:typedict)typedict
let need = 
 for acc = empty:set.mytype, have = empty:set.mytype, te ∈ toseq.totypedict.subdict do
  next(for acc2 = acc, t ∈ flatflds.te do if isseq.t then acc2 + parameter.t else acc2 + t /for(acc2)
  , have + type.te
  )
 /for(acc \ (asset.[typeint, typeboolean, typeptr, typereal, typeword] ∪ have))
for new = empty:set.typeentry, t ∈ toseq.need do
 let x = lookup(totypedict.all, typeentry(t, empty:seq.mytype))
 if isempty.x ∧ isseq.t then new + typeentry(t, [t])else new ∪ x
/for(if isempty.new then subdict else closedict(all, typedict(totypedict.subdict ∪ new))/if)

Function flatwithtype(alltypes:typedict, type:mytype)seq.mytype
let t = lookup(totypedict.alltypes, typeentry(type, empty:seq.mytype))
if isempty.t then empty:seq.mytype else[type.t_1] + flatflds.t_1

Function basetype(typ:mytype, alltypes:typedict)mytype
if isseq.typ then
 let para = parameter.typ
 if para = typebyte ∨ para = typebit ∨ iscore4.typ ∨ typ = typeT then typ
 else seqof.coretype(parameter.typ, alltypes, packedtypes)
else coretype(typ, alltypes, empty:seq.mytype)

function coretype(typ:mytype, alltypes:typedict, maxsize:seq.mytype)mytype
if iscore4.typ ∨ typ = typeT then typ
else if isencoding.typ then typeint
else if isseq.typ then typeptr
else
 let flatflds1 = flatflds(alltypes, typ)
 let flatflds = 
  if isempty.flatflds1 then
   for j = empty:seq.mytype, t ∈ flatflds(alltypes, abstracttype.typ)do j + replaceT(parameter.typ, t)/for(j)
  else flatflds1
 let fldsize = length.flatflds
 if fldsize = 1 then coretype(first.flatflds, alltypes, empty:seq.mytype)
 else if fldsize = 0 then typ
 else if fldsize - 1 > length.maxsize then typeptr else maxsize_(fldsize - 1) 