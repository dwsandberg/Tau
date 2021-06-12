Module mytype

use standard

use seq.mytype

use xxhash

use otherseq.typedef

Export type:mytype

Export typerep(mytype)seq.typedef

type mytype is typerep:seq.typedef

type modref is library:word, name:word, para:mytype

Export type:modref

Export para(modref)mytype

Export name(modref)word

Export library(modref)word

Export modref(word, word, mytype)modref

type typedef is name:word, module:word, library:word

Export type:typedef

Export name(typedef)word

Export module(typedef)word

Export library(typedef)word

Function print(s:mytype)seq.word
 for acc ="", t = typerep.s do acc + "." + name.t /for(acc << 1)

Function =(a:mytype, b:mytype)boolean typerep.a = typerep.b

Function abstracttypeof(t:mytype)mytype mytype.[ first.typerep.t]

Function abstracttypeof2(t:mytype)mytype mytype.[ first.typerep.t, first.typerep.typeT]

Function isabstract(m:modref)boolean not.isempty.typerep.para.m ∧ isabstract.para.m

Function issimple(m:modref)boolean isempty.typerep.para.m

Function parameter(t:mytype)mytype mytype(typerep.t << 1)

Function isabstract(a:mytype)boolean last.typerep.a = first.typerep.typeT

Function replaceT(with:mytype, m:mytype)mytype
 if isabstract.m then mytype(typerep.m >> 1 + typerep.with)else m

Function =(a:typedef, b:typedef)boolean name.a = name.b

∧ modname.a = modname.b

Function ?(a:mytype, b:mytype)ordering typerep.a ? typerep.b

Function ?(a:typedef, b:typedef)ordering name.a ? name.b

∧ modname.a ? modname.b

Function print(s:modref)seq.word
 if issimple.s then [ name.s]else [ name.s,"."_1] + print.para.s

Function replaceT(with:mytype, m:modref)modref
 if issimple.m ∨ not.isabstract.para.m then m
 else modref(library.m, name.m, mytype(typerep.para.m >> 1 + typerep.with))

Function typeint mytype typeref."int internal."

Function typeptr mytype typeref."ptr tausupport."

Function typeboolean mytype typeref."boolean standard."

Function typereal mytype typeref."real internal."

Function typeT mytype typeref."T internal."

Function typeref(s:seq.word)mytype
 assert length.s = 3 report"typereferror" + s
  mytype.[ typedef(first.s, s_2, s_3)]

Function internalmod modref moduleref."internal"

Function hash(b:seq.mytype, other:int)int
 for acc = hashstart, a = b >> 1 do
  for acc2 = acc, e = typerep.a do hash(acc2, other)/for(acc2)
 /for(finalmix.hash(acc, other))

------------------

Function iscomplex(a:mytype)boolean length.typerep.a > 1

Function abstracttype(m:mytype)word name.first.typerep.m

Function addabstract(a:mytype, t:mytype)mytype mytype([ first.typerep.a] + typerep.t)

Function typeref3(modname:modref, typname:word)mytype typeref.[ typname, name.modname, library.modname]

Function TypeFromOldTyperep(m:seq.word)mytype
 mytype.for acc = empty:seq.typedef, e = m do
  [ typedef(e,"?"_1,"?"_1)] + acc
 /for(acc)

Function oldTypeRep(m:mytype)seq.word
 for acc ="", e = typerep.m do [ name.e] + acc /for(acc)

Function parsetype(s:seq.word)mytype
 for acc ="", w = s do
  if w = "."_1 then acc else [ w] + acc
 /for(TypeFromOldTyperep.acc)

Function tomodref(m:mytype)modref modref("."_1, abstracttype.m, parameter.m)

Function moduleref(modname:seq.word, para:mytype)modref modref("."_1, modname_1, para)

Function moduleref(modname:seq.word)modref moduleref(modname, mytype.empty:seq.typedef)

------------

use set.modref

use otherseq.mytype

use set.mytype

use seq.passtypes

use set.passtypes

use set.typedef

use set.seq.typedef

use seq.seq.word

use otherseq.modref

Export type:passtypes

Export modname(passtypes)modref

Export defines(passtypes)set.mytype

Export uses(passtypes)set.modref

function modname(a:typedef)word module.a

Function modref(lib:word, name:word)modref modref(lib, name, mytype.empty:seq.typedef)

Function typeseqdec mytype typeref."sequence internal. "

function typedef(a:seq.word)typedef typedef(a_1, a_2, a_3)

Function module2(typ:mytype)modref
let t = first.typerep.typ
 modref(library.t, modname.t, if length.typerep.typ > 1 then typeT else mytype.empty:seq.typedef)

Function =(a:modref, b:modref)boolean name.a = name.b ∧ para.a = para.b

Function ?(a:modref, b:modref)ordering name.a ? name.b ∧ para.a ? para.b

Function ?2(a:modref, b:modref)ordering name.a ? name.b

Function ?2(a:seq.typedef, b:seq.typedef)ordering ?2(mytype.a, mytype.b)

Function ?2(a1:mytype, b1:mytype)ordering
let a = typerep.a1
let b = typerep.b1
let lengtha = length.a
let lengthb = length.b
 if lengtha > lengthb then GT else if lengtha < lengthb then LT else subcmp(a, b, 1)

function subcmp(a:seq.typedef, b:seq.typedef, i:int)ordering
 if i > length.a then EQ
 else
  let c = name.a_i ? name.b_i
   if c = EQ then subcmp(a, b, i + 1)else c

Function typebase(i:int)mytype mytype.[ typedef."$base internal.", typedef(toword.i,"internal"_1,"."_1)]

Function internalmod(s:seq.word)modref modref("."_1, s_1)

Function printrep(s:mytype)seq.word
 for acc = [ toword.length.typerep.s], t = typerep.s do
  acc + [ name.t, modname.t, library.t]
 /for(acc)

Function parsemytype(s:seq.word)mytype
 for acc = empty:seq.typedef, i = arithseq(toint.s_1, 3, 2)do
  acc + typedef(s_i, s_(i + 1), s_(i + 2))
 /for(mytype.acc)

Function seqof(base:mytype)mytype mytype([ typedef."seq seq."] + typerep.base)

Function isseq(t:mytype)boolean first.typerep.t = typedef."seq seq."

Function isencoding(t:mytype)boolean first.typerep.t = typedef."encoding encoding."

Function processof(base:mytype)mytype mytype([ typedef."process process."] + typerep.base)

type passtypes is modname:modref, defines:set.mytype, unresolveduses:seq.seq.word, unresolvedexports:seq.seq.word, exports:set.mytype, uses:set.modref

Function resolvetypes(t:seq.seq.word, lib:word)set.passtypes
 for knownmods = empty:set.modref, s = empty:set.passtypes, defines = empty:set.mytype, unresolveduses = empty:seq.seq.word, unresolvedexports = empty:seq.seq.word, mref = internalmod, m = t do
  if isempty.m then next(knownmods, s, defines, unresolveduses, unresolvedexports, mref)
  else if first.m ∈ "Module module"then
  let p2 = resolve(s, knownmods, passtypes(mref, defines, unresolveduses, unresolvedexports, empty:set.mytype, empty:set.modref))
  let newmod = if length.m > 2 then modref(lib, m_2, typeT)else modref(lib, m_2)
  next(knownmods + newmod, s + p2, empty:set.mytype, empty:seq.seq.word, empty:seq.seq.word, newmod)
  else if first.m ∈ "use"then next(knownmods, s, defines, unresolveduses + m << 1, unresolvedexports, mref)
  else if first.m ∈ "type"then next(knownmods, s, defines + newtype(mref, m_2), unresolveduses, unresolvedexports, mref)
  else if subseq(m, 1, 3) = "Export type:"then
   next(knownmods, s, defines, unresolveduses, unresolvedexports + m << 3, mref)
  else next(knownmods, s, defines, unresolveduses, unresolvedexports, mref)
 /for(let p2 = resolve(s, knownmods, passtypes(mref, defines, unresolveduses, unresolvedexports, empty:set.mytype, empty:set.modref))
 R(s + p2, knownmods, 100000))

function newtype(mref:modref, name:word)mytype mytype([ typedef(name, name.mref, library.mref)] + typerep.para.mref)

function R(s1:set.passtypes, knownmods:set.modref, countin:int)set.passtypes
 if countin = 0 then s1
 else
  { assert countin /in [ 100000, 134, 45, 22, 1]report"C"+ print.countin }
  for cnt = 0, acc = empty:set.passtypes, p = toseq.s1 do
   next(cnt + length.unresolvedexports.p + length.unresolveduses.p, acc + resolve(s1, knownmods, p))
  /for(assert countin ≠ cnt report"unresolvedtypes"
  + for acc2 ="", p2 = toseq.s1 do acc2 + print.p2 + EOL /for(acc2)
  R(acc, knownmods, cnt))

function resolve(all:set.passtypes, knownmods:set.modref, p:passtypes)passtypes
let dict = formtypedict(all, p)
let p1 = for exports = exports.p, x = empty:seq.seq.word, t2 = unresolvedexports.p do
let b = resolvetype(dict, t2)
if isempty.b then next(exports, x + t2)else next(exports + b_1, x)
/for(passtypes(modname.p, defines.p, unresolveduses.p, x, exports, uses.p))
for uses = uses.p, x = empty:seq.seq.word, t2 = unresolveduses.p do
 let b = resolveuse(dict, knownmods, t2)
 if isempty.b then next(uses, x + t2)else next(uses + b_1, x)
 /for(passtypes(modname.p, defines.p, x, unresolvedexports.p1, exports.p1, uses))

function ?(a:passtypes, b:passtypes)ordering name.modname.a ? name.modname.b

Function print(p:passtypes)seq.word
" /keyword module" + print.modname.p + EOL + " /keyword defines"
 + for acc ="", t = toseq.defines.p do acc + print.t /for(acc)
 + if not.isempty.unresolveduses.p then
  for acc =" /br  /keyword unresolveduses", s = unresolveduses.p do acc + s /for(acc)
 else""/if
 + for acc =" /br  /keyword uses", s = toseq.uses.p do acc + print.s /for(acc)
 + if not.isempty.unresolvedexports.p then
 " /br  /keyword unresolvedexports" + for acc ="", s = unresolvedexports.p do acc + s /for(acc)
 else""/if
 + " /br  /keyword exports"
 + for acc ="", t = toseq.exports.p do acc + print.t /for(acc)

Function resolvetype(knowntypes:set.mytype, ref:seq.word)seq.mytype
 if ref = "int"then [ typeint]
 else if ref = "boolean"then [ typeboolean]
 else if ref = "T"then [ typeT]
 else if ref = "real"then [ typereal]
 else
  let x = for acc = empty:seq.typedef, w = ref do
   if w = "."_1 then acc else acc + typedef(w,"internal"_1,"."_1)
  /for(mytype.acc)
  let a1 = findelement2(knowntypes, x)
  if cardinality.a1 = 1 then toseq.a1
   else if length.ref = 1 then empty:seq.mytype
   else
    let a = findelement2(knowntypes, mytype([ typedef(ref_1,"internal"_1,"."_1)] + typerep.typeT))
    if cardinality.a ≠ 1 then empty:seq.mytype
     else if ref_2 = "."_1 then
     let b = resolvetype(knowntypes, ref << 2)
     if isempty.b then b else [ mytype([(typerep.(toseq.a)_1)_1] + typerep.b_1)]
     else empty:seq.mytype

function resolveuse(knowntypes:set.mytype, knownmodules:set.modref, ref:seq.word)seq.modref
let a = findelement2(knownmodules, modref("?"_1, ref_1))
if cardinality.a ≠ 1 then empty:seq.modref
 else if length.ref = 1 then toseq.a
 else
  let b = resolvetype(knowntypes, ref << 2)
  { assert cardinality.knownmodules < 30 /or ref /ne"seq.word"report"ref"+ ref + toword.length.b + ref << 2 + for acc ="", t = toseq.knowntypes do acc + EOL + print.t /for(acc)}
   if isempty.b then empty:seq.modref else [ modref(library.a_1, name.a_1, b_1)]

Function findpasstypes(all:set.passtypes, lib:word, m:seq.word)set.passtypes
let newmod = if length.m > 2 then modref(lib, m_2, typeT)else modref(lib, m_2)
findelement(passtypes(newmod, empty:set.mytype, empty:seq.seq.word, empty:seq.seq.word, empty:set.mytype, empty:set.modref)
 , all
 )

Function formtypedict(all:set.passtypes, this:passtypes)set.mytype
 for r = exports.this, u = toseq.uses.this do
 let a = findelement(passtypes(u, empty:set.mytype, empty:seq.seq.word, empty:seq.seq.word, empty:set.mytype, empty:set.modref)
 , all
 )
 if isempty.a then r else r ∪ exports.a_1
 /for(r ∪ defines.this) 