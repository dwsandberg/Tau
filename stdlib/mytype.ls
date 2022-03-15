Module mytype

use standard

use xxhash

use otherseq.modref

use set.modref

use otherseq.mytype

use seq.mytype

use set.mytype

use seq.passtypes

use set.passtypes

use otherseq.typedef

use seq.typedef

use set.typedef

use set.seq.typedef

use seq.seq.word

Export type:mytype

Export typerep(mytype)seq.typedef

type mytype is typerep:seq.typedef

type modref is library:word, name:word, para:mytype

Export type:modref

Export para(modref)mytype

Export name(modref)word

Export library(modref)word

type typedef is name:word, modname:word, library:word

Export modname(a:typedef)word

Export type:typedef

Export name(typedef)word

Export library(typedef)word

Function print(s:mytype)seq.word
for acc = "", t ∈ typerep.s do acc + "." + name.t /for(acc << 1)

Function fullprint(s:mytype)seq.word
for acc = "", t ∈ typerep.s do acc + name.t + modname.t + library.t /for(acc)

Function =(a:mytype, b:mytype)boolean typerep.a = typerep.b

Function abstracttypename(m:mytype)word name.first.typerep.m

Function abstracttype(t:mytype)mytype
if length.typerep.t = 1 then t else mytype.[first.typerep.t, first.typerep.typeT]

Function abstractModref(typ:mytype)modref
let t = first.typerep.typ
modref(library.t, modname.t, if length.typerep.typ > 1 then typeT else noparameter)

Function tomodref(m:mytype)modref
let t = first.typerep.m
modref(library.t, modname.t, parameter.m)

Function abstractmod(m:modref)modref
if issimple.m ∨ para.m = typeT then m else modref(library.m, name.m, typeT)

Function isabstract(m:modref)boolean not.isempty.typerep.para.m ∧ isabstract.para.m

Function issimple(m:modref)boolean isempty.typerep.para.m

Function parameter(t:mytype)mytype mytype(typerep.t << 1)

Function isabstract(a:mytype)boolean last.typerep.a = first.typerep.typeT

Function replaceT(with:mytype, m:mytype)mytype
if isabstract.m then mytype(typerep.m >> 1 + typerep.with)else m

Function =(a:typedef, b:typedef)boolean name.a = name.b ∧ modname.a = modname.b

∧ library.a=library.b

Function ?(a:mytype, b:mytype)ordering typerep.a ? typerep.b

Function ?(a:typedef, b:typedef)ordering name.a ? name.b ∧ modname.a ? modname.b

∧ library.a ? library.b

Function print(s:modref)seq.word
if issimple.s then[name.s]else[name.s, "."_1] + print.para.s

Function replaceT(with:mytype, m:modref)modref
if issimple.m ∨ not.isabstract.para.m then m
else modref(library.m, name.m, mytype(typerep.para.m >> 1 + typerep.with))

Function typeint mytype typeref."int internal internallib"

Function typeptr mytype typeref."ptr tausupport"

Function typeboolean mytype typeref."boolean standard"

Function typereal mytype typeref."real internal internallib"

Function typeT mytype typeref."T internal internallib"

Function typeseqdec mytype typeref."sequence internal internallib"

Function typeref(s:seq.word)mytype
if length.s = 2 then mytype.[typedef(first.s, s_2, "stdlib"_1)]
else
 assert length.s = 3 report"typereferror" + s + stacktrace
 mytype.[typedef(first.s, s_2, s_3)]

Function internalmod modref moduleref."internallib internal"

Function hash(b:seq.mytype, other:seq.word)int 
for acc = hashstart, a ∈ b >> 1 do 
for acc2 = acc, e ∈ typerep.a do 
hash2(hash2(acc, name.e), modname.e)
/for(acc2)
/for(
 for acc3=acc, w /in other do
   hash2(acc3, w)
 /for(finalmix.acc3))
 
function hash2(b:bits,w:word) bits  hash(b,hash.w)


use bits


------------------

Function iscomplex(a:mytype)boolean length.typerep.a > 1

Function addabstract(a:mytype, t:mytype)mytype mytype([first.typerep.a] + typerep.t)

Function oldTypeRep(m:mytype)seq.word for acc = "", e ∈ typerep.m do[name.e] + acc /for(acc)

Function moduleref(modname:seq.word, para:mytype)modref
if length.modname = 1 then modref("stdlib"_1, modname_1, para)
else
 assert length.modname = 2 report"modname must be of length 2" + modname
 modref(modname_1, modname_2, para)

Function moduleref(modname:seq.word)modref moduleref(modname, noparameter)

------------

Export type:passtypes

Export modname(passtypes)modref

Export defines(passtypes)set.mytype

Export uses(passtypes)set.modref

function noparameter mytype mytype.empty:seq.typedef

Function =(a:modref, b:modref)boolean name.a = name.b ∧ para.a = para.b

∧ library.a=library.b

Function ?(a:modref, b:modref)ordering name.a ? name.b ∧ para.a ? para.b

∧ library.a ? library.b

Function ?2(a:modref, b:modref)ordering name.a ? name.b

Function ?2(a:seq.typedef, b:seq.typedef)ordering ?2(mytype.a, mytype.b)

Function ?2(a1:mytype, b1:mytype)ordering
let a = typerep.a1
let b = typerep.b1
let lengtha = length.a
let lengthb = length.b
if lengtha > lengthb then GT
else if lengtha < lengthb then LT else subcmp(a, b, 1)

function subcmp(a:seq.typedef, b:seq.typedef, i:int)ordering
if i > length.a then EQ
else
 let c = name.a_i ? name.b_i
 if c = EQ then subcmp(a, b, i + 1)else c

Function typebase(i:int)mytype
mytype.[typedef("$base"_1, "internal"_1, "internallib"_1)
, typedef(toword.i, "internal"_1, "internallib"_1)
]

Function internalmod(s:seq.word)modref modref("internallib"_1, "."_1, noparameter)

Function printrep(s:mytype)seq.word
for acc = [toword.length.typerep.s], t ∈ typerep.s do acc + [name.t, modname.t, library.t]/for(acc)

Function seqof(base:mytype)mytype mytype(typerep.typeref."seq seq" + typerep.base)

Function isseq(t:mytype)boolean first.typerep.t = first.typerep.typeref."seq seq"

Function isencoding(t:mytype)boolean first.typerep.t = first.typerep.typeref."encoding encoding"

Function encodingof(base:mytype)mytype mytype(typerep.typeref."encoding encoding" + typerep.base)

Function processof(base:mytype)mytype mytype(typerep.typeref."process process" + typerep.base)

type passtypes is modname:modref
, defines:set.mytype
, unresolveduses:seq.seq.word
, unresolvedexports:seq.seq.word
, exports:set.mytype
, uses:set.modref


Function passtypes(modname:modref, defines:set.mytype, exports:set.mytype)passtypes
passtypes(modname, defines, empty:seq.seq.word, empty:seq.seq.word, exports, empty:set.modref)

Function resolvetypes(librarytypes:set.passtypes, t:seq.seq.word, lib:word)set.passtypes
let librarymods = for acc = empty:set.modref, p ∈ toseq.librarytypes do acc + modname.p /for(acc)
for knownmods = librarymods
, s = librarytypes
, defines = empty:set.mytype
, unresolveduses = empty:seq.seq.word
, unresolvedexports = empty:seq.seq.word
, mref = internalmod
, m ∈ t
do
 if isempty.m then next(knownmods, s, defines, unresolveduses, unresolvedexports, mref)
 else if first.m ∈ "Module module"then
  let newmod = modref(lib, m_2, if length.m > 2 then typeT else noparameter)
  if mref = internalmod then
   next(knownmods + newmod, s, empty:set.mytype, empty:seq.seq.word, empty:seq.seq.word, newmod)
  else
   let p2 = 
    resolve(s
    , knownmods
    , passtypes(mref, defines, unresolveduses, unresolvedexports, empty:set.mytype, empty:set.modref)
    )
   next(knownmods + newmod, s + p2, empty:set.mytype, empty:seq.seq.word, empty:seq.seq.word, newmod)
 else if first.m ∈ "use"then
  next(knownmods, s, defines, unresolveduses + m << 1, unresolvedexports, mref)
 else if first.m ∈ "type"then
  next(knownmods, s, defines + newtype(mref, m_2), unresolveduses, unresolvedexports, mref)
 else if subseq(m, 1, 3) = "Export type:"then
  next(knownmods, s, defines, unresolveduses, unresolvedexports + m << 3, mref)
 else next(knownmods, s, defines, unresolveduses, unresolvedexports, mref)
/for(let p2 = 
 resolve(s
 , knownmods
 , passtypes(mref, defines, unresolveduses, unresolvedexports, empty:set.mytype, empty:set.modref)
 )
R(s + p2, knownmods, 100000))

Function newtype(mref:modref, name:word)mytype mytype([typedef(name, name.mref, library.mref)] + typerep.para.mref)

function R(s1:set.passtypes, knownmods:set.modref, countin:int)set.passtypes
if countin = 0 then s1
else
 {assert countin /in[100000, 134, 45, 22, 1]report"C"+print.countin}
 for cnt = 0, acc = empty:set.passtypes, p ∈ toseq.s1 do
  next(cnt + length.unresolvedexports.p + length.unresolveduses.p, acc + resolve(s1, knownmods, p))
 /for(assert countin ≠ cnt
 report for acc2 = "", p2 ∈ toseq.s1 do acc2 + printunresolved.p2 /for(acc2)
 R(acc, knownmods, cnt))

function printunresolved(p:passtypes)seq.word
let txt = 
 for acc = "", t ∈ unresolveduses.p do acc + "use" + t + EOL /for(acc)
 + for acc = "", t ∈ unresolvedexports.p do acc + "Export type:" + t + EOL /for(acc)
if isempty.txt then""
else"module" + print.modname.p + "contains lines that cannot be resolved:" + txt

function resolve(all:set.passtypes, knownmods:set.modref, p:passtypes)passtypes
let dict = formtypedict(all, p)
let p1 = 
 for exports = exports.p, x = empty:seq.seq.word, t2 ∈ unresolvedexports.p do
  let b = resolvetype(dict, t2)
  if isempty.b then next(exports, x + t2)else next(exports + b_1, x)
 /for(passtypes(modname.p, defines.p, unresolveduses.p, x, exports, uses.p))
for uses = uses.p, x = empty:seq.seq.word, t2 ∈ unresolveduses.p do
 let b = resolveuse(dict, knownmods, t2)
 if isempty.b then next(uses, x + t2)else next(uses + b_1, x)
/for(passtypes(modname.p, defines.p, x, unresolvedexports.p1, exports.p1, uses))

Function ?(a:passtypes, b:passtypes)ordering name.modname.a ? name.modname.b

Function print(p:passtypes)seq.word
" /keyword module" + print.modname.p + EOL + " /keyword defines"
+ for acc = "", t ∈ toseq.defines.p do acc + print.t /for(acc)
+ if not.isempty.unresolveduses.p then
 for acc = " /br  /keyword unresolveduses", s ∈ unresolveduses.p do acc + s /for(acc)
else""/if
+ for acc = " /br  /keyword uses", s ∈ toseq.uses.p do acc + print.s /for(acc)
+ if not.isempty.unresolvedexports.p then
 " /br  /keyword unresolvedexports"
 + for acc = "", s ∈ unresolvedexports.p do acc + s /for(acc)
else""/if
+ " /br  /keyword exports"
+ for acc = "", t ∈ toseq.exports.p do acc + print.t /for(acc)

Function resolvetype(knowntypes:set.mytype, ref:seq.word)seq.mytype
if ref = "int"then[typeint]
else if ref = "boolean"then[typeboolean]
else if ref = "T"then[typeT]
else if ref = "real"then[typereal]
else
 let x = 
  for acc = empty:seq.typedef, w ∈ ref do
   if w = "."_1 then acc else acc + typedef(w, "internal"_1, "."_1)
  /for(mytype.acc)
 let a1 = findelement2(knowntypes, x)
 if cardinality.a1 = 1 then toseq.a1
 else if length.ref = 1 then empty:seq.mytype
 else
  let a = 
   findelement2(knowntypes
   , mytype([typedef(ref_1, "internal"_1, "."_1)] + typerep.typeT)
   )
  if cardinality.a ≠ 1 then empty:seq.mytype
  else if ref_2 = "."_1 then
   let b = resolvetype(knowntypes, ref << 2)
   if isempty.b then b else[mytype([(typerep.(toseq.a)_1)_1] + typerep.b_1)]
  else empty:seq.mytype

function resolveuse(knowntypes:set.mytype, knownmodules:set.modref, ref:seq.word)seq.modref
let a = findelement2(knownmodules, modref("?"_1, ref_1, noparameter))
if cardinality.a ≠ 1 then empty:seq.modref
else if length.ref = 1 then toseq.a
else
 let b = resolvetype(knowntypes, ref << 2)
 {assert cardinality.knownmodules < 30 /or ref /ne"seq.word"report"ref"+ref+toword.length.b+ref << 2+for acc=""
, t=toseq.knowntypes do acc+EOL+print.t /for(acc)}
 if isempty.b then empty:seq.modref else[modref(library.a_1, name.a_1, b_1)]

Function findpasstypes(all:set.passtypes, lib:word, m:seq.word)set.passtypes
let newmod = modref(lib, m_2, if length.m > 2 then typeT else noparameter)
lookup(all
, passtypes(newmod, empty:set.mytype, empty:seq.seq.word, empty:seq.seq.word, empty:set.mytype
, empty:set.modref)
)

Function formtypedict(all:set.passtypes, this:passtypes)set.mytype
for r = exports.this, u ∈ toseq.uses.this do
 let a = 
  lookup(all
  , passtypes(u, empty:set.mytype, empty:seq.seq.word, empty:seq.seq.word, empty:set.mytype, empty:set.modref)
  )
 if isempty.a then r else r ∪ exports.a_1
/for(r ∪ defines.this) 