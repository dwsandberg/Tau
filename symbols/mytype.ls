Module mytype

use bits

use seq.modref

use set.modref

use seq.mytype

use set.mytype

use set.passtypes

use standard

use otherseq.typedef

use xxhash

Export type:modref

Export library(modref) word

Export name(modref) word

Export para(modref) mytype

Export type:mytype

Export typerep(mytype) seq.typedef

Export type:passtypes

Export modname(passtypes) modref

Export uses(passtypes) set.modref

Export type:typedef

Export library(typedef) word

Export modname(a:typedef) word

Export name(typedef) word

type mytype is typerep:seq.typedef

type modref is library:word, name:word, para:mytype

type typedef is name:word, modname:word, library:word

Function %(s:mytype) seq.word
for acc = "", t ∈ typerep.s do acc + "." + name.t,
acc << 1

Function fullprint(s:mytype) seq.word
for acc = "", t ∈ typerep.s do acc + name.t + modname.t + library.t,
acc

Function changelibrary(s:mytype, map:seq.word) mytype
for acc = empty:seq.typedef, t ∈ typerep.s
do
 let match = 1
 let nomatch = 2
 let done = 3,
  acc
   + 
   for state = 0, result = t, x ∈ map
   while state ≠ done
   do
    if state = nomatch then
    next(0, result)
    else if state = match then
    next(done, typedef(name.t, modname.t, x))
    else next(if x = library.t then match else nomatch, result),
   result,
mytype.acc

Function =(a:mytype, b:mytype) boolean typerep.a = typerep.b

Function abstracttypename(m:mytype) word name.1#typerep.m

Function abstracttype(t:mytype) mytype
if n.typerep.t = 1 then t else mytype.[1#typerep.t, 1#typerep.typeT]

Function abstractModref(typ:mytype) modref
let t = 1#typerep.typ,
modref(library.t, modname.t, if n.typerep.typ > 1 then typeT else noparameter)

Function tomodref(m:mytype) modref
let t = 1#typerep.m,
modref(library.t, modname.t, parameter.m)

Function abstractmod(m:modref) modref
if isSimple.m ∨ para.m = typeT then m else modref(library.m, name.m, typeT)

Function isAbstract(m:modref) boolean not.isempty.typerep.para.m ∧ isAbstract.para.m

Function isSimple(m:modref) boolean isempty.typerep.para.m

Function parameter(t:mytype) mytype mytype(typerep.t << 1)

Function isAbstract(a:mytype) boolean 1^typerep.a = 1#typerep.typeT

Function replaceT(with:mytype, m:mytype) mytype
if isAbstract.m then mytype(typerep.m >> 1 + typerep.with) else m

Function replaceT(m:modref, t:mytype) modref modref(library.m, name.m, replaceT(para.m, t))

Function =(a:typedef, b:typedef) boolean
name.a = name.b ∧ modname.a = modname.b ∧ wild(library.a, library.b) = EQ

Function >1(a:typedef, b:typedef) ordering
name.a >1 name.b ∧ modname.a >1 modname.b ∧ wild(library.a, library.b)

Function >2(a:typedef, b:typedef) ordering name.a >1 name.b

function wild(a:word, b:word) ordering if a ∈ "*" ∨ b ∈ "*" then EQ else a >1 b

Function >1(a:mytype, b:mytype) ordering typerep.a >1 typerep.b

Function >2(a:mytype, b:mytype) ordering typerep.a >2 typerep.b

Function %(s:modref) seq.word
if isSimple.s then [name.s] else [name.s, 1#"."] + %.para.s

Function replaceT(with:mytype, m:modref) modref
if isSimple.m ∨ not.isAbstract.para.m then
m
else modref(library.m, name.m, mytype(typerep.para.m >> 1 + typerep.with))

Function typeint mytype typeref."int internal internallib"

Function typeptr mytype typeref."ptr ptr *"

Function typeboolean mytype typeref."boolean standard *"

Function typereal mytype typeref."real internal internallib"

Function typeT mytype typeref."T internal internallib"

Function typeseqdec mytype typeref."sequence internal internallib"

Function typeref(s:seq.word) mytype
assert n.s = 3 report "typereferror^(s)",
mytype.[typedef(1#s, 2#s, 3#s)]

Function internalmod modref moduleref."internallib internal"

Function hash(b:seq.mytype, other:seq.word) int
for acc = hashstart, a ∈ b >> 1
do for acc2 = acc, e ∈ typerep.a do hash2(hash2(acc, name.e), modname.e), acc2
for acc3 = acc, w ∈ other do hash2(acc3, w),
finalmix.acc3

function hash2(b:bits, w:word) bits hash(b, hash.w)

Function addabstract(a:mytype, t:mytype) mytype mytype([1#typerep.a] + typerep.t)

Function moduleref(modname:seq.word, para:mytype) modref
assert n.modname = 2 report "modname must be of length 2^(modname + stacktrace)",
modref(1#modname, 2#modname, para)

Function moduleref(modname:seq.word) modref moduleref(modname, noparameter)

function noparameter mytype mytype.empty:seq.typedef

Function =(a:modref, b:modref) boolean
name.a = name.b ∧ para.a = para.b ∧ wild(library.a, library.b) = EQ

Function >1(a:modref, b:modref) ordering
name.a >1 name.b ∧ para.a >1 para.b ∧ wild(library.a, library.b)

Function >2(a:modref, b:modref) ordering name.a >1 name.b

Function typebase(i:int) mytype
mytype.[
 typedef(1#"$base", 1#"internal", 1#"internallib")
 , typedef(toword.i, 1#"internal", 1#"internallib")
]

Function internalmod(s:seq.word) modref modref(1#"internallib", 1#".", noparameter)

Function seqof(base:mytype) mytype mytype(typerep.typeref."seq seq *" + typerep.base)

Function processof(base:mytype) mytype
mytype(typerep.typeref."process process *" + typerep.base)

type passtypes is
modname:modref
, defines:set.mytype
, unresolveduses:seq.seq.word
, unresolvedexports:seq.seq.word
, exports:set.mytype
, uses:set.modref

Function passtypes(modname:modref, defines:set.mytype, exports:set.mytype) passtypes
passtypes(modname, defines, empty:seq.seq.word, empty:seq.seq.word, exports, empty:set.modref)

Function resolvetypes(librarytypes:set.passtypes, t:seq.seq.word, lib:word) set.passtypes
for librarymods = empty:set.modref, p ∈ toseq.librarytypes do librarymods + modname.p
for
 knownmods = librarymods
 , s = librarytypes
 , defines = empty:set.mytype
 , unresolveduses = empty:seq.seq.word
 , unresolvedexports = empty:seq.seq.word
 , mref = internalmod
 , m ∈ t
do
 if isempty.m then
 next(knownmods, s, defines, unresolveduses, unresolvedexports, mref)
 else if 1#m ∈ "Module module" then
  let newmod = modref(lib, 2#m, if n.m > 2 then typeT else noparameter)
  assert n(knownmods + newmod) = n.knownmods + 1 report "Duplicate module name:^(m)",
   if mref = internalmod then
   next(knownmods + newmod, s, empty:set.mytype, empty:seq.seq.word, empty:seq.seq.word, newmod)
   else
    let p2 = resolve(
     s
     , knownmods
     , passtypes(mref, defines, unresolveduses, unresolvedexports, empty:set.mytype, empty:set.modref)
    ),
    next(
     knownmods + newmod
     , s + p2
     , empty:set.mytype
     , empty:seq.seq.word
     , empty:seq.seq.word
     , newmod
    )
 else if 1#m ∈ "use" then
  assert
   for state = 0, w ∈ m << 1
   do if state < 2 then 2 else if state = 2 ∧ w ∈ "." then 1 else 3,
   state = 2
  report "incorrect format in module:^(mref) /br^(m)",
  next(knownmods, s, defines, unresolveduses + m << 1, unresolvedexports, mref)
 else if 1#m ∈ "type" then
  let newdefines =
   defines
    + newtype(
    if
     2#m
      ∈ "process boolean ptr seq encoding word bits byte char packed2 packed3 packed4 packed5 packed6
     encodingpair encodingstate typename index"
    then
    modref(1#"*", name.mref, para.mref)
    else mref
    , 2#m
   )
  assert n.newdefines = n.defines + 1 report "Duplicate type definition in Module:^(m)",
  next(knownmods, s, newdefines, unresolveduses, unresolvedexports, mref)
 else if subseq(m, 1, 3) = "Export type:" then
 next(
  knownmods
  , s
  , defines
  , unresolveduses
  , unresolvedexports + subseq(m, 4, findindex(m, 1#"{") - 1)
  , mref
 )
 else next(knownmods, s, defines, unresolveduses, unresolvedexports, mref)
let p2 = resolve(
 s
 , knownmods
 , passtypes(mref, defines, unresolveduses, unresolvedexports, empty:set.mytype, empty:set.modref)
),
R(s + p2, knownmods, 100000)

function newtype(mref:modref, name:word) mytype
mytype([typedef(name, name.mref, library.mref)] + typerep.para.mref)

function R(s1:set.passtypes, knownmods:set.modref, countin:int) set.passtypes
if countin = 0 then
s1
else
 for cnt = 0, acc = empty:set.passtypes, p ∈ toseq.s1
 do next(cnt + n.unresolvedexports.p + n.unresolveduses.p, acc + resolve(s1, knownmods, p))
 assert countin ≠ cnt report for acc2 = "", p2 ∈ toseq.s1 do acc2 + printunresolved.p2, acc2,
 R(acc, knownmods, cnt)

function printunresolved(p:passtypes) seq.word
for acc = "", t ∈ unresolveduses.p do acc + "use^(t) /br"
for txt = acc, t2 ∈ unresolvedexports.p do txt + "Export type:^(t2)+/br",
if isempty.acc then
""
else "module^(modname.p) contains lines that cannot be resolved:^(txt)"

function resolve(all:set.passtypes, knownmods:set.modref, p:passtypes) passtypes
let dict = formtypedict(all, p)
for exports = exports.p, x = empty:seq.seq.word, t2 ∈ unresolvedexports.p
do
 let b = resolvetype(dict, t2),
 if isempty.b then next(exports, x + t2) else next(exports + 1#b, x)
let p1 = passtypes(modname.p, defines.p, unresolveduses.p, x, exports, uses.p)
for uses = uses.p, x2 = empty:seq.seq.word, t3 ∈ unresolveduses.p
do
 let b = resolveuse(dict, knownmods, t3),
 if isempty.b then next(uses, x2 + t3) else next(uses + 1#b, x2),
passtypes(modname.p, defines.p, x2, unresolvedexports.p1, exports.p1, uses)

Function >1(a:passtypes, b:passtypes) ordering name.modname.a >1 name.modname.b

Function resolvetype(knowntypes:set.mytype, ref:seq.word) seq.mytype
if subseq(ref, 1, 2) = "seq." then
let t = resolvetype(knowntypes, ref << 2), if n.t ≠ 1 then t else [seqof.1#t]
else if ref = "int" then
[typeint]
else if ref = "boolean" then
[typeboolean]
else if ref = "T" then
[typeT]
else if ref = "real" then
[typereal]
else
 for acc = empty:seq.typedef, w ∈ ref
 do if w = 1#"." then acc else acc + typedef(w, 1#"internal", 1#".")
 let x = mytype.acc
 let a1 = findelement2(knowntypes, x),
  if n.a1 = 1 then
  toseq.a1
  else if n.ref = 1 then
  empty:seq.mytype
  else
   let a = findelement2(knowntypes, mytype([typedef(1#ref, 1#"internal", 1#".")] + typerep.typeT)),
    if n.a ≠ 1 then
    empty:seq.mytype
    else if 2#ref = 1#"." then
     let b = resolvetype(knowntypes, ref << 2),
     if isempty.b then b else [mytype([1#typerep.1#toseq.a] + typerep.1#b)]
    else empty:seq.mytype

function resolveuse(
 knowntypes:set.mytype
 , knownmodules:set.modref
 , ref:seq.word
) seq.modref
let a = findelement2(knownmodules, modref(1#"?", 1#ref, noparameter)),
if n.a ≠ 1 then
empty:seq.modref
else if n.ref = 1 then
toseq.a
else
 let b = resolvetype(knowntypes, ref << 2),
 if isempty.b then empty:seq.modref else [modref(library.1#a, name.1#a, 1#b)]

Function findpasstypes(all:set.passtypes, lib:word, m:seq.word) set.passtypes
let newmod = modref(lib, 2#m, if n.m > 2 then typeT else noparameter),
lookup(
 all
 , passtypes(
  newmod
  , empty:set.mytype
  , empty:seq.seq.word
  , empty:seq.seq.word
  , empty:set.mytype
  , empty:set.modref
 )
)

Function formtypedict(all:set.passtypes, this:passtypes) set.mytype
for r = exports.this, u ∈ toseq.uses.this
do
 let a = lookup(
  all
  , passtypes(
   u
   , empty:set.mytype
   , empty:seq.seq.word
   , empty:seq.seq.word
   , empty:set.mytype
   , empty:set.modref
  )
 ),
 if isempty.a then r else r ∪ exports.1#a,
r ∪ defines.this 