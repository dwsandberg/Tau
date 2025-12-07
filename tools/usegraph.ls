Module usegraph

use UTF8

use bits

use seq.byte

use seq.char

use file

use arc.modref

use graph.arc.modref

use seq.arc.modref

use set.arc.modref

use seq1.seq.modref

use seq1.modref

use set.modref

use seq1.set.modref

use stack.modref

use mytype

use seq.mytype

use seq1.mytype

use orderModules

use seq1.passsymbols

use set.passsymbols

use standard

use svg

use seq1.symbol

use set.symbol

use symbol1

use textio

use arc.word

use drawGraph.arc.word

use graph.arc.word

use seq.arc.word

use seq1.arc.word

use set.arc.word

use seq1.seq.word

use seq1.word

use set.word

use format1a

Function usegraph(
input:seq.file
, include:seq.word
, exclude:seq.word
, order:seq.word
) seq.byte
{COMMAND PROFILE /strong usegraph graphs /em use relationship between modules in source code. /br
/br
options: /br
/strong exclude lists the modules to ignore in the use clauses. /br
/strong include restricts the modules considered to those listed./br
/strong order finds ordering of modules so for any arc in graph, the tail occurs before the head. <* block • /strong nograph Does not include graph in output. *> /p
Examples:<* block > usegraph /sp+built core.libsrc // //../documentation/Ex1usegraph.html /href Result /a /br
> usegraph /sp+built core.libsrc exclude: seq standard // //../documentation/Ex2usegraph.html /href Result /a /br
> usegraph /sp+built core.libsrc include: UTF8 words standard textio exclude: seq standard // //../documentation/Ex3usegraph.html /href Result /a /br
> usegraph /sp+core UTF8.ls textio words standard encoding xxhash exclude = seq standard *> /p
The last two examples give the same result. The first excludes modules from consideration and the second only includes source files of modules that should be included. }
let words =
 if not.isempty.order then
  let allmodules = topasssymbols.breakparagraph.input
  for used = empty:set.modref, e ∈ allmodules
  do if isAbstract.modname.e then used else used ∪ uses.e + modname.e
  let backarcs = expand(toseq.used, asset.allmodules, true)
  let g0 = newgraph.toseq.backarcs
  let before = reverse.orderNodes(nodes.g0, arcs.g0),
  let check = check(before, toseq.arcs.g0),
  (if isempty.check then "Good Ordering" else "FailedOrdering:(check)")
  + {???? allow compound names in include such as encoding.seq.char} "/p ordering::(before)"
  + if "nograph" sub 1 ∈ order then ""
  else
   for wordarcs = empty:seq.arc.word, e ∈ toseq.arcs.g0
   do if head.e = tail.e then wordarcs else wordarcs + arc(merge.%.tail.e, merge.%.head.e),
   drawgraph(wordarcs, asset.include, asset.exclude)
 else
  let arcs = usegraph.breakparagraph.input,
  drawgraph(arcs, asset.include, asset.exclude),
toseqbyte(HTMLheader + HTMLformat1.words)

function %(a:set.modref) seq.word %.toseq.a

function check(ord:seq.modref, arcs:seq.arc.modref) seq.word
{verify ordering of modules}
for acc = "", a ∈ arcs
do
 for state = "", grp = empty:seq.modref, m ∈ ord
 do
  if isempty.state ∧ name.m ∈ "(" then next("group", grp)
  else if state = "group" then
   if name.m ∈ ")" then
    if head.a ∈ grp ∧ tail.a ∈ grp then next("foundhead", empty:seq.modref)
    else if tail.a ∈ grp then next("foundtail", empty:seq.modref)
    else if head.a ∈ grp then next("problem", empty:seq.modref)
    else next("", empty:seq.modref)
   else next(state, grp + m)
  else if tail.a = m ∧ isempty.state then next("foundtail", grp)
  else if head.a = m then if state = "foundtail" then next("foundhead", grp) else next("problem", grp)
  else next(state, grp),
 if state = "foundhead" then acc else acc + %.a,
acc

Function usegraph(lib:seq.seq.word) seq.arc.word
for currentmod = "?" sub 1, result = empty:seq.arc.word, p ∈ lib
do
 if isempty.p then next(currentmod, result)
 else if p sub 1 ∈ "module Module" then next(p sub 2, result)
 else if p sub 1 ∈ "use" ∧ n.p > 1 then
  let m = p sub 2,
  next(
   currentmod
   , if currentmod = m ∨ currentmod ∈ "?" then result else result + arc(currentmod, m)
  )
 else next(currentmod, result),
result

function lookuptype(basetype:word, types:set.symbol) seq.mytype
for found = empty:seq.mytype, e ∈ toseq.types
while isempty.found
do if abstracttypename.(nametype.e) sub 1 = basetype then nametype.e else found,
found

function resolvetype(s:seq.word, types:set.symbol) modref
let module = s sub 2,
if n.s < 3 ∨ s sub 3 ∉ "." then moduleref("X" + module)
else
 let basetype = s sub n.s
 let bt =
  if basetype ∈ "T" then typeT
  else if basetype ∈ "int" then typeint
  else if basetype ∈ "real" then typereal
  else
   let found = lookuptype(basetype, types),
   if isempty.found then newtype(internalmod, basetype) else found sub 1,
 if n.s = 4 then moduleref("X" + module, bt)
 else
  for newtype = bt, left = s << 3 >> 1
  while not.isempty.left
  do
   let e = left sub n.left,
   if e ∈ "." then next(newtype, left >> 1)
   else if e ∈ "seq" then next(seqof.newtype, left >> 1)
   else
    let found = lookuptype(e, types)
    let abstracttype =
     if isempty.found then typeref.[e, "unknown" sub 1, "X" sub 1] else found sub 1,
    next(addabstract(abstracttype, newtype), left >> 1)
  assert isempty.left report "XX:(s)",
  moduleref("X" + module, newtype)

function %(a:arc.modref) seq.word "{:(tail.a),:(head.a)}"

function topasssymbols(mods:seq.seq.word) seq.passsymbols
for
 allmodules = empty:seq.passsymbols
 , alltypes = empty:set.symbol
 , getuses ∈ [false, true]
do
 for
  result1 = empty:seq.passsymbols
  , thisModule = internalmod
  , types = empty:set.symbol
  , uses = empty:set.modref
  , p ∈ mods + "Module ?"
 do
  if p sub 1 ∈ "Module module" then
   let newmodule = passsymbols(thisModule, uses, types),
   next(result1 + newmodule, resolvetype(p, alltypes), empty:set.symbol, empty:set.modref)
  else if p sub 1 ∈ "type" then
   let sym = deepcopySym.newtype(thisModule, p sub 2),
   next(result1, thisModule, asset.[sym] ∪ types, uses)
  else if getuses ∧ p sub 1 ∈ "use" then next(result1, thisModule, types, uses + resolvetype(p, alltypes))
  else next(result1, thisModule, types, uses)
 for alltypes1 = empty:set.symbol, m ∈ result1 do alltypes1 ∪ defines.m,
 next(result1, alltypes1),
allmodules 