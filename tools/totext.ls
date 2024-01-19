Module totext

use UTF8

use backparse

use file

use otherseq.int

use seq.int

use seq.seq.int

use otherseq.mytype

use seq.mytype

use otherseq.paravalues

use otherseq.patternType

use standard

use symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use symbol2

use seq.symdef

use set.symdef

use word

use otherseq.word

use seq.word

use otherseq.seq.word

use seq.seq.word

use stack.seq.word

Export type:patternType

type paravalues is parano:int, value:seq.symbol

function >1(a:paravalues, b:paravalues) ordering parano.a >1 parano.b

function %(p:paravalues) seq.word "::^(parano.p)^(value.p)"

Function changes(m:midpoint, patterns:seq.patternType) seq.symdef
for psyms = empty:set.symbol, pat ∈ patterns
do psyms + psym.pat
for acc4 = empty:seq.symdef, e ∈ toseq.prg.m
do
 if paragraphno.e = 0 ∨ sym.e ∈ psyms then acc4
 else
  for newcode = empty:seq.symbol, pat ∈ patterns
  do
   let tmp = replace2(if isempty.newcode then code.e else newcode, pattern.pat, replacement.pat, nopara.pat),
   if isempty.tmp then newcode else tmp,
  if isempty.newcode then acc4
  else acc4 + symdef4(sym.e, newcode, paragraphno.e, getOptionsBits.e),
acc4

Function getpatterns(m:midpoint, patternmods:seq.word) seq.patternType
if isempty.patternmods then empty:seq.patternType
else
 for acc = empty:seq.symbol, md ∈ libmods.m
 do if name.modname.md ∈ patternmods then acc + exports.md else acc
 for patterns = empty:seq.patternType, psym ∈ acc
 do
  let code = getCode(prg.m, psym),
  if isempty.code ∨ not.isSequence.1^code ∨ nopara.1^code ≠ 2 then patterns
  else
   let para2 = backparse3(code, n.code - 1, true)
   let para1 = backparse3(code, para2 - 1, true),
   setinsert(
    patterns
    , patternType(psym, nopara.psym, subseq(code, para1, para2 - 1), subseq(code, para2, n.code - 1))
   ),
 patterns

type patternType is psym:symbol, nopara:int, pattern:seq.symbol, replacement:seq.symbol

function name(p:patternType) word name.psym.p

Function >1(a:patternType, b:patternType) ordering alphaword.name.a >1 alphaword.name.b

Function %(p:patternType) seq.word %.name.p

Function replace(
code:seq.symbol
, pattern:seq.symbol
, replacement:seq.symbol
, nopara:int
) seq.symbol
let tmp = replace2(code, pattern, replacement, nopara),
if isempty.tmp then code else tmp

function eq2(p:mytype, a:mytype) boolean
abstracttypename.p = 1#"*"
∨ p = a
∨ abstracttype.p = abstracttype.a ∧ eq2(parameter.p, parameter.a)

function sametypes(p:symbol, a:symbol) boolean
let tomatch = types.p
for same = true, idx = 1, atype ∈ types.a
while same
do
 let ptype = idx#tomatch,
 next(eq2(ptype, atype), idx + 1),
same

Function replace2(
code:seq.symbol
, pattern:seq.symbol
, replacement:seq.symbol
, nopara:int
) seq.symbol
if n.code < n.pattern then empty:seq.symbol
else
 for A = empty:seq.int, skip = 0, patternidx = n.pattern, place = n.code, sym ∈ reverse.code
 while patternidx > 0
 do
  if skip > 0 then next(A, skip - 1, patternidx, place - 1)
  else
   let p = patternidx#pattern,
   if islocal.p ∧ value.p ≤ nopara then
    let z = backparse3(code, place, nopara - n.A = 1),
    next(A + [value.p, z, place], place - z, patternidx - 1, place - 1)
   else if name.module.p = name.module.sym ∧ name.p = name.sym ∧ nopara.p = nopara.sym ∧ sametypes(p, sym) then next(if patternidx = n.pattern then [place] else A, skip, patternidx - 1, place - 1)
   else next(empty:seq.int, 0, n.pattern, place - 1),
 if isempty.A ∨ patternidx ≠ 0 then empty:seq.symbol
 else
  for acc = empty:seq.paravalues, i ∈ arithseq(n.A / 3, 3, 2)
  do
   setinsert(
    acc
    , paravalues(i#A, replace(subseq(code, (i + 1)#A, (i + 2)#A), pattern, replacement, nopara))
   )
  for new = empty:seq.symbol, sym ∈ replacement
  do if islocal.sym then new + value.(value.sym)#acc else new + sym,
  replace(code >> (n.code - place + skip), pattern, replacement, nopara)
   + new
   + code << 1#A

function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Export backparse3(s:seq.symbol, i:int, includeDefine:boolean) int 