Module totext

use UTF8

use backparse3

use file

use seq.int

use seq.seq.int

use seq1.int

use seq.mytype

use seq1.mytype

use seq1.paravalues

use seq1.patternType

use standard

use seq.symbol

use seq1.symbol

use set.symbol

use symbol1

use seq.symdef

use set.symdef

use word

use seq.word

use seq.seq.word

use seq1.seq.word

use stack.seq.word

use seq1.word

Export type:patternType

type paravalues is parano:int, value:seq.symbol

function >1(a:paravalues, b:paravalues) ordering parano.a >1 parano.b

function %(p:paravalues) seq.word ":::(parano.p):(value.p)"

function ifempty(a:seq.symbol, replacementValue:seq.symbol) seq.symbol
if isempty.a then replacementValue else a

Function changes(m:midpoint, patterns:seq.patternType) seq.symdef
for psyms = empty:set.symbol, pat ∈ patterns do psyms + psym.pat
for acc4 = empty:seq.symdef, e ∈ toseq.prg.m
do
 if paragraphno.e = 0 ∨ sym.e ∈ psyms then acc4
 else
  for newcode = empty:seq.symbol, pat ∈ patterns
  do ifempty(replace32(if isempty.newcode then code.e else newcode, pat), newcode),
  if isempty.newcode then acc4
  else acc4 + symdef4(sym.e, newcode, paragraphno.e, options.e),
acc4

Function getpatterns(m:midpoint, patternmods:seq.word) seq.patternType
if isempty.patternmods then empty:seq.patternType
else
 for acc = empty:seq.symbol, md ∈ libmods.m
 do if name.modname.md ∈ patternmods then acc + exports.md else acc
 for patterns = empty:seq.patternType, psym ∈ acc
 do
  let code = getCode(prg.m, psym),
  if isempty.code ∨ kind.code sub n.code ≠ ksequence ∨ nopara.code sub n.code ≠ 2 then patterns
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

Function >1(a:patternType, b:patternType) ordering name.a >alpha name.b

Function %(p:patternType) seq.word %.name.p

function eq2(p:mytype, a:mytype) boolean
abstracttypename.p = "*" sub 1
 ∨ p = a
 ∨ abstracttype.p = abstracttype.a ∧ eq2(parameter.p, parameter.a)

function sametypes(p:symbol, a:symbol) boolean
let tomatch = types.p
for same = true, idx = 1, atype ∈ types.a
while same
do
 let ptype = tomatch sub idx,
 next(eq2(ptype, atype), idx + 1),
same

function replace32(code:seq.symbol, pat:patternType) seq.symbol
let pattern = pattern.pat,
if n.code < n.pattern then empty:seq.symbol
else
 let replacement = replacement.pat
 let nopara = nopara.pat,
 for A = empty:seq.int, skip = 0, patternidx = n.pattern, place = n.code, sym ∈ reverse.code
 while patternidx > 0
 do
  if skip > 0 then next(A, skip - 1, patternidx, place - 1)
  else
   let p = pattern sub patternidx,
   if kind.p = klocal ∧ value.p ≤ nopara then
    let z = backparse3(code, place, nopara - n.A = 1),
    next(A + [value.p, z, place], place - z, patternidx - 1, place - 1)
   else if name.module.p = name.module.sym
   ∧ name.p = name.sym
   ∧ nopara.p = nopara.sym
   ∧ sametypes(p, sym) then next(if patternidx = n.pattern then [place] else A, skip, patternidx - 1, place - 1)
   else next(empty:seq.int, 0, n.pattern, place - 1),
 if isempty.A ∨ patternidx ≠ 0 then empty:seq.symbol
 else
  for acc = empty:seq.paravalues, i ∈ arithseq(n.A / 3, 3, 2)
  do
   let code1 = subseq(code, A sub (i + 1), A sub (i + 2)),
   setinsert(acc, paravalues(A sub i, ifempty(replace32(code1, pat), code1)))
  for new = empty:seq.symbol, sym ∈ replacement
  do if kind.sym = klocal then new + value.acc sub value.sym else new + sym,
  let code1 = code >> (n.code - place + skip),
  ifempty(replace32(code1, pat), code1) + new + code << A sub 1

function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Export backparse3(s:seq.symbol, i:int, includeDefine:boolean) int 