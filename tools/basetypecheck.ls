Module baseTypeCheck

use seq1.mytype

use stack.mytype

use standard

use seq.symbol

use set.symbol

use symbol1

use set.typemap

use process.seq.word

function coretype(typ:mytype, alltypes:typedict) mytype
let b = basetype(typ, alltypes),
if isseq.b then typeptr else b

type typemap is key:int, value:mytype

function lookup(a:set.typemap, key:int) set.typemap lookup(a, typemap(key, typeint))

Function >1(a:typemap, b:typemap) ordering key.a >1 key.b

Function baseTypeCheck(prg:seq.symdef, typedict:typedict) seq.word
for acc = empty:seq.word, count = 0, s ∈ prg
do
 let p = process.checkkind(s, typedict)
 let b =
  if aborted.p then "/p ERROR::(sym.s)/br:(message.p)/br fullcode:(code.s)"
  else result.p,
 next(acc + b, if isempty.b then count else count + 1),
if count = 0 then "Passed Base Type Check"
else "Base Type Check Failed:(count)Times:(acc)"

function addlocals(
localtypes:set.typemap
, para:seq.mytype
, localno:int
, i:int
) set.typemap
if i > 0 then addlocals(typemap(localno, para sub i) ∪ localtypes, para, localno - 1, i - 1)
else localtypes

function checkkind(s2:symdef, typedict:typedict) seq.word
if isconst.sym.s2 ∨ name.sym.s2 ∈ "type]" ∨ isAbstract.module.sym.s2 then ""
else
 let codeonly = code.s2,
 if n.codeonly = 0 then ""
 else
  let localdict =
   for acc = empty:set.typemap, @e ∈ arithseq(nopara.sym.s2, 1, 1)
   do typemap(@e, coretype((paratypes.sym.s2) sub @e, typedict)) ∪ acc,
   acc
  let returntype = coretype(resulttype.sym.s2, typedict)
  for stk = empty:stack.mytype, localtypes = localdict, skip = false, s ∈ codeonly
  do
   if skip then next(stk, localtypes, false)
   else
    let kind = kind.s,
    if kind = kdefine then
     assert not.isempty.stk report "Ill formed Define"
     let z = typemap(value.s, top.stk) ∪ localtypes,
     next(pop.stk, typemap(value.s, top.stk) ∪ localtypes, false)
    else if kind = kwords then next(push(stk, typeptr), localtypes, false)
    else if kind = kreal then next(push(stk, typereal), localtypes, false)
    else if kind ∈ [kword, kint, kfref] then next(push(stk, typeint), localtypes, false)
    else if kind = krecord then
     assert n.toseq.stk ≥ nopara.s report "stack underflow record",
     next(push(pop(stk, nopara.s), typeptr), localtypes, false)
    else if kind = ksequence then
     assert n.toseq.stk ≥ nopara.s report "stack underflow sequence",
     next(push(pop(stk, nopara.s), typeptr), localtypes, false)
    else if kind = kloop then
     let no = nopara.s
     let loc = addlocals(localtypes, top(stk, nopara.s), firstvar.s + no - 1, no),
     next(push(pop(stk, nopara.s), coretype(resulttype.s, typedict)), loc, false)
    else if kind = kexit then
     assert top.stk = top.pop.stk ∨ top.stk = typeint ∧ top.pop.stk = typebyte report "exit type does not match block type:(top.stk):(top.pop.stk)",
     next(pop.stk, localtypes, false)
    else if kind = kendblock then next(stk, localtypes, false)
    else if kind = kcontinue then
     assert n.toseq.stk ≥ nopara.s report "stack underflow continue",
     next(pop(stk, nopara.s), localtypes, false)
    else if kind = kstart then next(push(stk, if isseq.resulttype.s then typeptr else resulttype.s), localtypes, false)
    else if kind = kbr then
     assert top.stk = typeboolean report "if problem:(toseq.stk)",
     next(pop.stk, localtypes, false)
    else if kind ∈ [kjmpB, klabel] then next(stk, localtypes, false)
    else if kind = kjmp then
     let noval = (value.s - 3) / 2
     assert top(stk, noval) = constantseq(noval, typeint) report "jmp problem:(toseq.stk)/p:(toseq.stk)",
     next(pop(stk, noval + 1), localtypes, false)
    else if kind = klocal then
     let localtype = lookup(localtypes, value.s)
     assert not.isempty.localtype report "local not defined:(s)",
     next(push(stk, value.localtype sub 1), localtypes, false)
    else if name.s ∈ "packed blockit" ∧ nopara.s = 1 then next(stk, localtypes, false)
    else
     let parakinds =
      for acc = empty:seq.mytype, @e ∈ paratypes.s do acc + coretype(@e, typedict),
      acc
     assert check5(top(stk, nopara.s), parakinds) report "/br symbol type missmatch for:(s)/br stktop:(top(stk, nopara.s))/br parabasetypes:(parakinds)",
     next(push(pop(stk, nopara.s), coretype(resulttype.s, typedict)), localtypes, false)
  assert n.toseq.stk = 1 report "Expect one element on stack::(toseq.stk)",
  assert check5([top.stk], [coretype(returntype, typedict)]) report "Expected return type of:(returntype)but type on stack is:(top.stk)",
  ""

function check5(a:seq.mytype, b:seq.mytype) boolean
for acc = n.a = n.b, idx = 1, t ∈ a
while acc
do
 let t2 = b sub idx,
 next(t2 = t ∨ t = typebyte ∧ t2 = typeint ∨ t2 = typebyte ∧ t = typeint, idx + 1),
acc

Function checkresults(prg:seq.symdef) seq.word
for defines = asset.knownsym, uses = empty:set.symbol, sd ∈ prg
do next(defines + sym.sd, uses ∪ asset.code.sd)
let undefined = uses \ defines
for acc10 = "", h ∈ toseq.undefined
do
 if isAbstract.module.h
 ∨ kind.h
 ∈ [
  kint
  , kdefine
  , klocal
  , ksequence
  , kwords
  , kloop
  , kstart
  , kcontinue
  , kbr
  , kword
  , kreal
  , krecord
  , kglobal
  , kjmp
  , kjmpB
  , klabel
 ]
 ∨ isunbound.h
 ∨ kind.h = kfref ∧ basesym.h ∈ defines
 ∨ kind.h = kcreatethreadZ ∧ paratypes.h = [typeptr] then acc10
 else acc10 + %.h + "/br",
if isempty.acc10 then "Passed CheckResults" else "Failed CheckResult:/p:(acc10)"

function knownsym seq.symbol
[
 Litfalse
 , Littrue
 , PlusOp
 , NotOp
 , symbol(internalmod, "basewords", typeint)
 , symbol(internalmod, "assert", [seqof.typeword], typeint)
 , symbol(internalmod, "addencoding5", [typeptr, typeptr, typeint], typeint)
 , symbol(internalmod, "clock", typeint)
 , symbol(internalmod, "spacecount", typeint)
 , symbol(internalmod, "bitcast", [typeint], typeptr)
 , symbol(internalmod, "bitcast", [typeptr], typeint)
 , symbol(internalmod, "callstack", [typeint], seqof.typeint)
 , symbol(internalmod, "outofbounds", seqof.typeword)
 , symbol(internalmod, "getbytefile2", [seqof.typebyte], typeint)
 , symbol(internalmod, "createfile3", [seqof.seqof.typebyte, seqof.typebyte], typeint)
 , symbol(internalmod, "sqrt", [typereal], typereal)
 , symbol(internalmod, "randomfunc", typereal)
 , symbol(internalmod, "intpart", [typereal], typeint)
 , symbol(internalmod, "representation", [typereal], typeint)
 , symbol(internalmod, "sin", [typereal], typereal)
 , symbol(internalmod, "cos", [typereal], typereal)
 , symbol(internalmod, "tan", [typereal], typereal)
 , symbol(internalmod, "arcsin", [typereal], typereal)
 , symbol(internalmod, "arccos", [typereal], typereal)
 , symbol(internalmod, "toreal", [typeint], typereal)
 , symbol(internalmod, "+", [typereal, typereal], typereal)
 , symbol(internalmod, "-", [typereal, typereal], typereal)
 , symbol(internalmod, "*", [typereal, typereal], typereal)
 , symbol(internalmod, "/", [typereal, typereal], typereal)
 , symbol(internalmod, "?", [typereal, typereal], typeref."ordering standard. ")
 , symbol(internalmod, "?", [typeint, typeint], typeref."ordering standard. ")
 , symbol(internalmod, "*", [typeint, typeint], typeint)
 , symbol(internalmod, "-", [typeint, typeint], typeboolean)
 , symbol(internalmod, "/", [typeint, typeint], typeint)
 , symbol(internalmod, "=", [typeint, typeint], typeboolean)
 , symbol(internalmod, ">", [typeint, typeint], typeboolean)
 , symbol(internalmod, "=", [typeboolean, typeboolean], typeboolean)
 , symbol(internalmod, "⊻", [typebits, typebits], typebits)
 , symbol(internalmod, "∧", [typebits, typebits], typebits)
 , symbol(internalmod, "∨", [typebits, typebits], typebits)
 , symbol(internalmod, "<<", [typebits, typeint], typebits)
 , symbol(internalmod, ">>", [typebits, typeint], typebits)
 , GetSeqType
 , GetSeqLength
 , symbol(internalmod, "getmachineinfo", typeptr)
 , symbol(internalmod, "processisaborted", [typeptr], typeboolean)
 , symbol(internalmod, "randomint", [typeint], seqof.typeint)
 , symbol(internalmod, "GEP", [seqof.typeptr, typeint], typeptr)
 , symbol(internalmod, "GEP", [seqof.typeint, typeint], typeint)
 , symbol(internalmod, "toint", [typebyte], typeint)
 , symbol(builtinmod.typereal, "fld", [typeptr, typeint], typereal)
 , symbol(builtinmod.typeint, "fld", [typeptr, typeint], typeint)
 , symbol(builtinmod.typeptr, "fld", [typeptr, typeint], typeptr)
 , symbol(builtinmod.typeboolean, "fld", [typeptr, typeint], typeboolean)
 , symbol(internalmod, "set", [typeptr, typeint], typeptr)
 , symbol(internalmod, "set", [typeptr, typeptr], typeptr)
 , symIdxNB.typereal
 , symIdxNB.typeint
 , symIdxNB.typeboolean
 , symIdxNB.typeptr
 , symIdxNB.typebyte
 , symIdxNB.typepacked2
 , symIdxNB.typepacked3
 , symIdxNB.typepacked4
 , symIdxNB.typepacked5
 , symIdxNB.typepacked6
 , Exit
 , Start.typereal
 , Start.typeint
 , Start.typeboolean
 , Start.typeptr
 , EndBlock
] 