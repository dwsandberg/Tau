Module baseTypeCheck

use otherseq.mytype

use stack.mytype

use standard

use seq.symbol

use set.symbol

use symbol2

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
  if aborted.p then
  "/p ERROR:^(sym.s)
   /br^(message.p)
   /br fullcode^(code.s)"
  else result.p
 ,
 next(acc + b, if isempty.b then count else count + 1)
,
if count = 0 then
"Passed Base Type Check"
else "Base Type Check Failed^(count) Times^(acc)"

function addlocals(
 localtypes:set.typemap
 , para:seq.mytype
 , localno:int
 , i:int
) set.typemap
if i > 0 then
addlocals(typemap(localno, i_para) ∪ localtypes, para, localno - 1, i - 1)
else localtypes

function checkkind(s2:symdef, typedict:typedict) seq.word
if isconst.sym.s2 ∨ name.sym.s2 ∈ "type]" ∨ isAbstract.module.sym.s2 then
""
else
 let codeonly = code.s2,
  if n.codeonly = 0 then
  ""
  else
   let localdict =
    for acc = empty:set.typemap, @e ∈ arithseq(nopara.sym.s2, 1, 1)
    do typemap(@e, coretype(@e_paratypes.sym.s2, typedict)) ∪ acc,
    acc
   let returntype = coretype(resulttype.sym.s2, typedict)
   for stk = empty:stack.mytype, localtypes = localdict, skip = false, s ∈ codeonly
   do
    if skip then
    next(stk, localtypes, false)
    else if isdefine.s then
     assert not.isempty.stk report "Ill formed Define"
     let z = typemap(value.s, top.stk) ∪ localtypes,
     next(pop.stk, typemap(value.s, top.stk) ∪ localtypes, false)
    else if iswords.s then
    next(push(stk, typeptr), localtypes, false)
    else if isRealLit.s then
    next(push(stk, typereal), localtypes, false)
    else if isword.s ∨ isIntLit.s ∨ isFref.s then
    next(push(stk, typeint), localtypes, false)
    else if isRecord.s then
     assert n.toseq.stk ≥ nopara.s report "stack underflow record",
     next(push(pop(stk, nopara.s), typeptr), localtypes, false)
    else if isSequence.s then
     assert n.toseq.stk ≥ nopara.s report "stack underflow sequence",
     next(push(pop(stk, nopara.s), typeptr), localtypes, false)
    else if isloopblock.s then
     let no = nopara.s
     let loc = addlocals(localtypes, top(stk, nopara.s), firstvar.s + no - 1, no),
     next(push(pop(stk, nopara.s), coretype(resulttype.s, typedict)), loc, false)
    else if isExit.s then
     assert top.stk = top.pop.stk ∨ top.stk = typeint ∧ top.pop.stk = typebyte
     report "exit type does not match block type^(top.stk)^(top.pop.stk)"
     ,
     next(pop.stk, localtypes, false)
    else if isblock.s then
    next(stk, localtypes, false)
    else if iscontinue.s then
     assert n.toseq.stk ≥ nopara.s report "stack underflow continue",
     next(pop(stk, nopara.s), localtypes, false)
    else if isstart.s then
    next(push(stk, if isseq.resulttype.s then typeptr else resulttype.s), localtypes, false)
    else if isbr.s then
     assert top.stk = typeboolean
     report "if problem^(for a = "", e ∈ top(stk, 1) do a + %.e, a)"
     ,
     next(pop.stk, localtypes, false)
    else if islocal.s then
     let localtype = lookup(localtypes, value.s)
     assert not.isempty.localtype report "local not defined^(s)",
     next(push(stk, value.1_localtype), localtypes, false)
    else if name.s ∈ "packed blockit" ∧ nopara.s = 1 then
    next(stk, localtypes, false)
    else
     let parakinds = for acc = empty:seq.mytype, @e ∈ paratypes.s do acc + coretype(@e, typedict), acc
     assert check5(top(stk, nopara.s), parakinds)
     report "/br symbol type missmatch for^(s)
      /br stktop^(top(stk, nopara.s))
      /br parabasetypes^(parakinds)",
     next(push(pop(stk, nopara.s), coretype(resulttype.s, typedict)), localtypes, false)
   assert n.toseq.stk = 1 report "Expect one element on stack:^(toseq.stk)"
   assert check5([top.stk], [coretype(returntype, typedict)])
   report "Expected return type of^(returntype) but type on stack is^(top.stk)",
   ""

function check5(a:seq.mytype, b:seq.mytype) boolean
for acc = n.a = n.b, idx = 1, t ∈ a
while acc
do
 let t2 = idx_b,
 next(t2 = t ∨ t = typebyte ∧ t2 = typeint ∨ t2 = typebyte ∧ t = typeint, idx + 1)
,
acc

Function checkresults(prg:seq.symdef) seq.word
for defines = asset.knownsym, uses = empty:set.symbol, sd ∈ prg
do next(defines + sym.sd, uses ∪ asset.code.sd)
let undefined = uses \ defines
for
 acc10 = "/p
  /p checkresults
  /p"
 , h ∈ toseq.undefined
do
 if
  isAbstract.module.h
  ∨ 
   name.module.h
   ∈ "$int $define $local $sequence $FOR $words $loopblock $continue $br $global $word $real"
  ∨ isunbound.h
  ∨ isRecord.h
  ∨ isFref.h ∧ basesym.h ∈ defines
  ∨ isBuiltin.h ∧ wordname.h ∈ "createthreadZ" ∧ paratypes.h = [typeptr]
 then
 acc10
 else acc10 + %.h + "/br"
,
"CheckResult:^(
  if isempty.acc10 then
  "OK"
  else
   acc10
   + "/p end checkresults
    /p")"

function knownsym seq.symbol
let typecstr = typeref."cstr fileio."
let typeindex = typeref."index index.",
[
 Litfalse
 , Littrue
 , PlusOp
 , NotOp
 , symbol(internalmod, "basewords", typeint)
 , symbol(internalmod, "assert", seqof.typeword, typeint)
 , symbol(internalmod, "addencoding5", typeptr, typeptr, typeint, typeint)
 , symbol(internalmod, "clock", typeint)
 , symbol(internalmod, "spacecount", typeint)
 , symbol(internalmod, "bitcast", typeint, typeptr)
 , symbol(internalmod, "bitcast", typeptr, typeint)
 , symbol(internalmod, "callstack", typeint, seqof.typeint)
 , symbol(internalmod, "outofbounds", seqof.typeword)
 , symbol(internalmod, "getbytefile2", seqof.typebyte, typeint)
 , symbol(internalmod, "createfile3", seqof.seqof.typebyte, seqof.typebyte, typeint)
 , symbol(internalmod, "sqrt", typereal, typereal)
 , symbol(internalmod, "randomfunc", typereal)
 , symbol(internalmod, "intpart", typereal, typeint)
 , symbol(internalmod, "representation", typereal, typeint)
 , symbol(internalmod, "sin", typereal, typereal)
 , symbol(internalmod, "cos", typereal, typereal)
 , symbol(internalmod, "tan", typereal, typereal)
 , symbol(internalmod, "arcsin", typereal, typereal)
 , symbol(internalmod, "arccos", typereal, typereal)
 , symbol(internalmod, "toreal", typeint, typereal)
 , symbol(internalmod, "+", typereal, typereal, typereal)
 , symbol(internalmod, "-", typereal, typereal, typereal)
 , symbol(internalmod, "*", typereal, typereal, typereal)
 , symbol(internalmod, "/", typereal, typereal, typereal)
 , symbol(internalmod, "?", typereal, typereal, typeref."ordering standard. ")
 , symbol(internalmod, "?", typeint, typeint, typeref."ordering standard. ")
 , symbol(internalmod, "*", typeint, typeint, typeint)
 , symbol(internalmod, "-", typeint, typeint, typeint)
 , symbol(internalmod, "/", typeint, typeint, typeint)
 , symbol(internalmod, "=", typeint, typeint, typeboolean)
 , symbol(internalmod, ">", typeint, typeint, typeboolean)
 , symbol(internalmod, "=", typeboolean, typeboolean, typeboolean)
 , symbol(internalmod, "⊻", typebits, typebits, typebits)
 , symbol(internalmod, "∧", typebits, typebits, typebits)
 , symbol(internalmod, "∨", typebits, typebits, typebits)
 , symbol(internalmod, "<<", typebits, typeint, typebits)
 , symbol(internalmod, ">>", typebits, typeint, typebits)
 , GetSeqType
 , GetSeqLength
 , symbol(internalmod, "getmachineinfo", typeptr)
 , symbol(internalmod, "processisaborted", typeptr, typeboolean)
 , symbol(internalmod, "randomint", typeint, seqof.typeint)
 , symbol(internalmod, "GEP", seqof.typeptr, typeint, typeptr)
 , symbol(internalmod, "GEP", seqof.typeint, typeint, typeint)
 , symbol(internalmod, "toint", typebyte, typeint)
 , symbol(builtinmod.typereal, "fld", typeptr, typeint, typereal)
 , symbol(builtinmod.typeint, "fld", typeptr, typeint, typeint)
 , symbol(builtinmod.typeptr, "fld", typeptr, typeint, typeptr)
 , symbol(builtinmod.typeboolean, "fld", typeptr, typeint, typeboolean)
 , symbol(internalmod, "idxseq", seqof.typereal, typeint, typereal)
 , symbol(internalmod, "idxseq", seqof.typeint, typeint, typeint)
 , symbol(internalmod, "idxseq", seqof.typeptr, typeint, typeptr)
 , symbol(internalmod, "idxseq", seqof.typeboolean, typeint, typeboolean)
 , symbol(internalmod, "idxseq", seqof.typebyte, typeint, typebyte)
 , symbol(internalmod, "callidx", seqof.typereal, typeint, typereal)
 , symbol(internalmod, "callidx", seqof.typeint, typeint, typeint)
 , symbol(internalmod, "callidx", seqof.typeptr, typeint, typeptr)
 , symbol(internalmod, "callidx", seqof.typeboolean, typeint, typeboolean)
 , symbol(internalmod, "callidx", seqof.typebyte, typeint, typebyte)
 , symbol(internalmod, "packedindex", seqof.typebyte, typeint, typeptr)
 , symbol(internalmod, "packedindex", seqof.typeref."packed2 tausupport.", typeint, typeptr)
 , symbol(internalmod, "packedindex", seqof.typeref."packed3 tausupport.", typeint, typeptr)
 , symbol(internalmod, "packedindex", seqof.typeref."packed4 tausupport.", typeint, typeptr)
 , symbol(internalmod, "packedindex", seqof.typeref."packed5 tausupport.", typeint, typeptr)
 , symbol(internalmod, "packedindex", seqof.typeref."packed6 tausupport.", typeint, typeptr)
 , symbol(internalmod, "set", typeptr, typeint, typeptr)
 , symbol(internalmod, "set", typeptr, typeptr, typeptr)
 , Exit
 , Start.typereal
 , Start.typeint
 , Start.typeboolean
 , Start.typeptr
 , EndBlock
] 