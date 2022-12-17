Module pass2

use bits

use seq.int

use otherseq.mytype

use seq.mytype

use standard

use symbol

use otherseq.symbol

use stack.seq.symbol

use symbol2

use symbolconstant

Export type:expandresult

Export code(expandresult) seq.symbol

Export flags(expandresult) bits

Export nextvar(expandresult) int

Export expandresult(int, seq.symbol, bits) expandresult

Function reorgwhen int 6000

Function isverysimple(nopara:int, code:seq.symbol) boolean
if code = [Local.1] ∧ nopara = 1 then
 true
else
 for isverysimple = length.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do
  next(
   if idx ≤ nopara then
    sym = Local.idx
   else
    not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
   , idx + 1)
 /for (isverysimple)

Function Callself bits bits.1

Function State bits bits.4

Function Hasfor bits bits.8

Function Hasmerge bits bits.16

Function ∈(a:bits, b:bits) boolean (a ∧ b) = a

Function ismember(s:symbol) boolean
name.module.s = "seq"_1 ∧ name.s = "∈"_1
∧ (paratypes.s)_1 ∈ [typeint, typeword]

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol) seq.symbol
subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

type expandresult is nextvar:int, code:seq.symbol, flags:bits

function isconstorlocal(p:seq.symbol) boolean
length.p = 1 ∧ (isconst.first.p ∨ islocal.first.p)

Function expandIndex(code:seq.symbol, nextvarin:int) seq.symbol
for acc = empty:seq.symbol, nextvar = nextvarin, last = Lit.1, sym ∈ code do
 if not.isInternal.sym then
  next(acc + sym, nextvar, sym)
 else if wordname.sym ∈ "indexseq45 idxNB" then
  let theseqtype = (paratypes.sym)_1
  let seqtype = Local.nextvar
  let newcode = 
   if isconstorlocal.[acc_(length.acc - 1)] ∧ isconstorlocal.[last.acc] then
    let index = last.acc
    let theseq = acc_(length.acc - 1)
    acc >> 2 + indexseqcode(seqtype, theseq, index, theseqtype, wordname.sym ∈ "indexseq45")
   else
    let t = backparse2(acc, length.acc, 2, empty:seq.int)
    let index0 = subseq(acc, t_2, length.acc)
    let theseq0 = subseq(acc, t_1, t_2 - 1)
    let theseq = if isconstorlocal.theseq0 then first.theseq0 else Local(nextvar + 1)
    let index = if isconstorlocal.index0 then first.index0 else Local(nextvar + 2)
    subseq(acc, 1, t_1 - 1)
    + if isconstorlocal.theseq0 then empty:seq.symbol else theseq0 + Define.value.theseq /if
    + if isconstorlocal.index0 then empty:seq.symbol else index0 + Define.value.index /if
    + indexseqcode(seqtype, theseq, index, theseqtype, wordname.sym ∈ "indexseq45")
  next(newcode, nextvar + 3, sym)
 else
  next(if name.sym ∈ "checkfornoop" then acc else acc + sym, nextvar, sym)
/for (acc)

Function forexpisnoop(sym:symbol, acc:seq.symbol) seq.symbol
let len = length.acc
assert acc_(len - 1) = continue.2 ∧ nopara.acc_(len - 3) = 2 ∧ len ≥ 24
report "SDF $(len) $(sym) $(acc)"
let loop = acc_(len - 21)
if not(isloopblock.loop ∧ isSequence.acc_(len - 4)) then
 empty:seq.symbol
else
 let masteridx = acc_(len - 2)
 let cat = acc_(len - 3)
 let pcat = paratypes.cat
 assert parameter.pcat_1 ≠ pcat_2 report "XXX"
 {assert name.sym /nin" type" /or %.resulttype.sym /in [" seq.word"," seq.mytype"," seq.symbol
  "] report" CHECK"+%.sym+%.acc}
 let element = acc_(len - 5)
 let theacc = acc_(len - 6)
 let theseq = acc_(len - 10)
 if islocal.element ∧ value.element = value.masteridx + 1 ∧ firstvar.loop = value.theacc then
  let empty = if isrecordconstant.theseq then acc_(len - 23) else acc_(len - 26)
  let isempty = 
   isrecordconstant.empty ∧ isSequence.first.fullconstantcode.empty
   ∧ nopara.first.fullconstantcode.empty = 0
  {assert name.sym /in" tointseq towordseq toalphaseq % function hash breakcommas typerecords constantrecords
   AGGREGATE buildargs alphasort findelement2 profilecall tocharseq inrec asseqseqmytype" report" as"
   +%.sym+%.acc}
  {assert name.sym ∉" testr" report" kkk"+%.acc}
  let seqlen = 
   if isrecordconstant.theseq then
    Lit.nopara.last.fullconstantcode.theseq
   else
    Local(firstvar.loop - 1)
  let a = symbol(internalmod, "idxNB", paratypes.loop, parameter.first.paratypes.loop)
  let shouldbe = 
   [Local(firstvar.loop + 1)
    , seqlen
    , EqOp
    , Br2(1, 2)
    , theacc
    , Exit
    , Local(firstvar.loop + 1)
    , Lit.1
    , PlusOp
    , Define.value.masteridx
    , theseq
    , masteridx
    , a]
   + Define.value.element
   + theacc
   + element
  assert subseq(acc, len - 20, len - 5) = shouldbe
  report "$(theseq) shouldbe $(sym) $(acc) /p $(shouldbe)"
  if isrecordconstant.theseq ∧ isempty then
   subseq(acc, 1, len - 24) + theseq
  else if islocal.theseq ∧ isempty then
   subseq(acc, 1, len - 27) + theseq
  else
   let theseqtype = first.paratypes.loop
   if %.parameter.theseqtype ∈ ["packed2", "ptr"] then
    {???? hack! should at least check to see if cat is defined.} empty:seq.symbol
   else
    subseq(acc, 1, len - 1 - 24)
    + symbol(moduleref("* seq", parameter.theseqtype), "+", theseqtype, theseqtype, theseqtype)
 else
  empty:seq.symbol

function indexseqcode(seqtype:symbol
 , theseq:symbol
 , masteridx:symbol
 , xtheseqtype:mytype
 , boundscheck:boolean) seq.symbol
{seqtype will be a basetype}
let seqparameter = parameter.xtheseqtype
let theseqtype = seqof.seqparameter
let elementtype = 
 if seqparameter ∈ [typeint, typereal, typeboolean, typebyte] then seqparameter else typeptr
let maybepacked = seqparameter ∈ packedtypes ∨ seqparameter = typebyte
let callidx = symbol(internalmod, "callidx", [seqof.elementtype, typeint], elementtype)
[theseq
 , GetSeqType
 , Define.value.seqtype
 , Start.elementtype
 , seqtype
 , Lit.1
 , GtOp
 , Br2(1, 2)]
+ [theseq, masteridx, callidx, Exit]
+ if boundscheck then
 [masteridx
  , Lit.0
  , GtOp
  , Br2(1, 2)
  , masteridx
  , theseq
  , GetSeqLength
  , GtOp
  , Br2(1, 2)
  , outofboundssymbol
  , abortsymbol.elementtype
  , Exit]
else
 empty:seq.symbol
/if
+ if maybepacked then
 [seqtype, Lit.1, EqOp, Br2(1, 2)]
 + [theseq
  , masteridx
  , symbol(internalmod, "packedindex", theseqtype, typeint, elementtype)
  , Exit]
else
 empty:seq.symbol
/if
+ [theseq
 , masteridx
 , symbol(internalmod, "idxseq", seqof.elementtype, typeint, elementtype)
 , Exit
 , EndBlock]

function exitlocations(s:seq.symbol, i:int, result:seq.int) seq.int
let sym = s_i
if isstart.sym then
 [i] + result
else if isblock.sym then
 exitlocations(s, matchblock(s, i - 1, 0) - 1, result)
else
 exitlocations(s, i - 1, if isExit.sym then [i] + result else result)

function matchblock(s:seq.symbol, i:int, nest:int) int
let sym = s_i
if isblock.sym then
 matchblock(s, i - 1, nest + 1)
else if isstartorloop.sym then
 if nest = 0 then
  if isloopblock.sym then
   backparse2(s, i - 1, nopara.sym, empty:seq.int)_1
  else
   addDefine(s, i)
 else
  matchblock(s, i - 1, nest - 1)
else
 matchblock(s, i - 1, nest)

function addDefine(s:seq.symbol, i:int) int
if i > 1 ∧ isdefine.s_(i - 1) then
 addDefine(s, backparse2(s, i - 2, 1, empty:seq.int)_1)
else
 i

Function backparse2(s:seq.symbol, i:int, no:int, result:seq.int) seq.int
if no = 0 then
 result
else
 assert i > 0 report "back parse 1a:" + toword.no + %.s + stacktrace
 if isdefine.s_i then
  let args = backparse2(s, i - 1, 1, empty:seq.int)
  backparse2(s, args_1, no, result)
 else if isblock.s_i then
  let b = matchblock(s, i - 1, 0)
  if b = 1 then [b] + result else backparse2(s, b - 1, no - 1, [b] + result)
 else
  let nopara = nopara.s_i
  let first = 
   if nopara = 0 then
    i
   else
    let args = backparse2(s, i - 1, nopara, empty:seq.int)
    assert length.args = nopara
    report
     "back parse 3 $(s_i)" + toword.nopara + "//"
     + for acc = "", @e ∈ args do acc + toword.@e /for (acc)
    args_1
  let b = 
   if first > 1 ∧ isdefine.s_(first - 1) then
    let c = backparse2(s, first - 2, 1, empty:seq.int)
    c_1
   else
    first
  backparse2(s, b - 1, no - 1, [b] + result) 