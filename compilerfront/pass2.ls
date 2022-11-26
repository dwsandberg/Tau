Module pass2

use bits

use seq.int

use seq.mytype

use standard

use symbol

use otherseq.symbol

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

Function expandforexp(code:seq.symbol, nextvarin:int) seq.symbol
for acc = empty:seq.symbol, nextvar = nextvarin, last = Lit.1, sym ∈ code do
 if  isExit.sym ∧ module.last = internalmod ∧ name.last ∈ "next" then
  next(acc >> 1 + continue.nopara.last, nextvar, sym)
 else if not.isInternal.sym then
  next(acc + sym, nextvar, sym)
 else if wordname.sym ∈ "indexseq45 idxNB" then
  let theseqtype = (paratypes.sym)_1
  let seqtype = Local.nextvar
  let newcode = 
   if isconstorlocal.[acc_(length.acc - 1)] ∧ isconstorlocal.[last.acc] then
    let index = last.acc
    let theseq = acc_(length.acc - 1)
    acc >> 2
    + indexseqcode(seqtype, theseq, index, theseqtype, wordname.sym ∈ "indexseq45")
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

use stack.seq.symbol

use otherseq.mytype

Function forexpisnoop(sym:symbol, acc:seq.symbol) seq.symbol
if length.acc < 26 then
 empty:seq.symbol
else if acc_(length.acc - 1) ≠ continue.2 then
 empty:seq.symbol
else
 let masteridx = acc_(length.acc - 2)
 let cat = acc_(length.acc - 3)
 let pcat = paratypes.cat
 if length.pcat ≠ 2 then
  empty:seq.symbol
 else
  let adj = if pcat_1 = pcat_2 then length.acc - 1 else length.acc
  if adj < length.acc ∧ not.isSequence.acc_(length.acc - 4)
  ∨ adj = length.acc ∧ parameter.pcat_1 ≠ pcat_2 then
   empty:seq.symbol
  else
   let element = acc_(adj - 4)
   let theacc = acc_(adj - 5)
   let loop = acc_(adj - 20)
   let getseqlength = acc_(adj - 23)
   let theseq = acc_(adj - 24)
   let empty = acc_(adj - 25)
   if islocal.element ∧ value.element = value.masteridx + 1 ∧ islocal.theseq
   ∧ isloopblock.loop
   ∧ getseqlength = GetSeqLength
   ∧ firstvar.loop = value.theacc then
    {assert name.sym /in" tointseq towordseq toalphaseq % function hash breakcommas typerecords constantrecords
     AGGREGATE buildargs alphasort findelement2 profilecall tocharseq inrec asseqseqmytype" report" as"
     +%.sym+%.acc}
    if islocal.theseq ∧ isrecordconstant.empty ∧ isSequence.first.fullconstantcode.empty
    ∧ nopara.first.fullconstantcode.empty = 0 then
     subseq(acc, 1, adj - 26) + theseq
    else
     let theseqtype = first.paratypes.loop
     if %.parameter.theseqtype ∈ ["packed2", "ptr"] then
      {???? hack! should at least check to see if cat is defined.} empty:seq.symbol
     else
      subseq(acc, 1, adj - 24)
      + symbol(moduleref("* seq", parameter.theseqtype)
       , "+"
       , theseqtype
       , theseqtype
       , theseqtype)
   else
    empty:seq.symbol

if length.acc < 9 then empty:seq.symbol else let masteridx = value.acc_(length.acc-4) let cat = acc
_(length.acc-5) let pcat = paratypes.cat if length.pcat /ne 2 then empty:seq.symbol else let adj = if
pcat_1 = pcat_2 then length.acc-1 else length.acc if adj < length.acc ∧ not.isSequence.acc_(length
.acc-6) ∨ adj = length.acc ∧ parameter.pcat_1 ≠ pcat_2 then empty:seq.symbol else let acc6 = acc
_(adj-6) let acc7 = acc_(adj-7) let adj2 = if subseq (acc, adj-11, adj-10) = [Littrue, Br2 (2, 2)] then
adj-12 else adj-10 if adj2-14 < 0 then empty:seq.symbol else let acc9 = acc_(adj-9) let loop
= acc_(adj2-8) let getlength = acc_(adj2-11) let seq = acc_(adj2-12) let empty = acc_(adj2-13
) if islocal.acc7 ∧ islocal.acc6 ∧ value.acc7 = masteridx-1 ∧ value.acc6 = masteridx+1 ∧ value.acc7
= masteridx-1 ∧ isloopblock.loop ∧ getlength = GetSeqLength then if islocal.seq ∧ isrecordconstant
.empty ∧ isSequence.first.fullconstantcode.empty ∧ nopara.first.fullconstantcode.empty = 0 then subseq
(acc, 1, adj2-14)+seq else let theseqtype = first.paratypes.loop if %.parameter.theseqtype ∈ [" packed2
"," ptr"] then {???? hack! should at least check to see if cat is defined.} empty:seq.symbol else
subseq (acc, 1, adj2-12)+symbol (moduleref (" * seq", parameter.theseqtype),"+", theseqtype, theseqtype
, theseqtype) else {assert not (islocal.acc7 ∧ islocal.acc6 ∧ value.acc7 = masteridx-1 ∧ value.acc6 =
masteridx+1 ∧ value.acc7 = masteridx-1) report" X"+%.acc+" /p"+%.subseq (acc, 1, adj2)} empty
:seq.symbol

function indexseqcode(seqtype:symbol, theseq:symbol, masteridx:symbol, xtheseqtype:mytype, boundscheck:boolean) seq.symbol
{seqtype will be a basetype}
let seqparameter = parameter.xtheseqtype
let theseqtype = seqof.seqparameter
let elementtype = 
 if seqparameter ∈ [typeint, typereal, typeboolean, typebyte] then
  seqparameter
 else
  typeptr
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
  if b = 1 then
   [b] + result
  else
   backparse2(s, b - 1, no - 1, [b] + result)
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