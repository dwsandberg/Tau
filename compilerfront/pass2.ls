Module pass2

use backparse

use bits

use seq.mytype

use standard

use symbol

use seq.symbol

use symbol2

use encoding.track

use otherseq.track

use otherseq.track2

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
 for isverysimple = n.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do next(
  if idx ≤ nopara then
  sym = Local.idx
  else not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
  , idx + 1
 ),
 isverysimple

Function Callself bits bits.1

Function State bits bits.4

Function HasidxNB bits bits.8

Function ∈(a:bits, b:bits) boolean (a ∧ b) = a

Function ismember(s:symbol) boolean
name.module.s = 1_"seq" ∧ name.s = 1_"∈" ∧ 1_paratypes.s ∈ [typeint, typeword]

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol) seq.symbol
subseq(s, 1, start - 1) + value + subseq(s, start + length, n.s)

type expandresult is nextvar:int, code:seq.symbol, flags:bits

function isconstorlocal(p:symbol) boolean isconst.p ∨ islocal.p

Function expandIndex(code:seq.symbol, nextvarin:int, typedict:typedict) expandresult
{Expands idxNB}
for acc = empty:seq.symbol, nextvar = nextvarin, last = Lit.1, sym ∈ code
do
 if not.isInternal.sym then
 next(acc + sym, nextvar, sym)
 else if wordname.sym ∈ "idxNB" then
  let acc1 =
   if isconstorlocal.1^acc then
    if isconstorlocal.2^acc then
    {Neither argument is expression} acc
    else {first argument is expression} acc >> 1 + Define.nextvar + Local.nextvar + 1^acc
   else
    let para2 = backparse3(acc, n.acc, true),
     if isconstorlocal.(para2 - 1)_acc then
      {second argument is expression} subseq(acc, 1, para2 - 2)
      + subseq(acc, para2, n.acc)
      + Define(nextvar + 1)
      + (para2 - 1)_acc
      + Local(nextvar + 1)
     else
      {both arguments are expressions} subseq(acc, 1, para2 - 1)
      + Define(nextvar + 2)
      + subseq(acc, para2, n.acc)
      + Define(nextvar + 1)
      + Local(nextvar + 2)
      + Local(nextvar + 1)
  let index = 1^acc1
  let theseq = 2^acc1
  let theseqtype = basetype(1_paratypes.sym, typedict)
  let seqtype = Local.nextvar
  let newcode = acc1 >> 2 + indexseqcode(seqtype, theseq, index, theseqtype),
  next(newcode, nextvar + 3, sym)
 else next(acc + sym, nextvar, sym),
expandresult(nextvar, acc, 0x0)

function isemptysymbol(empty:symbol) boolean
empty = Words.""
 ∨ 
 isrecordconstant.empty
 ∧ isSequence.1_fullconstantcode.empty
 ∧ nopara.1_fullconstantcode.empty = 0

Function checkemptycat(sym:symbol, result:seq.symbol) seq.symbol
{???? generalize to detect any empty cat--not just words}
if name.module.sym ∈ "seq" ∧ name.sym ∈ "+" ∧ nopara.sym = 2 then
 let p = paratypes.sym,
  if 1_p = 2_p then
   if parameter.1_p ∈ [typeword, typeint, typechar] then
    if isemptysymbol.1^result then
    result >> 1
    else
     let para2 = backparse3(result, n.result, true),
      if isemptysymbol.(para2 - 1)_result then
      subseq(result, 1, para2 - 2) + subseq(result, para2, n.result)
      else empty:seq.symbol
   else empty:seq.symbol
  else empty:seq.symbol
else empty:seq.symbol

function indexseqcode(
 seqtype:symbol
 , theseq:symbol
 , idx:symbol
 , theseqtype:mytype
) seq.symbol
{seqtype will be a basetype}
let seqparameter = parameter.theseqtype
let elementtype = if seqparameter ∈ [typeint, typereal, typeboolean, typebyte] then seqparameter else typeptr
let maybepacked = seqparameter ∈ packedtypes ∨ seqparameter = typebyte
let callidx = symbol(internalmod, "callidx", [seqof.elementtype, typeint], elementtype)
let idxseq = symbol(internalmod, "idxseq", seqof.elementtype, typeint, elementtype),
[theseq, GetSeqType, Define.value.seqtype, Start.elementtype, seqtype, Lit.1, GtOp, Br2(1, 2)]
 + [theseq, idx, callidx, Exit]
 + 
 if maybepacked then
  [seqtype, Lit.1, EqOp, Br2(2, 1)]
  + [theseq, idx, idxseq, Exit]
  + [
   theseq
   , idx
   , symbol(internalmod, "packedindex", theseqtype, typeint, elementtype)
   , Exit
   , EndBlock
  ]
 else [theseq, idx, idxseq, Exit, EndBlock]

type track is key:int, sym:symbol

type track2 is count:int, sym:symbol

Function track(s:symbol) encoding.track encode.track(n.encodingdata:track + 1, s)

function hash(t:track) int key.t

function =(a:track, b:track) boolean key.a = key.b

function >1(a:track, b:track) ordering sym.a >1 sym.b ∧ key.a >1 key.b

function >1(a:track2, b:track2) ordering count.a >1 count.b

function %(t:track2) seq.word %.count.t + %.sym.t

Function trackresults seq.word
for acc = empty:seq.track2, count = 0, last = Lit.0, t ∈ sort.encodingdata:track
do
 if last = sym.t then
 next(acc, count + 1, sym.t)
 else next(setinsert(acc, track2(count, last)), 1, sym.t),
%("/br", setinsert(acc, track2(count, last))) 