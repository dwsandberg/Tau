Module pass2

use UTF8

use bits

use localmap2

use mergeblocks

use real

use standard

use symbol

use symbolconstant

use words

use seq.char

use otherseq.int

use seq.int

use set.int

use otherseq.mytype

use seq.mytype

use otherseq.symbol

use seq.symbol

use set.symbol

use seq.symdef

use set.symdef

use otherseq.word

use set.word

use otherseq.seq.int

use seq.seq.int

use seq.seq.symbol

use seq.seq.word

use set.seq.word

use seq.seq.seq.symbol

Function reorgwhen int 6000

Function isverysimple(nopara:int, code:seq.symbol)boolean
if code = [Local.1] ∧ nopara = 1 then true
else
 for isverysimple = length.code ≥ nopara, idx = 1, sym ∈ code
 while isverysimple
 do next(if idx ≤ nopara then sym = Local.idx else not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym
 , idx + 1
 )
 /for(isverysimple)

function print(s:seq.int)seq.word for acc = "", @e ∈ s do acc + toword.@e /for(acc)

Function Callself bits bits.1

Function State bits bits.4

Function Hasfor bits bits.8

Function Hasmerge bits bits.16

Function ∈(a:bits, b:bits)boolean(a ∧ b) = a

Function ismember(s:symbol)boolean
name.module.s = "seq"_1 ∧ name.s = "∈"_1 ∧ (paratypes.s)_1 ∈ [typeint, typeword]

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol)seq.symbol
subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

type expandresult is nextvar:int, code:seq.symbol, flags:bits

Export type:expandresult

Export flags(expandresult)bits

Export nextvar(expandresult)int

Export code(expandresult)seq.symbol

Export expandresult(int, seq.symbol, bits)expandresult

function isconstorlocal(p:seq.symbol)boolean length.p = 1 ∧ (isconst.first.p ∨ islocal.first.p)

Function expandforexp(code:seq.symbol, nextvarin:int)seq.symbol
for result = empty:seq.symbol, nextvar = nextvarin, sym ∈ code do
 if isBuiltin.sym ∧ wordname.sym = "forexp"_1 then
  let f = forexpcode(sym, result, nextvar)
  next(code.f, nextvar.f)
 else if isInternal.sym ∧ wordname.sym ∈ "indexseq45"then
  let theseqtype = (paratypes.sym)_1
  let t = backparse2(result, length.result, 2, empty:seq.int)
  let index = subseq(result, t_2, length.code)
  let theseq = subseq(result, t_1, t_2 - 1)
  let theseq2 = if isconstorlocal.theseq then first.theseq else Local(nextvar + 1)
  let newcode = 
   subseq(result, 1, t_1 - 1)
   + if isconstorlocal.theseq then empty:seq.symbol else theseq + Define(nextvar + 1)/if
   + [theseq2, GetSeqType, Define.nextvar]
   + index
   + [Lit.1, PlusOp, Define(nextvar + 2)]
   + indexseqcode(Local.nextvar, theseq2, Local(nextvar + 2), theseqtype, true)
  next(newcode, nextvar + 3)
 else next(result + sym, nextvar)
/for(result)

Function forexpisnoop(forsym:symbol, code:seq.symbol)seq.symbol
if nopara.forsym = 7 ∧ first.paratypes.forsym = resulttype.forsym ∧ code_(-2) = Littrue
∧ isseq.resulttype.last.code
∧ wordname.code_(-3) = "+"_1
∧ name.module.code_(-3) ∈ "seq"
∧ isSequence.code_(-4)
∧ nopara.code_(-4) = 1
∧ last.code = code_(-8)
∧ last.code = code_(-6)
∧ code_(-7) = code_(-5)then
 let t2 = backparse2(code, length.code - 8, 2, empty:seq.int)
 let initacc = subseq(code, t2_1, t2_2 - 1)
 if length.initacc = 1 ∧ isrecordconstant.initacc_1 ∧ constantcode.initacc_1 = [Lit.0, Lit.0]then
  subseq(code, 1, t2_1 - 1) + subseq(code, t2_2, length.code - 8)
 else empty:seq.symbol
else empty:seq.symbol

function indexseqcode(seqtype:symbol, theseq:symbol, masteridx:symbol, xtheseqtype:mytype, boundscheck:boolean)seq.symbol
{seqtype will be a basetype}
let seqparameter = parameter.xtheseqtype
let theseqtype = seqof.seqparameter
let elementtype = 
 if seqparameter ∈ [typeint, typereal, typeboolean, typebyte]then seqparameter
 else if seqparameter ∈ [typebit]then typeint else typeptr
let maybepacked = seqparameter ∈ packedtypes ∨ seqparameter = typebyte ∨ seqparameter = typebit
let callidx = symbol(internalmod, "callidx", [seqof.elementtype, typeint], elementtype)
[Start.elementtype, seqtype, Lit.1, GtOp, Br2(1, 2)] + [theseq, masteridx, callidx, Exit]
+ if boundscheck then
 [masteridx
 , theseq
 , GetSeqLength
 , GtOp
 , Br2(1, 2)
 , outofboundssymbol
 , abortsymbol.elementtype
 , Exit
 ]
else empty:seq.symbol /if
+ if maybepacked then
 [seqtype, Lit.1, EqOp, Br2(1, 2)]
 + [theseq
 , masteridx
 , symbol(internalmod, "packedindex", theseqtype, typeint, elementtype)
 , Exit
 ]
else empty:seq.symbol /if
+ [theseq
, masteridx
, symbol(internalmod, "idxseq", seqof.elementtype, typeint, elementtype)
, Exit
, EndBlock
]

function forexpcode(forsym:symbol, code:seq.symbol, nextvar:int)expandresult
let t = backparse2(code, length.code, 5, empty:seq.int) << 1
let endexp = subseq(code, t_(-1), length.code)
let exitexp = subseq(code, t_(-2), t_(-1) - 1)
let bodyexp = subseq(code, t_(-3), t_(-2) - 1)
let endofsymbols = t_(-3) - 1
let startofsymbols = endofsymbols - (nopara.forsym - 3) / 2 + 1
let syms = subseq(code, startofsymbols, endofsymbols)
let tmp = 
 for acc = empty:seq.symbol, i = 1, s ∈ syms >> 1 do next(acc + Local(nextvar + i - 1), i + 1)/for(acc)
let masteridx = Local(value.last.tmp + 1)
let seqelement = Local(value.masteridx + 1)
let nextvar1 = value.seqelement + 1
let Defineseqelement = Define.value.seqelement
let newsyms = tmp + seqelement
let theseqtype = (paratypes.forsym)_(length.newsyms)
let elementtype = if isseq.(paratypes.forsym)_(-4)then typeptr else(paratypes.forsym)_(-4)
{let theseqtype=seqof.elementtype}
let theseq = Local.nextvar1
let totallength = Local(nextvar1 + 1)
let seqtype = Local(nextvar1 + 2)
let Defineseqtype = Define(nextvar1 + 2)
let firstpart = 
 subseq(code, 1, startofsymbols - 1)
 + [Define.nextvar1
 , theseq
 , GetSeqLength
 , Define(nextvar1 + 1)
 , theseq
 , GetSeqType
 , Defineseqtype
 , Lit.1
 ]
 + Loopblock(subseq(paratypes.forsym, 1, length.syms - 1) + typeint, nextvar, resulttype.forsym)
 + {2 if masteridx > totallength then exit}[masteridx, totallength, GtOp]
 + Br2(2, 1)
 + {3 else let sequenceele=seq_(idx)}indexseqcode(seqtype, theseq, masteridx, theseqtype, false)
 + [Defineseqelement]
 + {3 while condition}replace$for(exitexp, newsyms, syms)
 + Br2(2, 1)
 + {4 exit loop}replace$for(endexp, newsyms, syms)
 + Exit
let bodyexp2 = replace$for(bodyexp, newsyms, syms)
let lastpart = 
 if length.syms = 2 then bodyexp2 + [masteridx, Lit.1, PlusOp, continue.2, EndBlock]
 else if not.iscompound.bodyexp then bodyexp2 >> 1 + [masteridx, Lit.1, PlusOp, continue.length.syms, EndBlock]
 else
  {replace exits in body with a continue or abortsymbol}
  let continue2 = [masteridx, Lit.1, PlusOp, continue.length.syms]
  let assert2 = [abortsymbol.resulttype.forsym, Exit]
  let locs = exitlocations(bodyexp2, length.bodyexp2 - 1, empty:seq.int)
  {first item in locs is start of block and the rest are exits}
  for acc = subseq(bodyexp2, 1, first.locs - 1), last = first.locs + 1, i ∈ locs << 1 do
   next(acc + subseq(bodyexp2, last, i - 2)
   + if inModFor.bodyexp2_(i - 1)then continue2 else assert2
   , i + 1
   )
  /for(acc + subseq(bodyexp2, last, length.bodyexp2 - 1) + EndBlock)
expandresult(nextvar1 + 3, firstpart + lastpart, bits.0)

function iscompound(bodyexp:seq.symbol)boolean
{detects compound accumulator}
let sym = bodyexp_(-3)
isblock.last.bodyexp
∧ (wordname.sym = "next"_1 ∧ nopara.sym > 3 ∧ inModFor.sym
∨ {assert case}abstracttype.resulttype.sym
= addabstract(typeref."$base internal internallib", typeT))

function exitlocations(s:seq.symbol, i:int, result:seq.int)seq.int
let sym = s_i
if isstart.sym then[i] + result
else if isblock.sym then exitlocations(s, matchblock(s, i - 1, 0) - 1, result)
else exitlocations(s, i - 1, if isexit.sym then[i] + result else result)

function replace$for(code:seq.symbol, new:seq.symbol, old:seq.symbol)seq.symbol
for acc = empty:seq.symbol, s ∈ code do
 acc
 + if inModFor.s then
  let i = findindex(s, old)
  if i ≤ length.new then[new_i]
  else{this is for one of two cases 1:a nested for and $for variable is from outer loop 2:the next expresion}[s]
 else[s]
/for(acc)

________________________________

function matchblock(s:seq.symbol, i:int, nest:int)int
let sym = s_i
if isblock.sym then matchblock(s, i - 1, nest + 1)
else if isstartorloop.sym then
 if nest = 0 then
  if isloopblock.sym then backparse2(s, i - 1, nopara.sym, empty:seq.int)_1 else addDefine(s, i)
 else matchblock(s, i - 1, nest - 1)
else matchblock(s, i - 1, nest)

function addDefine(s:seq.symbol, i:int)int
if i > 1 ∧ isdefine.s_(i - 1)then addDefine(s, backparse2(s, i - 2, 1, empty:seq.int)_1)else i

Function backparse2(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
if no = 0 then result
else
 assert i > 0 report"back parse 1a:" + toword.no + print.s  
 if isdefine.s_i then
  let args = backparse2(s, i - 1, 1, empty:seq.int)
  backparse2(s, args_1, no, result)
 else if isblock.s_i then
  let b = matchblock(s, i - 1, 0)
  if b = 1 then[b] + result else backparse2(s, b - 1, no - 1, [b] + result)
 else
  let nopara = nopara.s_i
  let first = 
   if nopara = 0 then i
   else
    let args = backparse2(s, i - 1, nopara, empty:seq.int)
    assert length.args = nopara
    report"back parse 3" + print.[s_i] + toword.nopara + "//"
    + for acc = "", @e ∈ args do acc + toword.@e /for(acc)
    args_1
  let b = 
   if first > 1 ∧ isdefine.s_(first - 1)then
    let c = backparse2(s, first - 2, 1, empty:seq.int)
    c_1
   else first
  backparse2(s, b - 1, no - 1, [b] + result) 