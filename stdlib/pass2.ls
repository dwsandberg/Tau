Module pass2

use UTF8

use bits

use interpreter

use mergeblocks

use real

use standard

use symbol

use words

use seq.char

use otherseq.int

use seq.int

use set.int

use otherseq.mytype

use seq.mytype

use seq.symdef

use otherseq.symbol

use seq.symbol

use set.symbol

use otherseq.word

use set.word

use otherseq.seq.int

use seq.seq.int

use seq.seq.symbol


use seq.seq.word

use set.seq.word

use seq.seq.seq.symbol

use localmap2


function firstopt(p:program, s:symbol, code:seq.symbol, options:seq.word, first:boolean)seq.symbol
let pdict = for pmap =  empty:set.localmap2  , parano =   arithseq(nopara.s,1, 1)  do 
       pmap+localmap2(parano,[ Local.parano])
     /for(pmap)
let a = xxx(p, removeoptions.code, s, pdict)
let t = if first then a
else if Hasfor ∈ flags.a ∨ Callself ∈ flags.a then
let ty = if Hasfor ∈ flags.a then expandforexp(code.a, nextvar.a)else code.a
let t2 = if Callself ∈ flags.a ∧ wordname.s ≠ "subpass2"_1 then optB(ty, s)else ty
 expandresult(nextvar.a, t2, flags.a)
else a
let newoptions1 = if length.code.t < 22 ∧ Callself ∉ flags.t ∧ Hasfor ∉ flags.t
∧ "NOINLINE"_1 ∉ options then
 if isverysimple(nopara.s, code.t)then"INLINE VERYSIMPLE"else"INLINE"
else""
let newoptions = if isempty.options then newoptions1
else if options = newoptions1 then options else toseq(asset.options - asset."VERYSIMPLE INLINE" ∪ asset.newoptions1)
if newoptions = ""then code.t else code.t + Words.newoptions + Optionsym

function isverysimple(nopara:int, code:seq.symbol)boolean
 if code = [ Local.1] ∧ nopara = 1 then true
 else
  for isverysimple = length.code ≥ nopara, idx = 1, sym = code while isverysimple do next(if idx ≤ nopara then sym = Local.idx
  else not.isbr.sym ∧ not.isdefine.sym ∧ not.islocal.sym, idx + 1)/for(isverysimple)

function xxx(p:program, code:seq.symbol, s:symbol, pdict:set.localmap2)expandresult
let a = scancode(p, code, nopara.s + 1, pdict, s)
let new = if Hasmerge ∈ flags.a then optB(code.a, Lit.1)else code.a
 if length.code = length.new ∧ length.code > 20 ∨ new = code then
  expandresult(nextvar.a, new, flags.a)
 else xxx(p, new, s, pdict)

function print(s:seq.int)seq.word for acc ="", @e = s do acc + toword.@e /for(acc)

Function Callself bits bits.1

Function State bits bits.4

Function Hasfor bits bits.8

Function Hasmerge bits bits.16

function ∈(a:bits, b:bits)boolean(a ∧ b) = a

function prepareargs(args:seq.symbol,func:symbol) seq.symbol
{returns empty sequence if args are not all constants. Removes record constants in args.
 returns empty if Fref appears in args }
for acc = true, newargs=empty:seq.symbol, @e = args while acc do 
       if not.isconst.@e /or isFref.@e then next(false,newargs)
       else if not.isrecordconstant.@e then next(true,newargs+@e)
       else 
         let t=removeconstantcode.[@e]
         let noFref= for noFref = true, sub = t  while noFref do   not.isFref.sub  /for(noFref) 
           next(noFref,newargs+t)
/for( if acc then args+func else empty:seq.symbol)

function scancode(p:program, org:seq.symbol, nextvarX:int, mapX:set.localmap2, self:symbol)expandresult
 for flags = bits.0, result = empty:seq.symbol, nextvar = nextvarX, map = mapX, sym = org do
 let len = length.result
  if not.isempty.result ∧ last.result = PreFref then
       next(flags,  result >> 1+Fref.sym,nextvar, map)
  else if isconst.sym then next(flags, result + sym, nextvar, map)
  else if isspecial.sym then
   if isdefine.sym then
   let thelocal = value.sym
    if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
     next(flags, subseq(result, 1, length.result - 1), nextvar, 
      localmap2(thelocal, [ result_len]) /cup map)
    else next(flags, result + Define.nextvar, nextvar + 1, 
    localmap2(thelocal, [ Local.nextvar]) /cup map )
   else if isbr.sym then
   let hasnot = last.result = NotOp
   let sym1 = if hasnot then Br2(brf.sym, brt.sym)else sym
   let result1 = if hasnot then result >> 1 else result
   let newsym = if last.result1 = Litfalse then Br2(brf.sym1, brf.sym1)
   else if last.result1 = Littrue then Br2(brt.sym1, brt.sym1)else sym1
    next(if brt.newsym = brf.newsym ∨ isblock.last.result1 then Hasmerge ∨ flags else flags, result1 + newsym, nextvar, map)
   else if sym = Exit ∧ isblock.last.result then next(flags ∨ Hasmerge, result + sym, nextvar, map)
   else if isloopblock.sym then
   let nopara = nopara.sym
   let addlooplocals = for pmap = map, parano = 1, e = constantseq(10000, 1)while parano ≤ nopara do 
   next(localmap2(firstvar.sym + parano - 1, [ Local(nextvar + parano - 1)]) /cup pmap, parano + 1)
   /for(pmap)
   next(flags, result + Loopblock(paratypes.sym, nextvar, resulttype.sym), nextvar + nopara, addlooplocals)
   else if isRecord.sym ∨ isSequence.sym then
   let nopara = nopara.sym
   let args = subseq(result, len + 1 - nopara, len)
   let constargs = for acc = true, @e = args while acc do isconst.@e /for(acc)
   if constargs then next(flags, subseq(result, 1, len - nopara) + Constant2(args + sym), nextvar, map)
    else next(flags, result + sym, nextvar, map)
   else if islocal.sym then
   let t = lookup( value.sym,map)
   next(flags, result + if isempty.t then [ sym]else value.t_1, nextvar, map)
   else next(flags, result + sym, nextvar, map)
  else if sym = NotOp ∧ last.result = NotOp then next(flags, result >> 1, nextvar, map)
  else if length.result > 2 ∧ isconst.last.result
  ∧ (sym = symbol(moduleref("stdlib seq", typeint),"∈", [ typeint, seqof.typeint], typeboolean)
  ∨ sym = symbol(moduleref("stdlib seq", typeword),"∈", [ typeword, seqof.typeword], typeboolean))then
  let arg = result_(-2)
  if islocal.arg ∨ isconst.arg then
    next(flags, result >> 2 + removeismember(last.result, arg), nextvar, map)
   else next(flags, result >> 1 + Define.nextvar + removeismember(last.result, Local.nextvar), nextvar, map)
  else if wordname.sym ∈ "forexp" ∧  isBuiltin.sym then
  let noop = forexpisnoop(sym, result)
  if not.isempty.noop then next(flags, noop, nextvar, map)else next(flags ∨ Hasfor, result + sym, nextvar, map)
  else if wordname.sym ∈ "indexseq45" ∧ isInternal.sym  then
   next(flags ∨ Hasfor, result + sym, nextvar, map)
  else if sym = self then next(flags ∨ Callself, result + sym, nextvar, map)
  else
   let nopara = nopara.sym
   let dd = getCode(p, sym)
   let options = getoption.dd
    let ct=if first."COMPILETIME" ∈ options then prepareargs(subseq(result, len - nopara + 1, len),sym)
       else empty:seq.symbol
    if {COMPILE TIME} not.isempty.ct then
     if sym = symbol(moduleref."stdlib words","decodeword", typeword, typeint)then
     let arg1 = result_len
     let a1 = for acc = empty:seq.symbol, @e = tointseq.decodeword.wordname.arg1 do acc + Lit.@e /for(acc)
     let d = Constant2(a1 + Sequence(typeint, length.a1))
     next(flags, result >> 1 + d, nextvar, map)
     else 
      let newcode = interpretCompileTime.ct
      let newconst = if length.newcode > 1 then Constant2.newcode else first.newcode
       next(flags, result >> nopara + newconst, nextvar, map)
    else if first."VERYSIMPLE" ∈ options then next(flags, result + removeoptions.dd << nopara.sym, nextvar, map)
    else if"INLINE"_1 ∉ options then
    let newflags = if"STATE"_1 ∈ options ∨ { wordname.sym ∈"setfld"∨ }isGlobal.sym then
     State ∨ flags
    else flags
     next(newflags, result + sym, nextvar, map)
    else
     let code = removeoptions.dd
      if isempty.code then next(flags, result + sym, nextvar, map)
      else if length.code = 1 ∧ code = [ Local.1] ∧ nopara = 1 then
       { function just returns result }next(flags, result, nextvar, map)
      else
       let t = backparse2(result, len, nopara, empty:seq.int) + [ len + 1]
       { assert length.t = nopara + 1 report"INLINE PARA PROBLEM"}
        let new = expandinline(result, t, nextvar, code, p, self)
        next(flags ∨ flags.new, subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map)
 /for(expandresult(nextvar, result, flags))

function expandinline(result:seq.symbol, t:seq.int, nextvarin:int, code:seq.symbol, p:program, self:symbol)expandresult
 for pmap = empty:set.localmap2, paracode = empty:seq.symbol, nextvar = nextvarin, parano = 1, lastidx = t_1, idx = t << 1 do
  next(pmap+localmap2( parano, [ Local.nextvar]) , paracode + subseq(result, lastidx, idx - 1) + Define.nextvar, nextvar + 1, parano + 1, idx)
 /for(let r = scancode(p, code, nextvar, pmap, self)
 expandresult(nextvar.r, paracode + code.r, flags.r))

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol)seq.symbol
 subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

type expandresult is nextvar:int, code:seq.symbol, flags:bits

function isconstorlocal(p:seq.symbol)boolean length.p = 1 ∧ (isconst.first.p ∨ islocal.first.p)

function expandforexp(code:seq.symbol, nextvarin:int)seq.symbol
 for result = empty:seq.symbol, nextvar = nextvarin, sym = code do
  if  isBuiltin.sym  ∧ wordname.sym = "forexp"_1 then
  let f = forexpcode(sym, result, nextvar)
  next(code.f, nextvar.f)
  else if  isInternal.sym ∧ wordname.sym ∈ "indexseq45"then
  let theseqtype =(paratypes.sym)_1
  let t = backparse2(result, length.result, 2, empty:seq.int)
  let index = subseq(result, t_2, length.code)
  let theseq = subseq(result, t_1, t_2 - 1)
  let theseq2 = if isconstorlocal.theseq then first.theseq else Local(nextvar + 1)
  let newcode = subseq(result, 1, t_1 - 1)
  + if isconstorlocal.theseq then empty:seq.symbol else theseq + Define(nextvar + 1)/if
  + [ theseq2, GetSeqType, Define.nextvar]
  + index
  + [ Lit.1, PlusOp, Define(nextvar + 2)]
  + indexseqcode(Local.nextvar, theseq2, Local(nextvar + 2), theseqtype, true)
  next(newcode, nextvar + 3)
  else next(result + sym, nextvar)
 /for(result)

function forexpisnoop(forsym:symbol, code:seq.symbol)seq.symbol
 if nopara.forsym = 7 ∧ first.paratypes.forsym = resulttype.forsym ∧ code_(-2) = Littrue
 ∧ isseq.resulttype.last.code
 ∧ wordname.code_(-3) = "+"_1
 ∧  name.module.code_(-3) /in "seq" 
 ∧ isSequence.code_(-4)
 ∧ nopara.code_(-4) = 1
 ∧ last.code = code_(-8)
 ∧ last.code = code_(-6)
 ∧ code_(-7) = code_(-5)then
 let t2 = backparse2(code, length.code - 8, 2, empty:seq.int)
 let initacc = subseq(code, t2_1, t2_2 - 1)
 if length.initacc = 1 ∧ isrecordconstant.initacc_1
  ∧ constantcode.initacc_1 = [ Lit.0, Lit.0]then
   subseq(code, 1, t2_1 - 1) + subseq(code, t2_2, length.code - 8)
  else empty:seq.symbol
 else empty:seq.symbol

function indexseqcode(seqtype:symbol, theseq:symbol, masteridx:symbol, xtheseqtype:mytype, boundscheck:boolean)seq.symbol
 { seqtype will be a basetype }
 let seqparameter = parameter.xtheseqtype
 let theseqtype = seqof.seqparameter
 let elementtype = if seqparameter ∈ [ typeint, typereal, typeboolean]then seqparameter else if seqparameter ∈ [ typebyte, typebit]then typeint else typeptr
 let maybepacked = seqparameter ∈ packedtypes ∨ seqparameter = typebyte ∨ seqparameter = typebit
 let callidx = symbol(internalmod,"callidx", [ seqof.elementtype, typeint], elementtype)
 [ Start.elementtype, seqtype, Lit.1, GtOp, Br2(1, 2)] + [ theseq, masteridx, callidx, Exit]
  + if boundscheck then
   [ masteridx, theseq, GetSeqLength, GtOp, Br2(1, 2), symbol(modTausupport,"outofbounds", seqof.typeword), abortsymbol.elementtype, Exit]
  else empty:seq.symbol /if
  + if maybepacked then
   [ seqtype, Lit.1, EqOp, Br2(1, 2)] + [ theseq, masteridx, symbol(internalmod,"packedindex", theseqtype, typeint, elementtype), Exit]
  else empty:seq.symbol /if
  + [ theseq, masteridx, symbol(internalmod,"idxseq", seqof.elementtype, typeint, elementtype), Exit, EndBlock]

function forexpcode(forsym:symbol, code:seq.symbol, nextvar:int)expandresult
let t = backparse2(code, length.code, 5, empty:seq.int) << 1
let endexp = subseq(code, t_(-1), length.code)
let exitexp = subseq(code, t_(-2), t_(-1) - 1)
let bodyexp = subseq(code, t_(-3), t_(-2) - 1)
let endofsymbols = t_(-3) - 1
let startofsymbols = endofsymbols - (nopara.forsym - 3) / 2 + 1
let syms = subseq(code, startofsymbols, endofsymbols)
let tmp = for acc = empty:seq.symbol, i = 1, s = syms >> 1 do
 next(acc + Local(nextvar + i - 1), i + 1)
/for(acc)
let masteridx = Local(value.last.tmp + 1)
let seqelement = Local(value.masteridx + 1)
let nextvar1 = value.seqelement + 1
let Defineseqelement = Define.value.seqelement
let newsyms = tmp + seqelement
let theseqtype =(paratypes.forsym)_(length.newsyms)
let elementtype = if isseq.(paratypes.forsym)_(-4)then typeptr else(paratypes.forsym)_(-4)
{ let theseqtype = seqof.elementtype }
 let theseq = Local.nextvar1
 let totallength = Local(nextvar1 + 1)
 let seqtype = Local(nextvar1 + 2)
 let Defineseqtype = Define(nextvar1 + 2)
 let firstpart = subseq(code, 1, startofsymbols - 1) + [ Define.nextvar1, theseq, GetSeqLength, Define(nextvar1 + 1), theseq, GetSeqType, Defineseqtype, Lit.1]
 + Loopblock(subseq(paratypes.forsym, 1, length.syms - 1) + typeint, nextvar, resulttype.forsym)
 + { 2 if masteridx > totallength then exit }[ masteridx, totallength, GtOp]
 + Br2(2, 1)
 + { 3 else let sequenceele = seq_(idx)}indexseqcode(seqtype, theseq, masteridx, theseqtype, false)
 + [ Defineseqelement]
 + { 3 while condition }replace$for(exitexp, newsyms, syms)
 + Br2(2, 1)
 + { 4 exit loop }replace$for(endexp, newsyms, syms)
 + Exit
 let bodyexp2 = replace$for(bodyexp, newsyms, syms)
 let lastpart = if length.syms = 2 then bodyexp2 + [ masteridx, Lit.1, PlusOp, continue.2, EndBlock]
 else if not.iscompound.bodyexp then bodyexp2 >> 1 + [ masteridx, Lit.1, PlusOp, continue.length.syms, EndBlock]
 else
  { replace exits in body with a continue or abortsymbol }
  let continue2 = [ masteridx, Lit.1, PlusOp, continue.length.syms]
  let assert2 = [ abortsymbol.resulttype.forsym, Exit]
  let locs = exitlocations(bodyexp2, length.bodyexp2 - 1, empty:seq.int)
  { first item in locs is start of block and the rest are exits }
   for acc = subseq(bodyexp2, 1, first.locs - 1), last = first.locs + 1, i = locs << 1 do
    next(acc + subseq(bodyexp2, last, i - 2)
    + if inModFor(bodyexp2_(i - 1)) then continue2 else assert2, i + 1)
   /for(acc + subseq(bodyexp2, last, length.bodyexp2 - 1) + EndBlock)
 expandresult(nextvar1 + 3, firstpart + lastpart, bits.0)

function iscompound(bodyexp:seq.symbol)boolean
 { detects compound accumulator }
 let sym = bodyexp_(-3)
 isblock.last.bodyexp
  ∧ (wordname.sym = "next"_1 ∧ nopara.sym > 3 ∧ inModFor.sym 
  ∨ { assert case }abstracttype.resulttype.sym = addabstract(typeref."$base internal.",typeT))

function exitlocations(s:seq.symbol, i:int, result:seq.int)seq.int
let sym = s_i
 if isstart.sym then [ i] + result
 else if isblock.sym then exitlocations(s, matchblock(s, i - 1, 0) - 1, result)
 else exitlocations(s, i - 1, if isexit.sym then [ i] + result else result)

function replace$for(code:seq.symbol, new:seq.symbol, old:seq.symbol)seq.symbol
 for acc = empty:seq.symbol, s = code do
  acc
  + if inModFor.s  then
  let i = findindex(s, old)
  if i ≤ length.new then [ new_i]
   else { this is for one of two cases 1:a nested for and $for variable is from outer loop 2:the next expresion }[ s]
  else [ s]
 /for(acc)

________________________________

use set.symdef

Function pass2(knownsymbols :program)program 
subpass2(empty:seq.symdef, emptyprogram, knownsymbols, 0)



function subpass2(bigin:seq.symdef, corein:program, toprocess:program, count:int)program
 { assert count < 4 report"SIZE"+ print.length.toseq.toprocess + print.length.bigin + print.length.toseq.corein + print.count }
 for big = bigin, small = emptyprogram, core = corein, pele = tosymdefs.toprocess do
 let s = sym.pele
 let fullcode = code.pele
 let options = getoption.fullcode
 let code = removeoptions.fullcode
  if isempty.code  ∨ "VERYSIMPLE"_1 ∈ options then
   next(big, small,   pele /cup core)
  else if"COMPILETIME"_1 ∈ options then
  let code4 = firstopt(core, s, fullcode, options, true)
  next(big, small,   symdef(s, code4) /cup core)
  else if length.code < 30 then
  let t = firstopt(core, s, fullcode, options, true)
  if"INLINE"_1 ∈ getoption.t then next(big, small, symdef(s,t) /cup  core )
   else next(big, symdef( s, t) /cup small, core)
  else next(big + pele, small, core)
 /for(if length.tosymdefs.corein = length.tosymdefs.core then
  for acc = core, prgele = tosymdefs.core + tosymdefs.small + big do
  let code3 = code.prgele
  let sym3 = sym.prgele
   if isempty.code3 then   prgele /cup acc else symdef( sym3, firstopt(acc, sym3, code3, getoption.code3, false) ) /cup acc
  /for(acc)
 else subpass2(big, core, small, count + 1)/if)

function matchblock(s:seq.symbol, i:int, nest:int)int
let sym = s_i
 if isblock.sym then matchblock(s, i - 1, nest + 1)
 else if isstartorloop.sym then
  if nest = 0 then
   if isloopblock.sym then backparse2(s, i - 1, nopara.sym, empty:seq.int)_1 else addDefine(s, i)
  else matchblock(s, i - 1, nest - 1)
 else matchblock(s, i - 1, nest)

function addDefine(s:seq.symbol, i:int)int
 if i > 1 ∧ isdefine.s_(i - 1)then
  addDefine(s, backparse2(s, i - 2, 1, empty:seq.int)_1)
 else i

function backparse2(s:seq.symbol, i:int, no:int, result:seq.int)seq.int
 if no = 0 then result
 else
  assert i > 0 report"back parse 1a:" + toword.no + print.s + stacktrace
   if isdefine.s_i then
   let args = backparse2(s, i - 1, 1, empty:seq.int)
   backparse2(s, args_1, no, result)
   else if isblock.s_i then
   let b = matchblock(s, i - 1, 0)
   if b = 1 then [ b] + result
    else backparse2(s, b - 1, no - 1, [ b] + result)
   else
    let nopara = nopara.s_i
    let first = if nopara = 0 then i
    else
     let args = backparse2(s, i - 1, nopara, empty:seq.int)
     assert length.args = nopara report"back parse 3" + print.[ s_i] + toword.nopara + "//"
      + for acc ="", @e = args do acc + toword.@e /for(acc)
      args_1
    let b = if first > 1 ∧ isdefine.s_(first - 1)then
    let c = backparse2(s, first - 2, 1, empty:seq.int)
    c_1
    else first
     backparse2(s, b - 1, no - 1, [ b] + result)
     
use program

 

 