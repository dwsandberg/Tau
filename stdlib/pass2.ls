Module pass2

use UTF8

use bits

use breakblocks

use interpreter

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

use otherseq.symbol

use seq.symbol

use set.symbol

use otherseq.word

use set.word

use otherseq.seq.int

use seq.seq.int

use seq.seq.symbol

use worddict.seq.symbol

use seq.seq.word

use set.seq.word

use seq.seq.seq.symbol

function firstopt(p:program, rep:symbol, code:seq.symbol, alltypes:typedict)program
let nopara = nopara.rep
 if isempty.removeoptions.code then map(p, rep, code)
 else
  let pdict = addpara(emptyworddict:worddict.seq.symbol, nopara)
  let code2 = code.yyy(p, code, 1, empty:seq.symbol, nopara + 1, pdict, true)
  let s = symbol(fsig.rep, module.rep, returntype.rep)
  let a = breakblocks(p, code2, s, alltypes)
  let a2 = code.yyy(p, a, 1, empty:seq.symbol, nopara + 1, pdict, true)
   addf(p, s, a2)

function print(s:seq.int)seq.word for acc ="", @e = s do acc + toword.@e end(acc)

function var(i:int)symbol Local.i

function var(w:word)symbol Local.w

function addpara(map:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i ≤ 0 then map
 else
  let v = var.i
   addpara(add(map, toword.i, [ v]), i - 1)

function addlooplocals(map:worddict.seq.symbol, firstvar:int, nextvar:int, nopara:int, i:int)worddict.seq.symbol
 if i = nopara then map
 else
  addlooplocals(replace(map, toword(firstvar + i), [ var(nextvar + i)]), firstvar, nextvar, nopara, i + 1)

function yyy(p:program, org:seq.symbol, k:int, result:seq.symbol, nextvar:int, map:worddict.seq.symbol, papply:boolean)expandresult
 if k > length.org then expandresult(nextvar, result)
 else
  let sym = org_k
  let len = length.result
   if isconst.sym then yyy(p, org, k + 1, result + sym, nextvar, map, papply)
   else if isspecial.sym then
   if fsig.sym = "BLOCK 3"then
    let t = backparse(result, len, 3, empty:seq.int) + [ len + 1]
    let condidx = t_2 - 4
    let cond = result_condidx
    let newresult = if not.isbr.result_(condidx + 3)then result + sym
    else if cond = Litfalse then
    let keepblock = value.result_(condidx + 2)
     subseq(result, 1, condidx - 1) + subseq(result, t_keepblock, t_(keepblock + 1) - 2)
    else if cond = Littrue then
    let keepblock = value.result_(condidx + 1)
     subseq(result, 1, condidx - 1) + subseq(result, t_keepblock, t_(keepblock + 1) - 2)
    else result + sym
     yyy(p, org, k + 1, newresult, nextvar, map, papply)
    else if \\ isdefine \\(fsig.sym)_1 = "DEFINE"_1 then
    let thelocal =(fsig.sym)_2
     if len > 0 ∧ (isconst.result_len ∨ islocal.result_len)then
     yyy(p, org, k + 1, subseq(result, 1, length.result - 1), nextvar, replace(map, thelocal, [ result_len]), papply)
     else
      yyy(p, org, k + 1, result + Define.toword.nextvar, nextvar + 1, replace(map, thelocal, [ var.nextvar]), papply)
    else if isloopblock.sym then
    let nopara = nopara.sym - 1
    let firstvar = value.result_len
     yyy(p, org, k + 1, subseq(result, 1, len - 1) + Lit.nextvar + sym, nextvar + nopara, addlooplocals(map, firstvar, nextvar, nopara, 0), papply)
    else if isRecord.sym ∨ isSequence.sym then
    let nopara = nopara.sym
    let args = subseq(result, len + 1 - nopara, len)
     if for acc = true, @e = args do acc ∧ isconst.@e end(acc)then
     yyy(p, org, k + 1, subseq(result, 1, len - nopara) + Constant2(args + sym), nextvar, map, papply)
     else yyy(p, org, k + 1, result + sym, nextvar, map, papply)
    else if(module.sym)_1 = "local"_1 then
    let t = lookup(map,(fsig.sym)_1)
     if isempty.t then yyy(p, org, k + 1, result + sym, nextvar, map, papply)
     else yyy(p, org, k + 1, result + t_1, nextvar, map, papply)
    else if(module.sym)_1 = "para"_1 then
    let sym2 = Local.(module.sym)_2
    let t = lookup(map,(fsig.sym2)_1)
     if isempty.t then yyy(p, org, k + 1, result + sym2, nextvar, map, papply)
     else yyy(p, org, k + 1, result + t_1, nextvar, map, papply)
    else if len > 2 ∧ result_(len - 2) = NotOp ∧ fsig.sym = "BR 3"then
    yyy(p, org, k + 1, subseq(result, 1, len - 3) + [ result_len, result_(len - 1), Br], nextvar, map, papply)
    else yyy(p, org, k + 1, result + sym, nextvar, map, papply)
   else if papply ∧ (fsig.sym)_1 ∈ "apply5"then applycode5(p, org, k, result, nextvar, map, papply)
   else if papply ∧ (fsig.sym)_1 ∈ "forexp"then forexpcode(p, org, k, result, nextvar, map, papply)
   else
    let nopara = nopara.sym
    let dd = code.lookupcode(p, sym)
    let options = getoption.dd
     if(first."COMPILETIME" ∈ options ∨ fsig.sym = "_(word seq, int)")
     ∧ for acc = true, @e = subseq(result, len - nopara + 1, len)do acc ∧ isconst.@e end(acc)then
     let newcode = interpret(subseq(result, len - nopara + 1, len) + sym)
     let newconst = if length.newcode > 1 then Constant2.newcode else first.newcode
      yyy(p, org, k + 1, result >> nopara + newconst, nextvar, map, papply)
     else if fsig.sym = "decodeword(word)" ∧ module.result_len = "$word"then
     let arg1 = result_len
     let a1 = for acc = empty:seq.symbol, @e = tointseq.decodeword.(fsig.arg1)_1 do acc + Lit.@e end(acc)
     let d = Constant2(a1 + Sequence(typeint, length.a1))
      yyy(p, org, k + 1, result >> 1 + d, nextvar, map, papply)
     else if not("INLINE"_1 ∈ options ∨ first."VERYSIMPLE" ∈ options)then
     yyy(p, org, k + 1, result + sym, nextvar, map, papply)
     else
      let code = removeoptions.dd
       if isempty.code then yyy(p, org, k + 1, result + sym, nextvar, map, papply)
       else if length.code = 1 ∧ code = [ var.1] ∧ nopara = 1 then
       \\ function just returns result \\ yyy(p, org, k + 1, result, nextvar, map, papply)
       else
        let t = backparse(result, len, nopara, empty:seq.int) + [ len + 1]
         assert length.t = nopara + 1 report"INLINE PARA PROBLEM"
         let new = if"STATE"_1 ∉ options ∧ issimple(p, nopara, code)then
         let pmap = simpleparamap(result, t, emptyworddict:worddict.seq.symbol, nopara)
          yyy(p, code, 1, empty:seq.symbol, nextvar, pmap, papply)
         else expandinlineX(result, t, emptyworddict:worddict.seq.symbol, nopara, empty:seq.symbol, nextvar, code, p, papply)
          yyy(p, org, k + 1, subseq(result, 1, t_1 - 1) + code.new, nextvar.new, map, papply)

function simpleparamap(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int)worddict.seq.symbol
 if i = 0 then pmap
 else
  simpleparamap(s, t, add(pmap, toword.i, subseq(s, t_i, t_(i + 1) - 1)), i - 1)

function expandinlineX(s:seq.symbol, t:seq.int, pmap:worddict.seq.symbol, i:int, newcode:seq.symbol, nextvar:int, inlinecode:seq.symbol, p:program, papply:boolean)expandresult
 \\ when i > 0 then assigning parameters to new local variables \\
 if i = 0 then
 let r = yyy(p, inlinecode, 1, empty:seq.symbol, nextvar, pmap, papply)
  expandresult(nextvar.r, newcode + code.r)
 else
  expandinlineX(s, t, add(pmap, toword.i, [ var.nextvar]), i - 1, subseq(s, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode, nextvar + 1, inlinecode, p, papply)

function replace(s:seq.symbol, start:int, length:int, value:seq.symbol)seq.symbol
 subseq(s, 1, start - 1) + value + subseq(s, start + length, length.s)

function adddefines2(s:seq.symbol, t:seq.int, i:int, nopara:int, newcode:seq.symbol, nextvar:int)seq.symbol
 if i > nopara then newcode
 else
  adddefines2(s, t, i + 1, nopara, newcode + subseq(s, t_i, t_(i + 1) - 1)
  + Define.toword(nextvar + i - 1), nextvar)

type expandresult is nextvar:int, code:seq.symbol

function definepara(code:seq.symbol, t:seq.int, i:int, nextvar:int, newcode:seq.symbol)seq.symbol
 if i = 0 then newcode
 else
  definepara(code, t, i - 1, nextvar - 1, subseq(code, t_i, t_(i + 1) - 1) + Define.toword.nextvar + newcode)

function substitute(s:seq.symbol, old:seq.symbol, new:seq.symbol)seq.symbol
 for acc = empty:seq.symbol, @e = s do
  acc
 + let i = findindex(@e, old)
   if between(i, 1, length.old)then new_i else @e
 end(acc)

compound accumaltor possiblities
+(int graph, int arc)graph.int
,"advancepnp(pnpstate, word)format"
,"state100(state100, program, symbol, symbol)breakblocks"
,"+(out23, char)format"
,"deletearc(word seq graph, word seq arc)graph.seq.word"
,"+(word seq graph, word seq arc)graph.seq.word"
,"+(place, char seq encodingpair)maindict"] 

function forexpcode(p:program, org:seq.symbol, k:int, code:seq.symbol, nextvar:int, map:worddict.seq.symbol, papply:boolean)expandresult
let forsym = org_k
let t = backparse(code, length.code, 4, empty:seq.int)
let endexp = subseq(code, t_(-1), length.code)
let exitexp = subseq(code, t_(-2), t_(-1) - 1)
let bodyexp = subseq(code, t_(-3), t_(-2) - 1)
let endofsymbols = t_(-3) - 1
let startofsymbols = endofsymbols - (nopara.forsym - 3) / 2 + 1
let syms = subseq(code, startofsymbols, endofsymbols)
let tmp = for acc = empty:seq.symbol, i = 1, s = syms >> 1 do
 next(acc + Local(nextvar + i - 1), i + 1)
end(acc)
let masteridx = Local(value.last.tmp + 1)
let seqelement = Local(value.masteridx + 1)
let nextvar1 = value.seqelement + 1
let Defineseqelement = Define.fsig.seqelement
let newsyms = tmp + seqelement
let theseqtype =(paratypes.org_k)_(length.newsyms)
let elementtype = if abstracttype.parameter.theseqtype ∈ "real"then mytype."real"
else if abstracttype.parameter.theseqtype ∈ "int bit byte boolean"then typeint else typeptr
let packedseq = maybepacked.theseqtype
let theseq = Local.nextvar1
let totallength = Local(nextvar1 + 1)
let seqtype = Local(nextvar1 + 2)
let Defineseqtype = Define(nextvar1 + 2)
let isnoop = if length.syms = 2 ∧ length.bodyexp = 4
∧ abstracttype.resulttype.first.syms = "seq"_1
∧ subseq(bodyexp, 1, 2) = syms
∧ name.last.bodyexp = "+"
∧ last.module.last.bodyexp = "seq"_1
∧ name.bodyexp_3 = "SEQUENCE 1"
∧ last.code = first.syms
∧ code_(-2) = Littrue then
let t2 = backparse(code, startofsymbols - 1, 2, empty:seq.int)
let initacc = subseq(code, t2_1, t2_2 - 1)
 if length.initacc = 1 ∧ isrecordconstant.initacc_1
 ∧ constantcode.initacc_1 = [ Lit.0, Lit.0]then
 subseq(code, 1, t2_1 - 1) + subseq(code, t2_2, startofsymbols - 1)
 else empty:seq.symbol
else empty:seq.symbol
 if not.isempty.isnoop then yyy(p, org, k + 1, isnoop, nextvar1 + 2, map, papply)
 else
  let part1 = subseq(code, 1, startofsymbols - 1) + Define.nextvar1 + theseq + GetSeqLength
  + Define(nextvar1 + 1)
  + Lit.1
  + Lit.nextvar
  + Loopblock(subseq(paratypes.forsym, 1, length.syms - 1) + typeint)
  + \\ 2 if masteridx > totallength then exit \\
  [ masteridx, totallength, GtOp, Lit.3, Lit.4, Br]
  + \\ 3 exit loop \\
  replace$for(endexp, newsyms, syms)
  + [ Exit, \\ 4 else let sequenceele = seq_(idx)\\ theseq, GetSeqType, Defineseqtype, seqtype, Lit.0, EqOp, Lit.2, Lit.3, Br
  , theseq, masteridx, IdxS.theseqtype, Exit]
  + if packedseq then [ seqtype, Lit.1, EqOp, Lit.4, Lit.5, Br, theseq, masteridx] + packedindex2.theseqtype + [ Exit]
  else empty:seq.symbol ;
  + [ theseq, masteridx, Callidx.theseqtype, Exit, Block(elementtype, if packedseq then 5 else 3)]
  + [ Defineseqelement]
  + \\ 4 while condition \\
  replace$for(exitexp, newsyms, syms) + [ Lit.5, Lit.3, Br]
  + \\ 5 do body and continue \\
  replace$for(bodyexp, newsyms, syms, [ masteridx, Lit.1, PlusOp, continue.length.syms])
  + if length.syms = 2 then [ masteridx, Lit.1, PlusOp, continue.2]else empty:seq.symbol ;
  + [ Block(resulttype.forsym, 5)]
   \\ assert false report print.forsym + print.startofsymbols + print.endofsymbols + EOL + print.endexp + EOL +"exit:"+ print.exitexp + EOL +"body:"+ print.bodyexp + EOL +"syms"+ print.subseq(code, startofsymbols, endofsymbols)+ EOL +"part1"+ print.part1 \\
   yyy(p, org, k + 1, part1, nextvar1 + 2, map, papply)

function replace$for(code:seq.symbol, new:seq.symbol, old:seq.symbol)seq.symbol replace$for(code, new, old, empty:seq.symbol)

function replace$for(code:seq.symbol, new:seq.symbol, old:seq.symbol, cont:seq.symbol)seq.symbol
 for acc = empty:seq.symbol, s = code do 
  if last.module.s = "$for"_1 then
   acc
  + if nopara.s > 0 then cont
  else
   let i = findindex(s, old)
    if i ≤ length.new then [ new_findindex(s, old)]
    else \\ this is a nested for and $for variable is from outer loop \\ [ s]
  else if last.module.s = "for"_1 then acc + cont else acc + s
 end(acc)

function applycode5(p:program, org:seq.symbol, k:int, code:seq.symbol, nextvar:int, map:worddict.seq.symbol, papply:boolean)expandresult
let totallength = nextvar + 1
let seqtype = Local(nextvar + 2)
let Defineseqtype = Define(nextvar + 2)
let Definenewmasteridx = Define(nextvar + 3)
let newmasteridx = Local(nextvar + 3)
let Defineseqelement = Define(nextvar + 4)
let seqelement = Local(nextvar + 4)
let Defineinitacc = Define(nextvar + 5)
let initacc = Local(nextvar + 5)
let theseq = Local(nextvar + 6)
let lastUsed = nextvar + 6
let applysym = org_k
let resulttype =(paratypes.applysym)_1
let theseqtype =(paratypes.applysym)_2
let elementtype = if abstracttype.parameter.theseqtype ∈ "real"then mytype."real"
else if abstracttype.parameter.theseqtype ∈ "int bit byte boolean"then typeint else typeptr
let exitstart = backparse(code, length.code, 1, empty:seq.int)_1
let t = backparse(code, exitstart - 1, 1, empty:seq.int)
let thunk0 = subseq(code, t_1, exitstart - 1)
let accfunc = last.thunk0
let thunkplaceholders = subseq(code, t_1 - 3, t_1 - 1)
let initseq = code_(t_1 - 4)
  let part1 = subseq(code, 1, t_1 - 5) + [ Defineinitacc, initseq, GetSeqLength, Define.totallength, initseq, initacc]
  let acc = Local(lastUsed + 1)
   let masteridx = Local(lastUsed + 2)
   let thunkcode =       substitute(thunk0, thunkplaceholders, [ seqelement, acc, masteridx]) + [ newmasteridx, continue.3]
  let packedseq = maybepacked.theseqtype
   let kk = \\ loop(seq, acc, masteridx)\\
   \\ 1 \\ 
   [ Lit.1, Lit.lastUsed, Loopblock.[ theseqtype, resulttype, typeint]]
   + \\ 2 if masteridx > totallength then exit \\
   [ masteridx, Local.totallength, GtOp, Lit.3, Lit.4, Br]
   + \\ 3 \\
[ acc, Exit, \\ 4 else let newmasteridx = masteridx + 1, let sequenceele = seq_(idx)continue(thseqeq, thunk, newmasteridx)\\ masteridx, Lit.1, PlusOp, Definenewmasteridx, theseq, GetSeqType, Defineseqtype, seqtype
, Lit.0, EqOp, Lit.2, Lit.3, Br, theseq, masteridx, IdxS.theseqtype, Exit]
   + if packedseq then [ seqtype, Lit.1, EqOp, Lit.4, Lit.5, Br, theseq, masteridx] + packedindex2.theseqtype + [ Exit]
   else empty:seq.symbol ;
   + [ theseq, masteridx, Callidx.theseqtype, Exit, Block(elementtype, if packedseq then 5 else 3), Defineseqelement, theseq]
   + thunkcode
   + [ Block(resulttype, 4)]
    yyy(p, org, k + 1, part1 + kk, lastUsed + 3, map, papply)

function maxvarused(code:seq.symbol)int maxvarused(code, 1, 0)

function maxvarused(code:seq.symbol, i:int, lastused:int)int
 if i > length.code then lastused
 else
  let s = code_i
   maxvarused(code
   , i + 1
   , max(lastused
   , if abstracttype.modname.s = "local"_1 then toint.(fsig.s)_1
   else if abstracttype.modname.s = "$define"_1 then toint.(fsig.s)_2 else 0
   )
   )

function depthfirst(knownsymbols:program, alltypes:typedict, i:int, pending:seq.symbol, processed:program, code:seq.symbol, s:symbol)program
 if i > length.code then firstopt(processed, s, code, alltypes)
 else
  let sym = code_i
  let sym2 = basesym.sym
  let newprg = if isconst.sym2 ∨ isspecial.sym2 ∨ sym2 ∈ pending then processed
  else
   let r = lookupcode(processed, sym)
    if isdefined.r then processed
    else
     let rep2 = lookupcode(knownsymbols, sym2)
      if length.code.rep2 > 0 then depthfirst(knownsymbols, alltypes, 1, pending + sym2, processed, code.rep2, sym2)else processed
   depthfirst(knownsymbols, alltypes, i + 1, pending, newprg, code, s)

________________________________

function addf(p:program, s:symbol, code0:seq.symbol)program
let options = getoption.code0
let code = removeoptions.code0
let fsig = fsig.s
let newoptions = if fsig = "∈(int, int seq)" ∨ fsig = "∈(word, word seq)"
∨ fsig = "_(int seq, int)"
∨ fsig = "_(word seq, int)"then
""
else
 let state = state100(code, p, s)
  options
  + if hasstate.state ∧ "STATE"_1 ∉ options then"STATE"else"";
  + if length.code < 20 ∧ not.callsself.state ∧ "NOINLINE"_1 ∉ options then
  "INLINE"
  else""
 map(p, s, if newoptions = ""then code else code + Words.newoptions + Optionsym)

// statebit is set on option so that adding an option doesn't auto add a inline bit ' //

Function issimple(p:program, nopara:int, code:seq.symbol)boolean
 between(length.code, 1, 15) ∧ (nopara = 0 ∨ checksimple(p, code, 1, nopara, 0))

function checksimple(p:program, code:seq.symbol, i:int, nopara:int, last:int)boolean
 \\ check that the parameters occur in order and they all occur exactly once \\
 \\ Any op that may involve state must occur after all parameters \\
 \\ should also check for loopblock \\
 if i > length.code then last = nopara
 else
  let rep = code_i
   if islocal.rep then
   let parano = value.rep
    if parano = last + 1
    ∧ (nopara ≠ parano ∨ not.hasstate.state100(subseq(code, 1, i - 1), p, rep))then
    checksimple(p, code, i + 1, nopara, last + 1)
    else false
   else checksimple(p, code, i + 1, nopara, last)

---------------------------

Function pass2(knownsymbols:program, alltypes:typedict)program
let bin0 = for acc = filterp(emptyprogram, emptyprogram), @e = toseq.knownsymbols do filterp(acc, @e, code.lookupcode(knownsymbols, @e), alltypes)end(acc)
let bin = for acc = filterp(emptyprogram, simple.bin0), @e = toseq.complex.bin0 do
 filterp(acc, @e, code.lookupcode(complex.bin0, @e), alltypes)
end(acc)
 \\ assert false report checkt(bin0)assert false report print.length.toseq.complex.bin + print.length.toseq.simple.bin \\
 for acc = simple.bin, sym = toseq.complex.bin do
  \\ depthfirst(acc, knownsymbols, alltypes, sym)Function depthfirst(acc:program, knownsymbols:program, alltypes:typedict, sym:symbol)program \\
  depthfirst(acc, alltypes, 1, [ sym], acc, code.lookupcode(knownsymbols, sym), sym)
 end(acc)

type filterp is complex:program, simple:program

function filterp(p:filterp, s:symbol, code:seq.symbol, alltypes:typedict)filterp
let complex = complex.p
let simple = simple.p
let options = getoption.code
 if isempty.code ∨ "BUILTIN"_1 ∈ options ∨ "VERYSIMPLE"_1 ∈ options then
 filterp(complex, map(simple, s, code))
 else if length.code < 30 ∨ "COMPILETIME"_1 ∈ options then
 let nopara = nopara.s
 let pdict = addpara(emptyworddict:worddict.seq.symbol, nopara)
 let code2 = code.yyy(simple, code, 1, empty:seq.symbol, nopara + 1, pdict, false)
  if length.code2 = 3 ∧ code2_1 = Local.1
  ∧ (fsig.code2_3)_1 ∈ "IDX"
  ∧ isconst.code2_2
  ∨ length.code2 = 1 ∧ nopara = 1 ∧ code2_1 = Local.1 then
  filterp(complex, map(simple, s, code2 + [ Words."VERYSIMPLE", Optionsym]))
  else if hasunknown.state100(removeoptions.code2, simple, s) ∧ "COMPILETIME"_1 ∉ options then
  filterp(addf(complex, s, code), simple)
  else filterp(complex, firstopt(simple, s, code2, alltypes))
 else filterp(map(complex, s, code), simple)

function xxx(p:program, alltypes:typedict, s:symbol)program
let code = code.lookupcode(p, s)
 if isempty.code then p else firstopt(p, s, code, alltypes)

Function uses(p:program, roots:set.symbol)set.symbol uses(p, empty:set.symbol, roots)

Function defines(p:program, roots:set.symbol)seq.symbol
 for acc = empty:seq.symbol, @e = toseq.roots do
  acc + if isconstantorspecial.@e ∨ isabstract.modname.@e then empty:seq.symbol else [ @e]
 end(acc)

function uses(p:program, processed:set.symbol, toprocess:set.symbol)set.symbol
 if isempty.toprocess then processed
 else
  let q = asset.for acc = empty:seq.symbol, @e = toseq.toprocess do
   acc
  + let d = code.lookupcode(p, @e)
   \\ assert not.containspara.d report"has p"+ print.@e + print.d \\
    if isempty.d then constantcode.@e else d
  end(acc)
   uses(p, processed ∪ toprocess, q - processed)

function containspara(code:seq.symbol)boolean for hasparameter = false, e = code do hasparameter ∨ isparameter.e end(hasparameter)