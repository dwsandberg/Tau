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

function print(s:seq.int)seq.word for @e ∈ s, acc ="",,, acc + toword.@e

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
      if for @e ∈ args, acc = true ,,, acc ∧ isconst.@e then
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
   else
    let nopara = nopara.sym
    let dd = code.lookupcode(p, sym)
    let options = getoption.dd
     if(first."COMPILETIME" ∈ options ∨ fsig.sym = "_(word seq, int)")
     ∧ for @e ∈ subseq(result, len - nopara + 1, len), acc = true ,,, acc ∧ isconst.@e then
     let newcode = interpret(subseq(result, len - nopara + 1, len) + sym)
      let newconst = if length.newcode > 1 then Constant2.newcode else first.newcode
       yyy(p, org, k + 1, result >> nopara + newconst, nextvar, map, papply)
     else if fsig.sym = "decodeword(word)" ∧ module.result_len = "$word"then
     let arg1 = result_len
      let a1 = for @e ∈ tointseq.decodeword.(fsig.arg1)_1, acc = empty:seq.symbol ,,, acc + Lit.@e
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
 for @e ∈ s, acc = empty:seq.symbol ,,, acc
 + 
 let i = findindex(@e, old)
  if between(i, 1, length.old)then new_i else @e

type compoundAC is state:word, result:seq.symbol, fldno:int

function chkAcc(a:compoundAC, next:symbol, fldvar:seq.symbol)compoundAC
 let state = state.a
 let newstate = if state = "start"_1 then
 if next = Local.1 then"local1"_1 else"start"_1
 else if state = "local1"_1 then if not.islit.next then"fail"_1 else"idx"_1
 else if state = "idx"_1 then if isIdx.next then"start"_1 else"fail"_1
 else"fail"_1
 let newresult = if newstate = "start"_1 then
 if state = "start"_1 then result.a + next
  else result.a + fldvar_(fldno.a + 1)
 else result.a
  compoundAC(newstate, newresult, if islit.next then value.next else fldno.a)

function breakAccumalator5(p:program, thunk:seq.symbol, resulttype:mytype, lastvar:int, seqelement:symbol, newmasteridx:symbol, papply:boolean, thunkplaceholders:seq.symbol)breakresult
 \\ lastvar + 1 to lastvar + nopara.last.code are accumalators \\
 \\ lastvar + 1 + nopara.last.code lastvar + nopara.last.code + nopara.accfunc-1 are location of parameters for lastvar \\
 if not(typerep.resulttype = "ptr" ∧ length.thunk > 2 ∧ first.thunk = thunkplaceholders_2
 ∧ resulttype.thunkplaceholders_2 = resulttype.last.thunk)then
 issimple
 else
  let accfunc = last.thunk
  let ttt = lookupcode(p, last.thunk)
  let code = removeoptions.code.ttt
   if isempty.code ∨ not.isRecord.last.code then issimple
   else
    let noAccumlators = nopara.last.code
    let fldnames = for @e ∈ paratypes.last.code, acc ="", @i, , acc + merge([ toword.@i] + typerep.@e)
    let fldsyms = for @e ∈ fldnames, acc = empty:seq.symbol ,,, acc + Local.@e
    let t5 = for @e ∈ code, acc = compoundAC("start"_1, empty:seq.symbol, 0),,, chkAcc(acc, @e, fldsyms)
    let xx = for e ∈ result.t5, acc = empty:seq.symbol ,,,
    let i = findindex(e, fldsyms)
     acc
     + if i > noAccumlators then [ e]else [ Local.1, Lit(i - 1), Idx.(paratypes.last.code)_i]
     \\ assert state.t5 ="fail"_1 &or xx = code report"DIFF"+ print.accfunc + EOL + print.xx + EOL + state.t5 + print.result.t5 \\
     \\ assert print.accfunc &in ["+(int graph, int arc)graph.int","advancepnp(pnpstate, word)format","advance(bindinfo lrstate, word, int, word seq, bindinfo token seq)parsersupport.bindinfo","advance(attribute2 lrstate, word, int, word seq, attribute2 token seq)parsersupport.attribute2","state100(state100, program, symbol, symbol)breakblocks","chkAcc(compoundAC, symbol, symbol seq)pass2","+(out23, char)format","deletearc(word seq graph, word seq arc)graph.seq.word","+(word seq graph, word seq arc)graph.seq.word","+(place, char seq encodingpair)maindict"]report"ZZZZZ"+ print.accfunc + EOL + state.t5 + print.result.t5 + EOL + EOL + print.code \\
     if state.t5 = "fail"_1 then issimple
     else
      let x = for @e ∈ fldnames, acc = emptyworddict:worddict.seq.symbol, @i, , add(acc, @e, [ Local(lastvar + @i)])
      let masteridx = lastvar + noAccumlators + 1
      let pmap = for @e ∈ paratypes.accfunc << 1, acc = x, @i, , add(acc, toword(@i + 1), [ Local(masteridx + @i)])
      let nextvar = masteridx + nopara.accfunc
      let r = yyy(p, result.t5 >> 1, 1, empty:seq.symbol, nextvar, pmap, papply)
      let thunkcode = substitute(subseq(thunk, 2, length.thunk - 1), thunkplaceholders, [ seqelement, Lit.0, Local.masteridx])
      + for @e ∈ arithseq(nopara.accfunc - 1,-1, nextvar - 1), acc = empty:seq.symbol ,,, acc + Define.toword.@e ;
      + code.r
      + newmasteridx
      + continue(noAccumlators + 2)
      let orgacc = nextvar.r
      let loopcode = for @e ∈ arithseq(nopara.last.code, 4, 2), acc = [ Define.orgacc],,, acc + [ Local.orgacc] + subseq(code, @e, @e + 1);
      + [ Lit.1, Lit.lastvar, Loopblock([ typeptr] + paratypes.last.code + typeint)]
      let finalcode = for @e ∈ arithseq(noAccumlators, 1, lastvar + 1), acc = empty:seq.symbol ,,, acc + Local.@e ;
      + last.code
       if true then issimple else breakresult(loopcode, thunkcode, finalcode, orgacc + 1, Local.masteridx)

type breakresult is loopcode:seq.symbol, thunkcode:seq.symbol, finalcode:seq.symbol, nextvar:int, masteridx:symbol

function issimple breakresult breakresult(empty:seq.symbol, empty:seq.symbol, empty:seq.symbol, 0, Lit.0)

function print(b:breakresult)seq.word
 "loopcode:" + print.loopcode.b + EOL + "thunkcode:" + print.thunkcode.b
 + EOL
 + "finalcode:"
 + print.finalcode.b
 + EOL
 + "nextvar:"
 + print.nextvar.b

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
 let exitexp = subseq(code, exitstart, length.code)
 let t = backparse(code, exitstart - 1, 1, empty:seq.int)
 let thunk0 = subseq(code, t_1, exitstart - 1)
 let accfunc = last.thunk0
 let thunkplaceholders = subseq(code, t_1 - 3, t_1 - 1)
 let initseq = code_(t_1 - 4)
 let maybenoop = exitexp = [ Litfalse] ∧ length.thunk0 ∈ [ 3, 6]
 ∧ abstracttype.resulttype.accfunc = "seq"_1
 ∧ first.fsig.accfunc = "+"_1
 ∧ code_(t_1 - 5) = Constant2.Emptyseq.elementtype
  if maybenoop ∧ thunk0 = [ thunkplaceholders_2, thunkplaceholders_1, accfunc] ∧ module.accfunc = "bits seq"then
  \\ assert false report"symbol("+ fsig.accfunc + '","' + module.accfunc + '","' + returntype.accfunc +")"\\
   yyy(p, org, k + 1, code >> 9 + initseq, nextvar, map, papply)
  else if maybenoop ∧ length.thunk0 = 6 ∧ isRecord.thunk0_5
  ∧ thunk0 >> 2 = [ thunkplaceholders_2, Lit.0, Lit.1, thunkplaceholders_1]then
  yyy(p, org, k + 1, code >> 12 + initseq, nextvar, map, papply)
  else
   let part1 = subseq(code, 1, t_1 - 5) + [ Defineinitacc, initseq, GetSeqLength, Define.totallength, initseq, initacc]
   let checkCompound = breakAccumalator5(p, thunk0, resulttype, lastUsed, seqelement, newmasteridx, papply, thunkplaceholders)
   let codeparts = if nextvar.checkCompound = nextvar.issimple then
   \\ simple acc \\
    let acc = Local(lastUsed + 1)
    let masteridx1 = Local(lastUsed + 2)
     breakresult([ Lit.1, Lit.lastUsed, Loopblock.[ typeptr, resulttype, typeint]], substitute(thunk0, thunkplaceholders, [ seqelement, acc, masteridx1]) + [ newmasteridx, continue.3], [ acc], lastUsed + 3, masteridx1)
   else checkCompound
   let masteridx = masteridx.codeparts
   let exitexp2 = if exitexp = [ Litfalse]then empty:seq.symbol
   else
    substitute(exitexp, thunkplaceholders, [ seqelement, \\ needs attention \\ Lit.0, masteridx])
    + [ Lit.2, Lit.3, Br, Local.totallength, Lit.1, PlusOp, Exit, newmasteridx, Exit, Block(typeint, 3)]
   let thunkcode = if isempty.exitexp2 then thunkcode.codeparts
   else
    let a = thunkcode.codeparts
     a >> 2 + exitexp2 + last.a
   let packedseq = maybepacked.theseqtype
    \\ let u = backparse([ Lit.1]+ thunkcode, length.thunkcode + 1, 1, empty:seq.int)assert u_1 = 1 report"XXX"+ print.u_1 + print.thunkcode \\
    let kk = \\ loop(seq, acc, masteridx)\\
    \\ 1 \\
    loopcode.codeparts
    + \\ 2 if masteridx > totallength then exit \\
    [ masteridx, Local.totallength, GtOp, Lit.3, Lit.4, Br]
    + \\ 3 \\
    finalcode.codeparts
    + [ Exit, \\ 4 else let newmasteridx = masteridx + 1, let sequenceele = seq_(idx)continue(thseqeq, thunk, newmasteridx)\\ masteridx, Lit.1, PlusOp, Definenewmasteridx, theseq, GetSeqType, Defineseqtype, seqtype
    , Lit.0, EqOp, Lit.2, Lit.3, Br, theseq, masteridx, IdxS.theseqtype, Exit]
    + if packedseq then [ seqtype, Lit.1, EqOp, Lit.4, Lit.5, Br, theseq, masteridx] + packedindex2.theseqtype + [ Exit]
    else empty:seq.symbol ;
    + [ theseq, masteridx, Callidx.theseqtype, Exit, Block(elementtype, if packedseq then 5 else 3), Defineseqelement, theseq]
    + thunkcode
    + [ Block(resulttype, 4)]
     yyy(p, org, k + 1, part1 + kk, nextvar.codeparts, map, papply)

function maxvarused(code:seq.symbol)int maxvarused(code, 1, 0)

function maxvarused(code:seq.symbol, i:int, lastused:int)int
 if i > length.code then lastused
 else
  let s = code_i
   maxvarused(code
   , i + 1
   , max(lastused, if abstracttype.modname.s = "local"_1 then toint.(fsig.s)_1
   else if abstracttype.modname.s = "$define"_1 then toint.(fsig.s)_2 else 0))

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
   options + if hasstate.state ∧ "STATE"_1 ∉ options then"STATE"else"";
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
 let bin0 = for @e ∈ toseq.knownsymbols, acc = filterp(emptyprogram, emptyprogram),,, filterp(acc, @e, code.lookupcode(knownsymbols, @e), alltypes)
 let bin = for @e ∈ toseq.complex.bin0, acc = filterp(emptyprogram, simple.bin0),,, filterp(acc, @e, code.lookupcode(complex.bin0, @e), alltypes)
  \\ assert false report checkt(bin0)assert false report print.length.toseq.complex.bin + print.length.toseq.simple.bin \\
  for sym ∈ toseq.complex.bin, acc = simple.bin ,,, \\ depthfirst(acc, knownsymbols, alltypes, sym)Function depthfirst(acc:program, knownsymbols:program, alltypes:typedict, sym:symbol)program \\
  depthfirst(acc, alltypes, 1, [ sym], acc, code.lookupcode(knownsymbols, sym), sym)

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
 for @e ∈ toseq.roots, acc = empty:seq.symbol ,,, acc + if isconstantorspecial.@e ∨ isabstract.modname.@e then empty:seq.symbol else [ @e]

function uses(p:program, processed:set.symbol, toprocess:set.symbol)set.symbol
 if isempty.toprocess then processed
 else
  let q = asset.for @e ∈ toseq.toprocess, acc = empty:seq.symbol ,,, acc
  + 
  let d = code.lookupcode(p, @e)
   \\ assert not.containspara.d report"has p"+ print.@e + print.d \\
   if isempty.d then constantcode.@e else d
   uses(p, processed ∪ toprocess, q - processed)

function containspara(code:seq.symbol)boolean for e ∈ code, hasparameter = false ,,, hasparameter ∨ isparameter.e