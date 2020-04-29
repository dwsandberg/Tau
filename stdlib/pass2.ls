Module pass2

use UTF8

use bits

use encoding.seq.char

use seq.char

use deepcopy.intercode

use intercode

use seq.mytype

use real

use stdlib

use otherseq.switch

use seq.switch

use seq.symbol

use set.symbol

use symbol

use seq.arc.word

use set.arc.word

use graph.word

use ipair.seq.word

use seq.seq.word

use deepcopy.tree.seq.word

use seq.ipair.tree.seq.word

use ipair.tree.seq.word

use seq.tree.seq.word

use stack.tree.seq.word

use worddict.tree.seq.word

use tree.seq.word

use set.word

use words

Function pass2(knownsymbols:symbolset, roots:seq.word, compiled:symbolset)intercode
 PROFILE
 .// does inline expansion, finds consts, removes unreaachable functions //
 let p = program(knownsymbols, newgraph.empty:seq.arc.word, empty:set.word,"")
 let x = @(addsymbol, identity, p, roots)
 let s2 = expandinline.x
 let statechangingfuncs = reachable(complement.callgraph.s2, hasstate.x) ∩ nodes.callgraph.s2
  // only pass on functions that can be reached from roots and are in this library //
  let g = reachable(callgraph.s2, roots) - asset.@(+, mangledname, empty:seq.word, toseq.compiled)
  let z = predecessors(callgraph.s2,"APPLY"_1)
   assert isempty.z report"APPLY?" + toseq.z
    // find tail calls and constants //
    // assert false report @(+, listswitchopt(s2, statechangingfuncs),"", toseq.g)//
    let rr = @(+, findconstandtail(s2, statechangingfuncs), empty:seq.symbol, toseq.g)
     // assert false report @(seperator."
&br 
&br", print2,"", rr)// convert2(knownsymbols.x, rr)

function listswitchopt(p:program, stateChangingFuncs:set.word, mangledname:word)seq.word
 // finds constants, discards builtins, and make sure"STATE"is root on state changing functions //
 if mangledname = "STATE"_1 then""
 else
  let a = codedown.mangledname
   if length.a > 1 ∧ a_2 = "builtin"then""
   else
    let f = lookupfunc(knownsymbols.p, mangledname)
    let t = optswitch(mangledname, 0, codetree.f)
     if t = codetree.f then empty:seq.word else [ mangledname]

function findconstandtail(p:program, stateChangingFuncs:set.word, mangledname:word)seq.symbol
 // finds constants, discards builtins, and make sure"STATE"is root on state changing functions //
 if mangledname = "STATE"_1 then empty:seq.symbol
 else
  let a = codedown.mangledname
   if length.a > 1 ∧ a_2 = "builtin"then empty:seq.symbol
   else
    let f = lookupfunc(knownsymbols.p, mangledname)
    let code1 = if false ∧ "TESTOPT"_1 in flags.f then
    let t = optswitch(mangledname, 0, codetree.f)
      // assert t = codetree.f report [ mangledname]// t
    else codetree.f
     // let code1 = if"TESTOPT"_1 in flags.f then hoistRecord.codetree.f else hoistRecord.codetree.f let code2 = //
     // remove result record in loop //
     // opt2.code1 let code3 = removerecords.code2 //
     let q = inline(p, empty:set.word, emptyworddict:worddict.tree.seq.word, empty:seq.tree.seq.word, 1, code1)
     let q2 = if"STATE"_1 in flags.f ∨ not(mangledname.f in stateChangingFuncs)then q
     else tree("STATE", [ q])
      [ changecodetree(f, q2)]

Function print2(t:tree.seq.word)seq.word print(" &br", t)

Function print(indent:seq.word, t:tree.seq.word)seq.word
 @(+, print(indent + "_"),"", sons.t) + indent
 + if(label.t)_1 in "PARAM FREF LIT SET LOCAL"then label.t else label.t + toword.nosons.t

- - - - - - - - - - - - - - - - - - - - - -

function maxvarused(t:tree.seq.word)int
 if inst.t in "SET LOCAL"then toint.arg.t
 else if inst.t = "FINISHLOOP"_1 then maxvarused.t_1
 else if inst.t = "LOOPBLOCK"_1 then
 toint.arg.t_(nosons.t) + nosons.t - 2
 else 0

function optswitch(name:word, k:int, t:tree.seq.word)tree.seq.word
 let s = checkswitch(empty:seq.tree.seq.word, t, t)
  if length.s < 6 then
  tree(label.t, @(+, optswitch(name, max(maxvarused.t, k)), empty:seq.tree.seq.word, sons.t))
  else
   // assert length.s in [ 28, 61, 26, 23, 22, 21, 18, 16, 15, 17, 14, 12, 11, 13, 10]report"K"+ toword.length.s //
   // assert false report @(+, print,"", s)//
   assert getmaxvar.t ≥ k report"KL" + toword.getmaxvar.t + toword.k + name
   let key = keyvalue.last.s
   let default = keycode.last.s
   let var = toword(getmaxvar.t + 1)
   let lower = switchorderkey.s_1 - 2
   let upper = switchorderkey.s_(length.s - 1) + 2
   let firstvalue = [ tree.["LIT"_1, toword.min(switchorderkey.s_1 - 1, 0)]]
   let r = tree("FINISHLOOP"
   , [ tree("LOOPBLOCK", [ key, tree("LIT" + var)]), buildswitchcode(s, tree("LOCAL" + var), 1, length.s - 1, default, tree("CONTINUE", firstvalue), lower, upper)])
    // assert false report print2.r // r

function checkswitch(start:seq.tree.seq.word, key:tree.seq.word, t:tree.seq.word)seq.switch
 if subseq(label.t, 1, 1) = "if"
 ∧ label.t_1 in ["Q3DZbuiltinZintZint","inZwordzseqZTZTzseq","inZintzseqZTZTzseq"]
 ∧ (label.t_1_2)_1 in "WORD WORDS LIT CRECORD"
 ∧ (length.start = 0 ∨ key = t_1_1)then
 checkswitch(start + t_1_2 + t_2, t_1_1, t_3)
 else if length.start > 0 then buildswitchlist(start, 1, empty:seq.switch) + [ switch(t, key)]
 else empty:seq.switch

type switch is record keycode:tree.seq.word, keyvalue:tree.seq.word

function switchorderkey(s:switch)int
 if(label.keyvalue.s)_1 = "WORD"_1 then valueofencoding.asencoding.(label.keyvalue.s)_2
 else toint.(label.keyvalue.s)_2

function ?(a:switch, b:switch)ordering switchorderkey.a ? switchorderkey.b

function print(s:switch)seq.word
 " &br bbb" + toword.switchorderkey.s + print.keyvalue.s + print.keycode.s

function buildswitchlist(t:seq.tree.seq.word, i:int, result:seq.switch)seq.switch
 if i > length.t then result
 else
  let label = label.t_i
   if label_1 in "WORD LIT"then
   buildswitchlist(t, i + 2, setinsert(result, switch(t_(i + 1), t_i)))
   else if label_1 in "WORDS"then
   if label_3 = "0"_1 then
    // handle empty seq //
     let more = empty:seq.switch
      buildswitchlist(t, i + 2, result)
    else
     let treelist = @(+, tree, empty:seq.tree.seq.word, @(+, +."WORD", empty:seq.seq.word, subseq(label, 2, length.label)))
      buildswitchlist(t, i + 2, findfirst(result, t_(i + 1), treelist, 1, false))
   else
    // CRECORD //
    // assert false report print.t_i //
    buildswitchlist(t, i + 2, findfirst(result, t_(i + 1), subseq(sons.t_i, 3, nosons.t_i), 3, false))

function findfirst(result:seq.switch, code:tree.seq.word, sons:seq.tree.seq.word, i:int, found:boolean)seq.switch
 if i > length.sons then result
 else
  let first = sons_i
  let try = setinsert(result, switch(code, sons_i))
   if length.result = length.try then // key is already present // findfirst(result, code, sons, i + 1, false)
   else findfirst(try, if not.found then tree("CONTINUE", [ first])else code, sons, i + 1, true)

function buildswitchcode(s:seq.switch, key:tree.seq.word, f:int, t:int, default:tree.seq.word, defaultcontinue:tree.seq.word, lower:int, upper:int)tree.seq.word
 let EQL ="Q3DZbuiltinZintZint"
 let opGT ="Q3EZbuiltinZintZint"
 let j =(f + t) / 2
  assert between(j, 1, length.s)report [ toword.j, toword.f, toword.t, toword.length.s]
  let defaultcode = if j = 1 then default else defaultcontinue
  let order = switchorderkey.s_j
   if f = t then
   if order + 1 = upper ∧ order - 1 = lower then keycode.s_j
    else tree("if", [ tree(EQL, [ key, keyvalue.s_j]), keycode.s_j, defaultcode])
   else
    let a = if j = f then buildswitchcode(s, key, f, f, default, defaultcontinue, lower, upper)
    else
     tree("if"
     , [ tree(opGT, [ keyvalue.s_j, key]), buildswitchcode(s, key, f, j - 1, default, defaultcontinue, lower, order), keycode.s_j])
     tree("if", [ tree(opGT, [ key, keyvalue.s_j]), buildswitchcode(s, key, j + 1, t, default, defaultcontinue, order, t), a])

- - - - - - - - - - - - - - - - - - - - - - - -

function paratree(i:int)tree.seq.word tree("PARAM" + toword.i)

function addsymbol(p:program, mangledname:word)program
 let caller = lookupsymbol(knownsymbols.p, mangledname)
  if isdefined.caller ∧ label.codetree.caller = "default"then
  let startindex = if(src.caller)_1 = "parsedfunc"_1 then toint.(src.caller)_2 + 3 else 1
   let treecode = subseq(src.caller, startindex, length.src.caller - length.flags.caller)
    if length.src.caller > 0 ∧ last.src.caller = "EXTERNAL"_1 then
    program(replace(knownsymbols.p, changecodetree(caller, tree."EXTERNAL")), callgraph.p, inline.p, if"STATE"_1 in flags.caller then hasstate.p + mangledname.caller else hasstate.p)
    else
     let tr0 = buildcodetreeX(false, empty:stack.tree.seq.word, 1, treecode)
     let tr = inline(p, inline.p, emptyworddict:worddict.tree.seq.word, empty:seq.tree.seq.word, 1, if label.tr0 = "STATE"then tr0_1 else tr0)
     let tr2 = tailcall(tr, mangledname.caller, nopara.caller)
     let calls3 = asset.calls.tr2
     let isrecusive = mangledname.caller in calls3
     let newsym = changecodetree(caller, tr2)
     let flags = flags.newsym
     let newp = program(replace(knownsymbols.p, newsym)
     , callgraph.p + @(+, arc.mangledname.caller, empty:seq.arc.word, toseq.calls3)
     , if isrecusive ∨ not("SIMPLE"_1 in flags ∨ "INLINE"_1 in flags)then
     inline.p
     else inline.p + mangledname.newsym
     , if"STATE"_1 in flags ∨ inst.tr0 = "STATE"_1 then
     hasstate.p + mangledname.newsym
     else hasstate.p)
      @(addsymbol, identity, newp, toseq(calls3 - "APPLY"_1))
  else p

function buildcodetree(src:seq.word)tree.seq.word
   buildcodetreeX(false, empty:stack.tree.seq.word, 1, src)
   
 
       
   
function buildcodetreeX(hasstate:boolean, stk:stack.tree.seq.word, i:int, src:seq.word)tree.seq.word
 if i > length.src then
 assert length.toseq.stk > 0 report"STACK ISSUE" + src
  let top2 = top.stk
   if hasstate then tree("STATE", [ top2])else top2
 else
  let name = src_i
   if name in "builtinZinternal1Zwordzseq builtinZinternal1Zinternal1"then buildcodetreeX(hasstate, stk, i + 1, src)
   else if name in "if "then
      let args=top(stk,3)
      let t=tree("BLOCK 3",   [tree( "BR",[args_1,tree."LIT 2",tree."LIT 3"] ),
      tree("EXITBLOCK",[args_2]),tree("EXITBLOCK",[args_3])])
      buildcodetreeX(hasstate, push(pop(stk, 3), t), i + 1, src)
   else if name in "CALLIDX"then
   let specialnopara = 3
     buildcodetreeX(hasstate, push(pop(stk, specialnopara), tree([ name], top(stk, specialnopara))), i + 1, src)
    else if name in "IDXUC"then
   buildcodetreeX(hasstate, push(pop(stk, 2), tree([ name], top(stk, 2))), i + 1, src)
   else if name = "SET"_1 then
   buildcodetreeX(hasstate, push(pop(stk, 2), tree(subseq(src, i, i + 1), top(stk, 2))), i + 2, src)
   else if name in "LIT PARAM LOCAL WORD"then
   buildcodetreeX(hasstate, push(stk, tree.subseq(src, i, i + 1)), i + 2, src)
   else if name = "FREF"_1 then
   // let sym = lookupfunc(knownsymbols, src_(i + 1))//
    buildcodetreeX(hasstate, push(stk, tree.subseq(src, i, i + 1)), i + 2, src)
   else if name = "DEFINE"_1 then 
    assert false report "here define"
   buildcodetreeX(hasstate, stk, i + 2, src)
   else  if name in "RECORD APPLY LOOPBLOCK STKRECORD CONTINUE FINISHLOOP CRECORD BLOCK EXITBLOCK BR"then
     assert not(src_(i+1)="LIT"_1) report "KKK"+name+src
   let size = toint.src_(i + 1)
     assert length.toseq.stk ≥ size report"stack problem APPLY/RECORD" + src
      buildcodetreeX(hasstate, push(pop(stk, size), tree(subseq(src, i, i + 1), top(stk, size))), i + 2, src)
   else // if name = "PRECORD"_1 then
   let size = toint.src_(i + 1)
    let s = top(stk, size)
    let b = tree("process2ZbuiltinZint", [ tree("RECORD", subseq(s, size - 3, size) + subseq(s, 1, size - 4))])
     buildcodetreeX(hasstate, push(pop(stk, size), b), i + 2, src)
   else // if name = "WORDS"_1 then
   let size = toint.src_(i + 1)
     buildcodetreeX(hasstate, push(stk, tree.subseq(src, i, i + size + 1)), i + size + 2, src)
   else if name = "COMMENT"_1 then
   let size = toint.src_(i + 1)
     buildcodetreeX(hasstate, stk, i + size + 2, src)
   else if name in "STATEZinternal1Zinternal1"then buildcodetreeX(true, stk, i + 1, src)
   else
    let p = handlelocalandpara.name
    let nopara = index.p
     assert length.toseq.stk ≥ nopara report"stack problem" + name
      buildcodetreeX(hasstate, push(pop(stk, nopara), tree(value.p, top(stk, nopara))), i + 1, src)

function handlelocalandpara(w:word)ipair.seq.word
 let charmajorseparator = // Z // char.90
 let l = decodeword.w
 let nopara = @(+, count.charmajorseparator, -1, l)
  if nopara ≠ 0 then ipair(nopara, [ w])
  else if subseq(l, length.l - 4, length.l) = decodeword."zpara"_1 then
  let j = findindex(charmajorseparator, l)
    ipair(0,"PARAM" + encodeword.subseq(l, j + 1, length.l - 5))
  else if subseq(l, length.l - 5, length.l) = decodeword."Zlocal"_1 then
  ipair(0,"LOCAL" + removeQ(subseq(l, 1, length.l - 6), 1, empty:seq.char))
  else ipair(nopara, [ w])

function count(val:char, i:char)int if val = i then 1 else 0

function removeQ(l:seq.char, i:int, w:seq.char)word
 let charQ = char.81
  if i > length.l then encodeword.w
  else if l_i = charQ then
  assert i + 2 ≤ length.l report"format problem with removeQ for" + encodeword.l
   let first = hexvalue.l_(i + 1)
   let t = first * 16 + hexvalue.l_(i + 2)
    if first > 0 then removeQ(l, i + 3, w + char.t)
    else
     let t1 =((t * 16 + hexvalue.l_(i + 3)) * 16 + hexvalue.l_(i + 4))
     * 16
     + hexvalue.l_(i + 5)
      removeQ(l, i + 6, w + char.t1)
  else removeQ(l, i + 1, w + l_i)

function hexvalue(i:char)int
 if between(toint.i, 48, 57)then toint.i - 48 else toint.i - 65 + 10

Function calls(t:tree.seq.word)seq.word
 @(+, calls, empty:seq.word, sons.t)
 + if inst.t = "FREF"_1 then [ arg.t]
 else if inst.t in "WORD WORDS RECORD IDXUC LIT LOCAL PARAM SET DEFINE FINISHLOOP LOOPBLOCK CONTINUE NOINLINE EQL if CALLIDX  CRECORD STKRECORD TESTOPT
 BR EXITBLOCK BLOCK"then
 empty:seq.word
 else [ inst.t]

Function calls(self:word, t:tree.seq.word)seq.arc.word
 @(+, calls.self, empty:seq.arc.word, sons.t)
 + if inst.t = "FREF"_1 then [ arc(self, arg.t)]
 else if inst.t in "WORD WORDS RECORD IDXUC LIT LOCAL PARAM SET DEFINE FINISHLOOP LOOPBLOCK CONTINUE NOINLINE EQL if CALLIDX  CRECORD STKRECORD TESTOPT
  BR EXITBLOCK BLOCK"then
 empty:seq.arc.word
 else
  // let a = codedown.inst.t if length.a > 1 ∧(a_2 ="builtin")then empty:seq.arc.word else //
  [ arc(self, inst.t)]

function opSUB word"Q2DZbuiltinZintZint"_1

function opRSUB word"Q2DZbuiltinZrealZreal"_1

function isconst(t:tree.seq.word)boolean inst.t in "LIT CRECORD WORD WORDS FREF"

function simplecalcs(label:seq.word, a:int, b:int, l:seq.tree.seq.word)tree.seq.word
 TESTOPT
 .
 let inst = label_1
  if inst = opRSUB then tree.["LIT"_1, toword.representation(casttoreal.a - casttoreal.b)]
  else if not(between(a, -2147483648, 2147483648) ∧ between(b, -2147483648, 2147483648))then tree(label, l)
  else if inst = opSUB then tree.["LIT"_1, toword(a - b)]
  else if inst = "Q2BZbuiltinZintZint"_1 then tree.["LIT"_1, toword(a + b)]
  else if inst = "Q2FZbuiltinZintZint"_1 then
  if b = 0 then tree(label, l)else tree.["LIT"_1, toword(a / b)]
  else if inst = "Q2AZbuiltinZintZint"_1 then tree.["LIT"_1, toword(a * b)]
  else if inst = "Q3DZbuiltinZintZint"_1 then
  tree.["LIT"_1, if a = b then"1"_1 else"0"_1]
  else if inst = "Q3CQ3CZbuiltinZbitsZint"_1 then tree.["LIT"_1, toword.toint(bits.a << b)]
  else if inst = "Q3EQ3EZbuiltinZbitsZint"_1 then tree.["LIT"_1, toword.toint(bits.a >> b)]
  else tree(label, l)

type program is record knownsymbols:symbolset, callgraph:graph.word, inline:set.word, hasstate:seq.word

__________________________

inline expansion

Function expandinline(p:program)program
 let canidates = @(∪, predecessors.callgraph.p, asset."", toseq.inline.p)
  // canidates will contain functions with just FREF's //
  let s0 = program(knownsymbols.p, callgraph.p, asset."", hasstate.p)
  let s1 = @(simple3.inline.p, identity, s0, toseq.canidates)
  let usesapply = predecessors(callgraph.s1,"APPLY"_1)
  let s2 = @(simple3(inline.p ∪ asset."APPLY"), identity, s1, toseq.usesapply)
   if isempty.inline.s2 then s2 else expandinline.s2

Function simple3(inline:set.word, p:program, f:word)program
 let infunc = lookupfunc(knownsymbols.p, f)
 let oldarcs = arcstosuccessors(callgraph.p, f)
 let z = @(+, head, empty:set.word, toseq.oldarcs) ∩ inline - f
  if isempty.z then p
  else
   // inline may introduce new calls that are not in z so pass full set of possible inline expansions //
   let t = inline(p, inline, emptyworddict:worddict.tree.seq.word, empty:seq.tree.seq.word, 1, codetree.infunc)
   let newsymbol = changecodetree(infunc, t)
   let newknown = replace(knownsymbols.p, newsymbol)
   let flags = flags.newsymbol
    program(newknown, replacearcs(callgraph.p, oldarcs, asset.calls(f, t)), if"SIMPLE"_1 in flags ∨ "INLINE"_1 in flags then inline.p + f
    else inline.p,"")

function explodeinline(prg:program, inlinename:set.word, inlinetree:tree.seq.word, simple:boolean, nextset:int, paras:seq.tree.seq.word)tree.seq.word
 // add sets for complex parameters and then does inline expansion. //
 if simple then inline(prg, inlinename, emptyworddict:worddict.tree.seq.word, paras, nextset, inlinetree)
 else
  let pmap = @(addtoparamatermap, identity, parametermap(empty:seq.tree.seq.word, nextset, empty:seq.ipair.tree.seq.word), paras)
  let a = inline(prg, inlinename, emptyworddict:worddict.tree.seq.word, paramap.pmap, nextset.pmap, inlinetree)
   @(addsets, identity, a, addnodes.pmap)

type parametermap is record paramap:seq.tree.seq.word, nextset:int, addnodes:seq.ipair.tree.seq.word

function addtoparamatermap(p:parametermap, t:tree.seq.word)parametermap
 if inst.t in "LIT LOCAL PARAM FREF FREFB WORD WORDS"then
 parametermap(paramap.p + t, nextset.p, addnodes.p)
 else
  parametermap(paramap.p + tree.["LOCAL"_1, toword.nextset.p], nextset.p + 1, addnodes.p + ipair(nextset.p, t))

function addsets(t:tree.seq.word, a:ipair.tree.seq.word)tree.seq.word
 tree(["SET"_1, toword.index.a], [ value.a, t])

function addlooptosetmap(sets:worddict.tree.seq.word, old:int, new:int, numbertoadd:int)worddict.tree.seq.word
 if numbertoadd = 0 then sets
 else
  let i = numbertoadd - 1
   addlooptosetmap(addtosetmap(sets, toword(old + i), new + i), old, new, i)

function addtosetmap(sets:worddict.tree.seq.word, old:word, new:int)worddict.tree.seq.word
 replace(sets, old, tree.["LOCAL"_1, toword.new])

function inline(pp:program, inlinename:set.word, sets:worddict.tree.seq.word, paramap:seq.tree.seq.word, nextset:int, code:tree.seq.word)tree.seq.word
 let inst = inst.code
  if nosons.code = 0 ∧ inst in "LIT FREF FREFB WORD WORDS"then code
  else if inst = "LOCAL"_1 then lookup(sets, arg.code)_1
  else if inst = "PARAM"_1 then
  let i = toint.arg.code
    assert i > 0 report"PARAM Problem" + print.code
     if i ≤ length.paramap then paramap_i else code
  else if inst = "CRECORD"_1 then code
  else if inst = "SET"_1 then
  let s1 = inline(pp, inlinename, sets, paramap, nextset + 1, code_1)
    if inst.s1 in "LIT LOCAL PARAM FREF FREFB WORD"
    ∨ inst.s1 = "getaddressZbuiltinZTzseqZint"_1 ∧ inst.s1_1 = "LOCAL"_1
    ∧ inst.s1_2 = "LIT"_1 then
    inline(pp, inlinename, replace(sets, arg.code, s1), paramap, nextset, code_2)
    else
     let s2 = inline(pp, inlinename, addtosetmap(sets, arg.code, nextset), paramap, nextset + 1, code_2)
    // if  inst.s2="BLOCK"_1 then
       tree(label.s2,[tree(["SET"_1, toword.nextset], [ s1,  s2_1])])
     else //
      tree(["SET"_1, toword.nextset], [ s1, s2])
  else if inst.code = "FINISHLOOP"_1 then
  let lb = code_1
   let firstvar = toint.arg.lb_(nosons.lb)
   let noloopvars = nosons.lb - 1
   let newmap = addlooptosetmap(sets, firstvar, nextset, noloopvars)
   let newlb = tree(label.lb
   , @(+, inline(pp, inlinename, newmap, paramap, nextset + noloopvars), empty:seq.tree.seq.word, subseq(sons.lb, 1, noloopvars))
   + tree.["LIT"_1, toword.nextset])
    tree(label.code, [ newlb, inline(pp, inlinename, newmap, paramap, nextset + noloopvars, code_2)])
  else
   let l = @(+, inline(pp, inlinename, sets, paramap, nextset), empty:seq.tree.seq.word, sons.code)
    // look for simplifications //
    if inst = "RECORD"_1 then
    let insts = @(+, inst, empty:set.word, l)
      if isempty(insts - asset."LIT CRECORD WORD WORDS FREF")then
      if length.l > 2 ∧ label.l_1 = "LIT 0"
       ∧ inst.l_2 = "LIT"_1
       ∧ arg.l_2 = toword(length.l - 2)
       ∧ insts = asset."WORD LIT"
       ∧ toseq.@(+, inst, empty:set.word, subseq(l, 3, length.l)) = "WORD"then
       // assert length.l > 3 &or decode(arg.l_3)_1 > 75 &or arg.l_3 in"
&br, IDXUC HASH INLINE HERe HELLO"report"HERe"+ print.code + @(+, toword,"", decode.arg.l_3)//
        tree.@(+, arg,"WORDS" + arg.l_2, subseq(l, 3, length.l))
       else tree("CRECORD", l)
      else tree(label.code, l)
    else if inst = "IDXUC"_1 ∧ inst.l_2 = "LIT"_1 then
    let idx = toint.arg.l_2
      if inst.l_1 = "CRECORD"_1 then
      if between(idx, 0, nosons.l_1 - 1)then l_1_(idx + 1)
       else tree(label.code, l)
      else if inst.l_1 = "getaddressZbuiltinZTzseqZint"_1 ∧ inst.l_1_2 = "LIT"_1 then
      tree(label.code, [ l_1_1, tree.["LIT"_1, toword(idx + toint.arg.l_1_2)]])
      else tree(label.code, l)
    else if inst = "if"_1 then
    let i2 = inst.l_1
      if i2 = "LIT"_1 then
      if arg.l_1 = "1"_1 then l_2 else l_3
      else if i2 = "notZbuiltinZboolean"_1 then tree(label.code, [ l_1_1, l_3, l_2])
      else tree(label.code, l)
    else if inst in "mergeZwordsZwordzseq" ∧ inst.l_1 = "WORDS"_1 then
    // assert false report"merge"+ label(l_1)//
     tree("WORD" + merge.subseq(label.l_1, 3, length.label.l_1))
    else if inst = "Q2BZwordzseqZTzseqZTzseq"_1 ∧ inst.l_1 = "WORDS"_1
    ∧ inst.l_2 = "WORDS"_1 then
    let cat = subseq(label.l_1, 3, length.label.l_1)
     + subseq(label.l_2, 3, length.label.l_2)
      tree("WORDS" + toword.length.cat + cat)
    else if inst = "decodeZcharzseqzencodingZTzerecordZTzencoding"_1 ∧ inst.l_2 = "WORD"_1
    ∧ inst.l_1 = "wordencodingZwords"_1 then
    let charseq = decodeword.arg.l_2
      tree("CRECORD", @(+, treelit, empty:seq.tree.seq.word, [ char.0, char.length.charseq] + charseq))
    else if inst in "Q5FZwordzseqZTzseqZint" ∧ inst.l_2 = "LIT"_1
    ∧ inst.l_1 = "WORDS"_1 then
    let cst = l_1
     let idx = toint.arg.l_2
      if idx > 0 ∧ idx ≤ toint.arg.l_1 then
      tree("WORD" + (label.l_1)_(idx + 2))
      else tree(label.code, l)
    else if inst = "APPLY"_1 ∧ (nosons.code ≠ 5 ∨ nosons.l_1 > 2)then
    expandapply(pp, inlinename, nextset, code, l)
    else if inst in inlinename then
    // inline expansion //
     if inst = "APPLY"_1 then
     if nosons.code = 5 ∧ checkistypechangeonly(pp, inlinename, arg.l_4, arg.l_3, l_1)then
      inline(pp, inlinename, sets, paramap, nextset, l_2)
      else expandapply(pp, inlinename, nextset, code, l)
     else
      let f = lookupfunc(knownsymbols.pp, inst)
       explodeinline(pp, inlinename, codetree.f,"SIMPLE"_1 in flags.f, nextset, l)
    else if length.l = 2 ∧ inst.l_2 = "LIT"_1 then
    if inst.l_1 = "LIT"_1 then
     // location after inline expansion so inlining will happen if both sons happen to be LIT's //
      simplecalcs(label.code, toint.arg.l_1, toint.arg.l_2, l)
     else if inst.l_1 = "CRECORD"_1 then
     // only expand when is standard sequence:that is 0 is in first field of record //
      let cst = l_1
      let idx = toint.arg.l_2
       if idx > 0 ∧ idx ≤ nosons.cst - 2
       ∧ inst.cst_1 = "LIT"_1
       ∧ arg.cst_1 = "0"_1 then
       let c = codedown.inst
         if c_1 = "_" ∧ last.c_2 = "seq"_1
         ∧ c_3 = "T seq"
         ∧ c_4 = "int"then
         cst_(idx + 2)
         else tree(label.code, l)
       else tree(label.code, l)
     else if inst.code = "getaddressZbuiltinZTzseqZint"_1 ∧ arg.l_2 = "0"_1 then
     l_1
     else tree(label.code, l)
    else if inst = "makerealZUTF8Zwordzseq"_1 ∧ inst.l_1 = "WORDS"_1 then
    tree.["LIT"_1, toword.representation.makereal.subseq(label.l_1, 3, length.label.l_1)]
    else tree(label.code, l)

function treelit(c:char)tree.seq.word tree("LIT" + toword.toint.c)

function expandapply(pp:program, inlinename:set.word, nextset:int, code:tree.seq.word, l:seq.tree.seq.word)tree.seq.word
 let term1 = arg.code_(nosons.code - 1)
 let term2 = arg.code_(nosons.code - 2)
 let ptyp = arg.code_(nosons.code)
 let p1 = noparamangled.term1 - 2
 let p2 = noparamangled.term2 - 1
 let nopara = 2 + p2 + p1
  assert p2 ≥ 0 report"illformed" + term1 + term2 + print.lookupfunc(knownsymbols.pp, term2)
   // let thetree = buildcodetree(nopara, template2(term1, term2, p1, p2, ptyp))let z = @(+, identity, knownsymbols.pp, testx)//
   let thetree = buildcodetree.template2(term1, term2, p1, p2, ptyp)
    explodeinline(pp, inlinename, thetree, false, nextset, subseq(l, 1, length.l - 3))

______________

Tailcall

Function tailcall(self:word,t:tree.seq.word)boolean 
// if inst.t="EXITBLOCK"_1 &and nosons.t=1  then //
if inst.t="EXITBLOCK"_1    then
  tailcall(self,t_1)
else if inst.t="BLOCK"_1 then
   @(&or, tailcall(self), false, sons.t) 
  else if inst.t = "SET"_1 then tailcall(self,t_2)
 else if inst.t in "FINISHLOOP"then false else inst.t = self

Function tailcall(t:tree.seq.word, self:word, nopara:int)tree.seq.word
 if tailcall( self,t)then
 let m = getmaxvar.t + 1
  let s = @(+, newNode("LOCAL"_1), empty:seq.tree.seq.word, arithseq(nopara, 1, m))
  let plist = @(+, newNode("PARAM"_1), empty:seq.tree.seq.word, arithseq(nopara, 1, 1))
   tree("FINISHLOOP 2"
   , [ tree(["LOOPBLOCK"_1, toword(nopara + 1)], plist + newNode("LIT"_1, m)), tailcall(s, self, t)])
 else t

/function leftcat(a:seq.tree.seq.word, b:tree.seq.word)seq.tree.seq.word [ b] + a

function newNode(w:word, i:int)tree.seq.word tree.[ w, toword.i]



function tailcall(paramap:seq.tree.seq.word, self:word, t:tree.seq.word)tree.seq.word
 // if inst.t="BLOCK"_1  &or (inst.t="EXITBLOCK"_1 &and nosons.t=1) then //
 if inst.t="BLOCK"_1  &or (inst.t="EXITBLOCK"_1 ) then 
  tree(label.t,@(+, tailcall(paramap,self), empty:seq.tree.seq.word, sons.t))
 else if inst.t = "SET"_1 then
 tree(label.t, [ tailcall(paramap,"nomatch"_1, t_1), tailcall(paramap, self, t_2)])
 else if inst.t = self then
 tree(["CONTINUE"_1, self], @(+, tailcall(paramap,"nomatch"_1), empty:seq.tree.seq.word, sons.t))
 else if inst.t = "PARAM"_1 then paramap_(toint.arg.t)
 else
  tree(label.t, @(+, tailcall(paramap,"nomatch"_1), empty:seq.tree.seq.word, sons.t))

- - - - - - paramap_(length.paramap - toint.arg.code + 1)

function getmaxvar(t:tree.seq.word)int
 @(max
 , getmaxvar
 , if inst.t in "SET LOCAL"then toint.arg.t
 else if inst.t = "LOOPBLOCK"_1 then
 toint.arg.t_(nosons.t) + nosons.t - 2
 else 0
 , sons.t)

_____________

function noparamangled(a:word)int length.codedown.a - 2

function parainst(i:int)seq.word"PARAM" + toword.i

function template2(term1:word, term2:word, nopara1:int, nopara2:int, ptyp:word)seq.word
 // PARA 1 is seq PARA 2 is result LOCAL 10 is result of inner loop LOCAL 3 is seq LOCAL 2 is stk LOCAL 1 is accumulator //
 // Inner loop LOCAL 6 result LOCAL 7 index LOCAL 5 length of seq //
 // EQL - Q3DZbuiltinZintZint opGT = Q3EZbuiltinZintZint ADD = Q2BZbuiltinZintZint //
 let CALLTERM1 = [ term1]
 let CALLTERM2 = [ term2]
 let TERM1PARA = @(+, parainst,"", arithseq(nopara1, 1, 1))
 let TERM2PARA = @(+, parainst,"", arithseq(nopara2, 1, nopara1 + 1))
  parainst(nopara1 + nopara2 + 1) + "LIT 0" + parainst(nopara1 + nopara2 + 2)
  + "LIT 1 LOOPBLOCK 4 LOCAL 3 LIT 0 IDXUC FREF"
  + ptyp
  + "Q3DZbuiltinZintZint LOCAL 1 LOCAL 2 LOCAL 3 LIT 3 IDXUC STKRECORD 2 LOCAL 3 LIT 2 IDXUC CONTINUE 3 LOCAL 3 LIT 1 IDXUC LOCAL 1 LIT 1 LIT 6 LOOPBLOCK 3 LOCAL 7 LOCAL 5 Q3EZbuiltinZintZint LOCAL 6"
  + TERM2PARA
  + "LOCAL 3 LIT 0 IDXUC LIT 0 Q3DZbuiltinZintZint LOCAL 3 LOCAL 7 LIT 1 Q2BZbuiltinZintZint 
  IDXUC LOCAL 3 LIT 0 IDXUC LOCAL 3 LOCAL 7 CALLIDX if"
  + CALLTERM2
  + TERM1PARA
  + "LOCAL 6 LOCAL 8"
  + CALLTERM1
  + "LOCAL 7 LIT 1 Q2BZbuiltinZintZint CONTINUE 2 SET 8 if FINISHLOOP 2 SET 5 
  LOCAL 2 LIT 0 Q3DZbuiltinZintZint LOCAL 10 LOCAL 10 LOCAL 2 LIT 0 IDXUC LOCAL 2 LIT 1 IDXUC CONTINUE 3 if 
  SET 10 if FINISHLOOP 2"



function checkistypechangeonly(prg:program, inlinename:set.word, term1:word, term2:word, term3:tree.seq.word)boolean
 // check to see if APPLY just does a type change //
 let q = codedown.term1
  if length.q = 4 ∧ last.q_2 = "seq"_1
  ∧ q_1_1 = "+"_1
  ∧ subseq(q, 3, length.q) = ["T seq","T"]then
  let f = lookupfunc(knownsymbols.prg, term2)
    if nopara.f = 1 ∧ inst.codetree.f in "PARAM"
    ∧ not("NOINLINE"_1 in flags.f)then
    if inst.term3 = "CRECORD"_1 ∧ nosons.term3 = 2
     ∧ "LIT 0" = label.term3_1
     ∧ "LIT 0" = label.term3_1 then
     true
     else // assert false report"Z"+ term1 + term2 + print(term3)// false
    else false
  else false

function print(a:arc.word)seq.word [ tail.a,":"_1, head.a]