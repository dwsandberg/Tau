module pass2a

use bits

use buildtree

use graph.word

use invertedseq.func

use ipair.func

use ipair.tree.seq.word

use libscope

use opt2

use oseq.int

use passcommon

use real

use seq.arc.word

use seq.cnode

use seq.func

use seq.int

use seq.ipair.func

use seq.ipair.tree.seq.word

use seq.libsym

use seq.mod2desc

use seq.mytype

use seq.parametermap

use seq.pass1result

use seq.program

use seq.rexpand

use seq.seq.cnode

use seq.seq.func

use seq.seq.word

use seq.syminfo

use seq.tree.seq.word

use seq.word

use set.arc.word

use set.int

use set.syminfo

use set.track

use seq.track

use set.word

use stdlib

use tree.seq.word

use seq.seq.ipair.func


5E^2A * 2B + 2F /

function prt(f:seq.func, i:int)seq.word 
 [ EOL]+ mangledname(f_i)+ towords.returntype(f_i)+ print.codetree(f_i)

function filterlib(existing:set.word, f:func)seq.func 
 if mangledname.f in existing then empty:seq.func else [ f]

type track is record tosyminfo:syminfo

function ?(a:track, b:track)ordering mangled.tosyminfo.a ? mangled.tosyminfo.b

function =(a:track, b:track)boolean mangled.tosyminfo.a = mangled.tosyminfo.b

function isoption(w:word)boolean 
 w in"PROFILE FORCEINLINE NOINLINE STATE TESTOPT"

function optdivide(inst:seq.word, i:int)int 
 // look for options at end of instruction // 
  if inst_i ="1"_1 ∧ isoption(inst_(i - 1))then optdivide(inst, i - 2)else i

function addtoprogram(alltypes:set.libtype, map:set.track, p:program, f:word)program 
 if isoption.f 
  then // ignore options // p 
  else let asfunc = find(allfunctions.p, func(0, mytype."", f, tree."X X",""))
  if length.asfunc = 1 
  then // already added // p 
  else let a = findelement(track.syminfoX.f, map)
  if isempty.a 
  then p 
  else let q = tosyminfo(a_1)
  let rt = if hasproto.q then protoreturntype.q else returntype.q 
  let myinst = funcfrominstruction(alltypes, instruction.q, replaceT(parameter.modname.q, returntype.q), length.paratypes.q)
  let instend = optdivide(myinst, length.myinst)
  let options = subseq(myinst, instend, length.myinst)
  if subseq(instruction.q, 1, length.instruction.q - length.options)= [ mangled.q]
  then let fn = func(length.paratypes.q, rt, mangled.q, tree."UNASSIGNED", options)
   let p2 = program(library.p, add(allfunctions.p, encoding.mangledname.fn, fn), callgraph.p, inline.p, 
   if"STATE"_1 in flags.fn then hasstate.p + mangledname.fn else hasstate.p)
   p2 
  else let trz = buildcodetree(length.paratypes.q, subseq(myinst, 1, instend))
  // remove APPLY and unneeded sets // 
  let tr = inline(p, inline.p, dseq.tree."UNASIGNED 1" , empty:seq.tree.seq.word, 1, trz)
  let tr1 = if inst.tr ="STATE"_1 then tr_1 else tr 
  let arcs = asset.calls(mangled.q, tr1)
  let isrecusive = arc(mangled.q, mangled.q)in arcs 
  let tr2 = if isrecusive then tailcall(tr1, mangled.q, length.paratypes.q)else tr1 
  let arcs2 = if isrecusive then asset.calls(mangled.q, tr2)else arcs 
  let flags = fixflags(tr2, length.paratypes.q, if inst.tr ="STATE"_1 then options +"STATE"else options)
  let fn = func(length.paratypes.q, rt, mangled.q, tr2, flags)
  let p2 = program(library.p, add(allfunctions.p, encoding.mangledname.fn, fn), callgraph.p + toseq.arcs2, if isrecusive ∨ not("SIMPLE"_1 in flags ∨"INLINE"_1 in flags)
   then inline.p 
   else inline.p + mangled.q, if"STATE"_1 in flags.fn then hasstate.p + mangledname.fn else hasstate.p)
  @(addtoprogram(alltypes, map), head, p2, toseq.arcs2)

function fixflags(t:tree.seq.word, nopara:int, oldflags:seq.word)seq.word 
 let functyp = if"FORCEINLINE"_1 in oldflags 
   then"INLINE"_1 
   else if"NOINLINE"_1 in oldflags 
   then"NOINLINE"_1 
   else functype(t, nopara)
  toseq(asset.oldflags - asset."SIMPLE INLINE"+ functyp)

function roots(isencoding:set.syminfo, m:mod2desc)set.word 
 if isabstract.modname.m ∨ isprivate.m 
  then empty:set.word 
  else @(+, mangled, empty:set.word, toseq.export.m + toseq(defines.m ∩ isencoding))

function hasErecord(s:syminfo)seq.syminfo 
 if"erecord"_1 in towords.returntype.s then [ s]else empty:seq.syminfo
 
 function lookupfunc(p:program,name:word) func
   lookupfunc(allfunctions.p,name)

Function pass2(r:pass1result) intercode2
 // does inline expansion, finds consts, removes unreaachable functions // 
  let p1 = program(libname(r)_1, invertedseq.dummyfunc, newgraph.empty:seq.arc.word, asset."","")
  let roots = toseq.@(∪, roots.asset.@(+, hasErecord, empty:seq.syminfo, newcode.r), empty:set.word, mods.r)
  let p = @(addtoprogram(alltypes.r, @(+, track, empty:set.track, newcode.r + compiled.r)), identity, p1, roots)
  let s2 = expandinline.p 
  let statechangingfuncs = reachable(complement.callgraph.s2, hasstate.p)∩ nodes.callgraph.s2 
  // only pass on functions that can be reached from roots and are in this library // 
  let g = reachable(callgraph.s2, roots) - asset.@(+, mangled, empty:seq.word, compiled.r)
  // find tail calls and constants // 
  let rr = @(+, findconstandtail(s2, statechangingfuncs), empty:seq.func, toseq.g)
  // assert false report @(+, toword,"", mapping.debuginfoencoding)// 
   convert2(allfunctions.p, rr)

function xor(a:boolean, b:boolean)boolean if a then not.b else b

function findconstandtail(p:program, stateChangingFuncs:set.word, mangledname:word)seq.func 
 // finds constants, discards builtins, and make sure"STATE"is root on state changing functions // 
  let a = codedown.mangledname 
  if length.a > 1 ∧ a_2 ="builtin"
  then empty:seq.func 
  else let f = lookupfunc(allfunctions.p, mangledname)
  let code1 = if"TESTOPT"_1 in flags.f then hoistRecord.codetree.f else hoistRecord.codetree.f 
  let code2 = // remove result record in loop // opt2.code1 
  let code3 = removerecords.code2 
  let q = // if(mangledname in"syminfoinstanceZprocesstypesZmytypeZwordZmytypeZmytypezseqZmytypeZwordzseq")then // 
   inline(p, empty:set.word, dseq.tree."UNASIGNED 1", empty:seq.tree.seq.word, 1, code3)
  // else code3 // 
  // assert not(mangledname = xx_195)report [ mangledname]+ printb(0, code3)+"<<<"+ printb(0, q)> 130 ok let discard = if q = code3 then 0 else encoding.encode(debuginfo.mangledname, debuginfoencoding)// 
  // assert q = code3 ∨ mangledname in"stacktraceZstacktrace"report"inline"+ mangledname // 
  // assert xor(code1 = code2, mangledname in"addtobitstreamZinternalbcZintZbitzbitpackedseqZinternalbc buildcodetreeZbuildtreeZwordzseq siQ7AetypeZprocesstypesZlibtypezsetZlibtype xaddwordseqZpersistantZlinklists2Zwordzseq assigntypesiQ7AesZprocesstypesZlibtypezseq callsZsymbolZsyminfo addconstZpersistantZlinklists2Zwordzseqztree addobject2ZpersistantZlibtypezsetZmytypeZlinklists2Zint")report"X"+ mangledname // 
  let newflags = if"STATE"_1 in flags.f ∨ not(mangledname.f in stateChangingFuncs)
   then flags.f 
   else flags.f +"STATE"
  [ func(nopara.f, returntype.f, mangledname.f, q, newflags)]

/use seq.debuginfo

/type debuginfoencoding is encoding debuginfo

/function hash(a:debuginfo)int hash.toword.a

/type debuginfo is record toword:word

/function =(a:debuginfo, b:debuginfo)boolean toword.a = toword.b

function print(g:graph.word)seq.word @(+, p,"", toseq.arcs.g)

function p(a:arc.word)seq.word [ tail.a]+":"+ head.a

Function getarcs(f:func)seq.arc.word calls(mangledname.f, codetree.f)


function opSUB word {"Q2DZbuiltinZintZint"_1 }

function opRSUB word {"Q2DZbuiltinZrealZreal"_1 }

function isconst(t:tree.seq.word)boolean inst.t in"LIT CRECORD WORD WORDS FREF"

function simplecalcs(label:seq.word, a:int, b:int, l:seq.tree.seq.word)tree.seq.word 
 let inst =  label_1 
  if inst = opRSUB 
  then tree.["LIT"_1, toword.representation(casttoreal.a - casttoreal.b)]
  else if not(between(a, -2147483648, 2147483648)∧ between(b, -2147483648, 2147483648))
  then tree(label, l)
  else if inst = opSUB 
  then tree.["LIT"_1, toword(a - b)]
  else if inst ="Q2BZbuiltinZintZint"_1 
  then tree.["LIT"_1, toword(a + b)]
  else if inst ="Q2FZbuiltinZintZint"_1 ∧ b ≠ 0 
  then tree.["LIT"_1, toword(a / b)]
  else if inst ="Q2AZbuiltinZintZint"_1 
  then tree.["LIT"_1, toword(a * b)]
  else if inst ="EQL"_1 
  then tree.["LIT"_1, if a = b then"1"_1 else"0"_1]
  else if inst ="Q3CQ3CZbuiltinZbitsZint"_1 
  then tree.["LIT"_1, toword.toint(bits.a << b)]
  else if inst ="Q3EQ3EZbuiltinZbitsZint"_1 
  then tree.["LIT"_1, toword.toint(bits.a >> b)]
  else // assert inst in"Q5EZstdlibZintZint BLOCKCOUNTZinternalbcZintZint"report"XY"+ inst // 
  tree(label, l)


Function calls(self:word, t:tree.seq.word)seq.arc.word 
 @(+, calls.self, empty:seq.arc.word, sons.t)+ if inst.t ="FREF"_1 
  then [ arc(self, arg.t)]
  else if inst.t in"WORD WORDS RECORD IDXUC LIT LOCAL PARAM SET FINISHLOOP LOOPBLOCK CONTINUE NOINLINE EQL if CALLIDX PROCESS2 CRECORD STKRECORD"
  then empty:seq.arc.word 
  else // let a = codedown.inst.t if length.a > 1 ∧(a_2 ="builtin")then empty:seq.arc.word else // 
  [ arc(self, inst.t)]

type program is record library:word, allfunctions:invertedseq.func, callgraph:graph.word, inline:set.word, hasstate:seq.word

__________________________

inline expansion

Function expandinline(p:program)program 
 let canidates = @(∪, predecessors.callgraph.p, asset."", toseq.inline.p)
  // canidates will contain functions with just FREF's // 
  let s0 = program(library.p, allfunctions.p, callgraph.p, asset."", hasstate.p)
  let s1 = @(simple3.inline.p, identity, s0, toseq.canidates)
  let usesapply = predecessors(callgraph.s1,"APPLY"_1)
  let s2 = @(simple3(inline.p ∪ asset."APPLY"), identity, s1, toseq.usesapply)
  if isempty.inline.s2 then s2 else expandinline.s2

Function simple3(inline:set.word, p:program, f:word)program 
 let infunc = lookupfunc(p, f)
  let oldarcs = arcstosuccessors(callgraph.p, f)
  let z = @(+, head, empty:set.word, toseq.oldarcs)∩ inline - f 
  if isempty.z ∨"NOINLINE"_1 in flags.infunc 
  then p 
  else // inline may introduce new calls that are not in z so pass full set of possible inline expansions // 
  let t = inline(p, inline, dseq.tree."UNASIGNED 1", empty:seq.tree.seq.word, 1, codetree.infunc)
  let flags = fixflags(t, nopara.infunc, flags.infunc)
  let newfn = func(nopara.infunc, returntype.infunc, f, t, flags)
  let newall = add(allfunctions.p, encoding.f, newfn)
  program(library.p, newall, replacearcs(callgraph.p, oldarcs, asset.getarcs.newfn), if"SIMPLE"_1 in flags ∨"INLINE"_1 in flags then inline.p + f else inline.p,"")


function checksets(s:set.word, t:tree.seq.word)seq.word 
 if inst.t ="SET"_1 
  then checksets(s, t_1)+ checksets(s + arg.t, t_2)
  else if inst.t ="LOCAL"_1 
  then if arg.t in s then""else [ arg.t]
  else if inst.t ="FINISHLOOP"_1 
  then let a = toint.arg(t_1_nosons(t_1))
   @(+, checksets.s,"", subseq(sons(t_1), 1, nosons(t_1) - 1))+ checksets(@(+, toword, s, arithseq(nosons(t_1) - 1, 1, a)), t_2)
  else @(+, checksets(s + arg.t),"", sons.t)

function explodeinline(prg:program, inlinename:set.word, inlinetree:tree.seq.word, simple:boolean, nextset:int, paras:seq.tree.seq.word)tree.seq.word 
 // add sets for complex parameters and then does inline expansion. // 
  if simple 
  then inline(prg, inlinename, dseq.tree."UNASIGNED 1", paras, nextset, inlinetree)
  else let pmap = @(addtoparamatermap, identity, parametermap(empty:seq.tree.seq.word, nextset, empty:seq.ipair.tree.seq.word), paras)
  let a = inline(prg, inlinename, dseq.tree."UNASIGNED 1", paramap.pmap, nextset.pmap, inlinetree)
  @(addsets, identity, a, addnodes.pmap)

type parametermap is record paramap:seq.tree.seq.word, nextset:int, addnodes:seq.ipair.tree.seq.word

function addtoparamatermap(p:parametermap, t:tree.seq.word)parametermap 
 if inst.t in"LIT LOCAL PARAM FREF FREFB WORD"
  then parametermap(paramap.p + t, nextset.p, addnodes.p)
  else parametermap(paramap.p + tree.["LOCAL"_1, toword.nextset.p], nextset.p + 1, addnodes.p + ipair(nextset.p, t))

function addsets(t:tree.seq.word, a:ipair.tree.seq.word)tree.seq.word 
 tree(["SET"_1, toword.index.a], [ value.a, t])

function addlooptosetmap(sets:seq.tree.seq.word, old:int, new:int, numbertoadd:int)seq.tree.seq.word 
 if numbertoadd = 0 
  then sets 
  else let i = numbertoadd - 1 
  addlooptosetmap(addtosetmap(sets,toword(old+i),new + i),old, new, i)
  
  function addtosetmap(sets:seq.tree.seq.word, old:word, new:int)seq.tree.seq.word 
    replace(sets, setvarmapping.old , tree.["LOCAL"_1, toword(new)])
    
function setvarmapping(var:word) int // should change how local vars are mapped. changing from int.var to encoding.var slowed things down 
by have a second // encoding.var

function paraorder boolean true 

function inline(pp:program, inlinename:set.word, sets:seq.tree.seq.word, paramap:seq.tree.seq.word, nextset:int, code:tree.seq.word)tree.seq.word 
 let inst = inst.code 
  if nosons.code = 0 ∧ inst in"LIT FREF FREFB WORD WORDS"
  then code 
  else if inst ="LOCAL"_1 
  then sets_setvarmapping.arg.code 
  else if inst ="PARAM"_1 
  then let i = if paraorder then -1 - toint.arg.code else toint.arg.code
   if i ≤ length.paramap then paramap_i else code 
  else if inst ="CRECORD"_1 
  then code 
  else if inst ="SET"_1 
  then let s1 = inline(pp, inlinename, sets, paramap, nextset + 1, code_1)
   if inst.s1 in"LIT LOCAL PARAM FREF FREFB WORD"∨ inst.s1 ="getaddressZbuiltinZTzseqZint"_1 ∧ inst(s1_1)="LOCAL"_1 ∧ inst(s1_2)="LIT"_1 
   then inline(pp, inlinename, replace(sets, setvarmapping.arg.code, s1), paramap, nextset, code_2)
   else let s2 = inline(pp, inlinename, addtosetmap(sets, arg.code, nextset), paramap, nextset + 1, code_2)
   tree(["SET"_1, toword.nextset], [ s1, s2])
  else if inst.code ="FINISHLOOP"_1 
  then let lb = code_1 
   let firstvar = toint.arg(lb_nosons.lb)
   let noloopvars = nosons.lb - 1 
   let newmap = addlooptosetmap(sets, firstvar, nextset, noloopvars)
   let newlb = tree(label.lb, @(+, inline(pp, inlinename, newmap, paramap, nextset + noloopvars), empty:seq.tree.seq.word, subseq(sons.lb, 1, noloopvars))+ tree.["LIT"_1, toword.nextset])
   tree(label.code, [ newlb, inline(pp, inlinename, newmap, paramap, nextset + noloopvars, code_2)])
  else let l = @(+, inline(pp, inlinename, sets, paramap, nextset), empty:seq.tree.seq.word, sons.code)
  // look for simplifications // 
  if inst ="RECORD"_1 
  then tree(if @(∧, isconst, true, l)then  "CRECORD 0" else label.code, l)
  else if inst ="IDXUC"_1 ∧ inst(l_2)="LIT"_1 
  then let idx = toint.arg(l_2)
   if inst(l_1)="CRECORD"_1 
   then if between(idx, 0, nosons(l_1) - 1)then l_1_(idx + 1)else tree(label.code, l)
   else if inst(l_1)="getaddressZbuiltinZTzseqZint"_1 ∧ inst(l_1_2)="LIT"_1 
   then tree(label.code, [ l_1_1, tree.["LIT"_1, toword(idx + toint.arg(l_1_2))]])
   else tree(label.code, l)
  else if inst ="if"_1 
  then let i2 = inst(l_1)
   if i2 ="LIT"_1 
   then if arg(l_1)="1"_1 then l_2 else l_3 
   else if i2 ="notZbuiltinZboolean"_1 
   then tree(label.code, [ l_1_1, l_3, l_2])
   else tree(label.code, l)
  else if inst in"Q5FZwordzseqZTzseqZint"∧ inst(l_2)="LIT"_1 ∧ inst(l_1)="CRECORD"_1 
  then // only expand when is standard sequence:that is 0 is in first field of record // 
   let cst = l_1 
   let idx = toint.arg(l_2)
   if idx > 0 ∧ idx ≤ nosons.cst - 2 ∧ inst(cst_1)="LIT"_1 ∧ arg(cst_1)="0"_1 
   then cst_(idx + 2)
   else tree(label.code, l)
  else if length.l = 2 ∧ inst(l_2)="LIT"_1 ∧ inst.code ="getaddressZbuiltinZTzseqZint"_1 ∧ arg(l_2)="0"_1 
  then l_1 
  else if inst ="APPLY"_1 ∧(nosons.code ≠ 5 ∨ nosons(l_1)> 2)
  then expandapply(pp, inlinename, nextset, code, l)
  else if inst in inlinename 
  then // inline expansion // 
   if inst ="APPLY"_1 
   then if nosons.code = 5 ∧ checkistypechangeonly(pp, inlinename, arg(l_4), arg(l_3), l_1)
    then inline(pp, inlinename, sets, paramap, nextset, l_2)
    else expandapply(pp, inlinename, nextset, code, l)
   else let f = lookupfunc(pp, inst)
   explodeinline(pp, inlinename, codetree.f,"SIMPLE"_1 in flags.f, nextset, l)
  else if length.l = 2 ∧ inst(l_1)="LIT"_1 ∧ inst(l_2)="LIT"_1 
  then // location after inline expansion so inlining will happen if both sons happen to be LIT's // 
   simplecalcs(label.code, toint.arg(l_1), toint.arg(l_2), l)
  else tree(label.code, l)

function expandapply(pp:program, inlinename:set.word, nextset:int, code:tree.seq.word, l:seq.tree.seq.word)tree.seq.word 
 let term1 = arg(code_(nosons.code - 1))
  let term2 = arg(code_(nosons.code - 2))
  let ptyp = arg(code_nosons.code)
  let p1 = noparamangled.term1 - 2 
  let p2 = noparamangled.term2 - 1 
  let nopara = 2 + p2 + p1 
  assert p2 ≥ 0 report"illformed"+ term1 + term2 + print.lookupfunc(allfunctions.pp, term2)
  let thetree = buildcodetree(nopara, template2(term1, term2, p1, p2, ptyp))
  explodeinline(pp, inlinename, thetree, false, nextset, subseq(l, 1, length.l - 3))

______________

Tailcall

Function tailcall(t:tree.seq.word, self:word)boolean 
 if inst.t ="if"_1 
  then if tailcall(t_2, self)then true else tailcall(t_3, self)
  else if inst.t ="SET"_1 
  then tailcall(t_2, self)
  else if inst.t in"FINISHLOOP"then false else inst.t = self

Function tailcall(t:tree.seq.word, self:word, nopara:int)tree.seq.word 
 if tailcall(t, self)
  then let m = getmaxvar.t + 1 
   let s = @(+, newNode("LOCAL"_1), empty:seq.tree.seq.word, arithseq(nopara, 1, m))
   let plist = @(+, newNode("PARAM"_1), empty:seq.tree.seq.word, if paraorder then arithseq(nopara, -1, -2) else arithseq(nopara,1,1))
   tree("FINISHLOOP 2", [ tree(["LOOPBLOCK"_1, toword(nopara + 1)], plist + newNode("LIT"_1, m)), 
   tailcall(s, self, t)])
  else t

function leftcat(a:seq.tree.seq.word, b:tree.seq.word)seq.tree.seq.word [ b]+ a

function newNode(w:word, i:int)tree.seq.word tree.[w, toword.i]

function tailcall(paramap:seq.tree.seq.word, self:word, t:tree.seq.word)tree.seq.word 
 if inst.t ="if"_1 
  then tree(label.t, [ tailcall(paramap,"nomatch"_1, t_1), tailcall(paramap, self, t_2), tailcall(paramap, self, t_3)])
  else if inst.t ="SET"_1 
  then tree(label.t, [ tailcall(paramap,"nomatch"_1, t_1), tailcall(paramap, self, t_2)])
  else if inst.t = self 
  then tree(["CONTINUE"_1, self], @(+, tailcall(paramap,"nomatch"_1), empty:seq.tree.seq.word, sons.t))
  else if inst.t ="PARAM"_1 
  then paramap_if paraorder then (-1 - toint.arg.t) else toint.arg.t
  else tree(label.t, @(+, tailcall(paramap,"nomatch"_1), empty:seq.tree.seq.word, sons.t))

------paramap_(length.paramap-toint.arg.code + 1)

function getmaxvar(t:tree.seq.word)int 
 @(max, getmaxvar, if inst.t ="SET"_1 
  then toint.arg.t 
  else if inst.t ="LOOPBLOCK"_1 then toint.arg(t_nosons.t)+ nosons.t - 2 else 0, sons.t)

_____________

function noparamangled(a:word)int length.codedown.a - 2

function parainst(i:int)seq.word {"PARAM"+ if paraorder then toword(-1 - i) else toword.i }

function template2(term1:word, term2:word, nopara1:int, nopara2:int, ptyp:word)seq.word 
 // PARA 1 is seq PARA 2 is result LOCAL 10 is result of inner loop LOCAL 3 is seq LOCAL 2 is stk LOCAL 1 is accumulator // 
  // Inner loop LOCAL 6 result LOCAL 7 index LOCAL 5 length of seq // 
  // EQL-Q3DZbuiltinZintZint opGT = Q3EZbuiltinZintZint ADD = Q2BZbuiltinZintZint // 
  let CALLTERM1 = [ term1, toword(2 + nopara1)]
  let CALLTERM2 = [ term2, toword(1 + nopara2)]
  let TERM1PARA = @(+, parainst,"", arithseq(nopara1, 1, 1))
  let TERM2PARA = @(+, parainst,"", arithseq(nopara2, 1, nopara1 + 1))
  {"X"+ parainst(nopara1 + nopara2 + 1)+"LIT 0"+ parainst(nopara1 + nopara2 + 2)+"LIT 1 LOOPBLOCK 4 LOCAL 3 LIT 0 IDXUC 2 FREF"+ ptyp +"Q3DZbuiltinZintZint 2 LOCAL 1 LOCAL 2 LOCAL 3 LIT 3 IDXUC 2 STKRECORD 2 LOCAL 3 LIT 2 IDXUC 2 CONTINUE 3 LOCAL 3 LIT 1 IDXUC 2 LOCAL 1 LIT 1 LIT 6 LOOPBLOCK 3 LOCAL 7 LOCAL 5 Q3EZbuiltinZintZint 2 LOCAL 6"+ TERM2PARA +"LOCAL 3 LIT 0 IDXUC 2 LIT 0 Q3DZbuiltinZintZint 2 LOCAL 3 LOCAL 7 LIT 1 Q2BZbuiltinZintZint 2 IDXUC 2 LOCAL 3 LIT 0 IDXUC 2 LOCAL 3 LOCAL 7 CALLIDX 3 if 3"+ CALLTERM2 + TERM1PARA +"LOCAL 6 LOCAL 8"+ CALLTERM1 +"LOCAL 7 LIT 1 Q2BZbuiltinZintZint 2 CONTINUE 2 SET 8 if 3 FINISHLOOP 2 SET 5 LOCAL 2 LIT 0 Q3DZbuiltinZintZint 2 LOCAL 10 LOCAL 10 LOCAL 2 LIT 0 IDXUC 2 LOCAL 2 LIT 1 IDXUC 2 CONTINUE 3 if 3 SET 10 if 3 FINISHLOOP 2"}

function checkistypechangeonly(prg:program, inlinename:set.word, term1:word, term2:word, term3:tree.seq.word)boolean 
 // check to see if APPLY just does a type change // 
  let q = codedown.term1 
  if length.q = 4 ∧ last(q_2)="seq"_1 ∧ q_1_1 ="+"_1 ∧ subseq(q, 3, length.q)= ["T seq","T"]
  then let f = lookupfunc(prg, term2)
   if nopara.f = 1 ∧ inst.codetree.f in"PARAM"
   then if inst.term3 ="CRECORD"_1 ∧ nosons.term3 = 2 ∧ "LIT 0"= label(term3_1)∧ "LIT 0"= label(term3_1)
    then // let z = [ term1, term2]+ print(term3)assert z in ["Q2BZbitszseqZTzseqZT tobitsZbitsZbit LIT 0 LIT 0 CRECORD 2","Q2BZbitszseqZTzseqZT tobitsZfileioZbyte LIT 0 LIT 0 CRECORD 2","Q2BZalphawordzseqZTzseqZT alphawordZstdlibZword LIT 0 LIT 0 CRECORD 2","Q2BZwordzseqZTzseqZT towordZstdlibZalphaword LIT 0 LIT 0 CRECORD 2","Q2BZalphawordzseqzseqZTzseqZT toalphaseqZstdlibZwordzseq LIT 0 LIT 0 CRECORD 2","Q2BZwordzseqzseqZTzseqZT towordseqZstdlibZalphawordzseq LIT 0 LIT 0 CRECORD 2","Q2BZbytezseqZTzseqZT byteZfileioZint LIT 0 LIT 0 CRECORD 2","Q2BZmytypezseqZTzseqZT mytypeZlibscopeZwordzseq LIT 0 LIT 0 CRECORD 2","Q2BZwordzarczseqZTzseqZT identityZwordzarczseqZT LIT 0 LIT 0 CRECORD 2","Q2BZsyminfozseqZTzseqZT identityZsyminfozseqZT LIT 0 LIT 0 CRECORD 2","Q2BZlibtypezarczseqZTzseqZT identityZlibtypezarczseqZT LIT 0 LIT 0 CRECORD 2","Q2BZbitzseqZTzseqZT bitZbitsZint LIT 0 LIT 0 CRECORD 2"]report"V"+ z // 
     true 
    else // assert false report"Z"+ term1 + term2 + print(term3)// false 
   else false 
  else false

