module pass2a

use buildtree

use constant

use graph.int

use libscope

use options.pass1result

use options.seq.func

use options.tree.cnode

use oseq.int

use passcommon

use real

use seq.arc.int

use seq.cnode

use seq.func

use seq.int

use seq.libsym

use seq.mod2desc

use seq.mytype

use seq.rexpand

use seq.seq.cnode

use seq.seq.word

use seq.syminfo

use seq.tree.cnode

use seq.word

use set.arc.int

use set.int

use set.syminfo

use set.word

use stdlib

use tree.cnode

function opADD word {"ADD"_1 }

function opSUB word {"Q2DZbuiltinZintZint"_1 }

function opRSUB word {"Q2DZbuiltinZrealZreal"_1 }

function opGT word {"Q3EZbuiltinZintZint"_1 }

function opEQL word {"Q3DZbuiltinZintZint"_1 }

/Function findconst(f:func)func replacecodetree(f, findconst.codetree.f)

Function findconst(t:tree.cnode)tree.cnode 
 // We assume that ENCODE 1 is the word encodings.THIS IS NO LONGER TRUE! // 
  if nosons.t = 0 
  then t 
  else let l = @(+, findconst, empty:seq.tree.cnode, sons.t)
  let inst = if inst.label.t ="CALL"_1 ∧ arg.label.t ="Q5FZwordzseqZTzseqZint"_1 
   then arg.label.t 
   else inst.label.t 
  if inst ="RECORD"_1 
  then let z2 = asconst(l, 1,"")
   if isempty.z2 
   then tree(label.t, l)
   else tree.cnode("CONST"_1, addconst("RECORD"+ [ toword(length.z2 / 2)]+ z2), 0)
  else if inst in"encodeword encodewordZstdlibZintzseq"∧ inst.label(t_1)="CONST"_1 
  then let cst = constantmapping_toint.arg.label(t_1)
   findconst.tree.cnode("WORD"_1, encodeword.@(+, toint, empty:seq.int, @(+,_.cst, empty:seq.word, arithseq(length.cst / 2 - 3, 2, 8))), 0)
  else if inst ="IDXUC"_1 ∧ inst.label(t_2)="LIT"_1 ∧ inst.label(t_1)="CONST"_1 
  then let cst = constantmapping_toint.arg.label(t_1)
   let idx = toint.arg.label(t_2)
   extractith(cst, idx, 3)
  else if inst in"Q5FZwordzseqZTzseqZint"∧ inst.label(t_2)="LIT"_1 ∧ inst.label(t_1)="CONST"_1 
  then // only expand when is standard sequence:that is 0 is in first field of record // 
   let cst = constantmapping_toint.arg.label(t_1)
   let idx = toint.arg.label(t_2)
   if idx > 0 ∧ cst_3 ="LIT"_1 ∧ cst_4 ="0"_1 
   then extractith(cst, idx + 1, 3)
   else tree(label.t, l)
  else // assert not(nosons.t = 2)∨ not(inst.label(t_2)="LIT"_1 ∧ inst.label(t_1)="CONST"_1)report"+"+ inst + arg.label.t // 
  if inst ="SET"_1 ∧ not.isempty.asconst(t_1)
  then findconst.replacelocal(arg.label.t, t_1, t_2)
  else if inst in [ opSUB, opRSUB]∧ inst.label(t_1)="LIT"_1 ∧ inst.label(t_2)="LIT"_1 
  then let a = toint.arg.label(t_1)
   let b = toint.arg.label(t_2)
   if inst = opSUB 
   then if between(a, -100, 100)∧ between(b, -100, 100)
    then tree.cnode("LIT"_1, toword(a - b), 0)
    else tree(label.t, l)
   else // opRSUB // 
   tree.cnode("LIT"_1, toword.representation(casttoreal.a - casttoreal.b), 0)
  else tree(label.t, l)

function asconst(t:tree.cnode)seq.word 
 if inst.label.t in"LIT CONST WORD FREF"
  then [ inst.label.t, arg.label.t]
  else if inst.label.t ="FLAT"_1 ∧ inst.label(t_1)="CONST"_1 
  then let cst = constantmapping_toint.arg.label(t_1)
   subseq(cst, 3, length.cst)
  else""

function asconst(t:seq.tree.cnode, i:int, result:seq.word)seq.word 
 if i > length.t 
  then result 
  else let x = asconst(t_i)
  if isempty.x then""else asconst(t, i + 1, result + x)

function extractith(a:seq.word, p:int, i:int)tree.cnode 
 let k = 2 * p + i 
  tree.cnode(a_k, a_(k + 1), 0)

Function replacelocal(v:word, with:tree.cnode, t:tree.cnode)tree.cnode 
 if nosons.t = 0 
  then if inst.label.t ="LOCAL"_1 ∧ arg.label.t = v then with else t 
  else tree(label.t, @(+, replacelocal(v, with), empty:seq.tree.cnode, sons.t))

function prt(f:seq.func, i:int)seq.word [ EOL]+ number(f_i)+ symboltext(f_i)+ print.codetree(f_i)

function filterlib(existing:set.word, f:func)seq.func 
 if number.f in existing then empty:seq.func else [ f]

function addlibsym(alltypes:set.libtype, s:seq.func, q:syminfo)seq.func 
 let myinst = funcfrominstruction(alltypes, instruction.q, replaceT(parameter.modname.q, returntype.q), length.paratypes.q)
  let tr = findconst.buildcodetree(subseq(myinst, 2, length.myinst), 1)
  let rt = if hasproto.q then towords.protoreturntype.q else towords.returntype.q 
  let t = if nosons.tr = 1 ∧ inst.label.tr ="CALL"_1 
   then let a = tosyminfo.arg.label.tr 
    if name.a ="PROFILE"_1 ∧ last.towords.modname.a ="options"_1 
    then func(length.paratypes.q, rt, mangled.q, tr_1,"profile"+ mangled.q)
    else func(length.paratypes.q, rt, mangled.q, tr,"")
   else func(length.paratypes.q, rt, mangled.q, tr,"")
  replace(s, key.t, t)

function roots(m:mod2desc)set.int 
 if isabstract.modname.m ∨ isprivate.m 
  then empty:set.int 
  else @(+, encoding, empty:set.int, @(+, mangled, empty:seq.word, toseq.export.m + toseq.defines.m))

Function pass2(r:pass1result)pass1result 
 // does inline expansion, finds consts, removes unreaachable functions // 
 PROFILE.
   let funcs = @(addlibsym.alltypes.r, identity, dseq.dummyfunc, newcode.r + compiled.r)
   let roots = toseq.@(∪, roots, empty:set.int, mods.r)
  let callgraph = @(+, getarcs, newgraph.empty:seq.arc.int, funcs)
  let reachable = reachable(callgraph, roots + getFREFinconstants)
  let p = program(libname(r)_1, funcs, callgraph, dummyfunc)
  let s = @(expandapply, identity, p, toseq.reachable)
  // assert false:@(+, prt(allfunctions.s),"", toseq.reachable)// 
  let s1 = @(simpleinline, identity, s, toseq.reachable)
  let s2 = @(simpleinline, identity, s1, toseq.reachable)
  let reachable2 = reachable(callgraph.s2, roots + getFREFinconstants)
  let f = @(+,_.allfunctions.s2, empty:seq.func, toseq.reachable2)
  let y = @(+, readwritestate, empty:seq.int, f)
  let state = reachable(complement.callgraph.s2, y)
  // only pass on functions that can be reached from roots and are in this library // 
  let g = @(+, filterlib.asset.@(+, mangled, empty:seq.word, compiled.r), empty:seq.func, f)
  // find tail calls and constants // 
  let rr = @(+, findconstandtail.@(+, toword, asset.empty:seq.word, toseq.state), empty:seq.func, g)
  pass1result(rr, libname.r, newcode.r, compiled.r, mods.r, existingtypes.r, alltypes.r)



function checktree(s:seq.func)boolean @(∧, checktree, true, s)

function checktree(f:func)boolean 
 assert checktree.codetree.f report"invalid tree"+ print.f 
  true

function checktree(t:tree.cnode)boolean 
 if inst.label.t in"CALLB FREFB"
  then false 
  else if inst.label.t ="SET"_1 ∧ not(nosons.t = 2)
  then false 
  else if inst.label.t ="if"_1 ∧ not(nosons.t = 3)then false else @(∧, checktree, true, sons.t)

function readwritestate(f:func)seq.int 
 if"STATE"in codetree.f then [ key.f]else empty:seq.int

function findconstandtail(stateChangingFuncs:set.word, f:func)func 
 // finds constants,, finds tail calls, 
   and make sure"STATE"is root on state changing functions // 
  let p = findconst( codetree.f)
  let q = if   // number.f in "Q5FZtesttypezseqZTzpseqZint " // true
  then
     tailcall(p,number.f,nopara.f)
  else 
    tailcall(p, getmaxvar.p + 1, number.f)
  replacecodetree(f, if number.f in stateChangingFuncs ∧ not(inst.label.q ="STATE"_1)
   then tree(cnode("STATE"_1,"0"_1, 0), [ q])
   else q)


function print(g:graph.int)seq.word @(+, p,"", toseq.arcs.g)

function p(a:arc.int)seq.word [ toword.tail.a]+":"+ toword.head.a

Function getarcs(f:func)seq.arc.int calls(key.f, codetree.f)

Function calls(self:int, t:tree.cnode)seq.arc.int 
 @(+, calls.self, empty:seq.arc.int, sons.t)+ if inst.label.t in"CALL FREF"
  then [ arc(self, funckey.arg.label.t)]
  else // if inst.label(t)="CONST"_1 then let constnumber = toint.arg.label(t)@(+, arc.self, empty:seq.arc.int, getFREF(1, empty:seq.int, constantmapping_constnumber))else // 
  empty:seq.arc.int

type program is record library:word, allfunctions:seq.func, callgraph:graph.int, fn:func

__________________________

Simple inline expansion

function inline(fn:word, replacement:tree.cnode, adjust:int, code:tree.cnode)tree.cnode 
 let l = @(+, inline(fn, replacement, adjust), empty:seq.tree.cnode, sons.code)
  if inst.label.code ="CALL"_1 ∧ arg.label.code = fn 
  then subinline(fn, l, adjust, replacement)
  else tree(label.code, l)

function subinline(fn:word, p:seq.tree.cnode, adjust:int, code:tree.cnode)tree.cnode 
 if inst.label.code ="PARA"_1 
  then assert between(toint.arg.label.code, 1, length.p)report"inline problem"+ fn + arg.label.code + toword.length.p 
   p_(length.p - toint.arg.label.code + 1)
  else let l = @(+, subinline(fn, p, adjust), empty:seq.tree.cnode, sons.code)
  if inst.label.code in"LOCAL SET"
  then tree(cnode(inst.label.code, toword(toint.arg.label.code + adjust), 0), l)
  else tree(label.code, l)

Function simpleinline(p:program, f:int)program 
 let fn = allfunctions(p)_f 
  if not.simple.fn 
  then p 
  else let pred = toseq.predecessors(callgraph.p, f)
  @(replacecall, identity, program(library.p, allfunctions.p, callgraph.p, fn), pred)

function replacecall(p:program, f:int)program 
 if key.fn.p = f 
  then p 
  else let simple = fn.p 
  let infunc = allfunctions(p)_f 
  let t = inline(number.simple, codetree.simple, getmaxvar.codetree.infunc, codetree.infunc)
  replace(p, replacecodetree(infunc, findconst.t))

Function replace(p:program, fn:func)program 
 let f = key.fn 
  let newall = replace(allfunctions.p, f, fn)
  let oldarcs = @(+, arc.f, asset.empty:seq.arc.int, toseq.successors(callgraph.p, f))
  program(library.p, newall, replacearcs(callgraph.p, oldarcs, asset.getarcs.fn), fn.p)

/Function replace(allfunctions:seq.func, f:func)seq.func replace(allfunctions, key.f, f)

______________

Tailcall is a little bit tricky because must use tmps when a parameter is used to define another parameter to the right.For example F1(P1, P2)has tail call of F1(P1 + 1, P1)must use T1 = P1 + 1 ; P2 = P1 ; P1 = T1 ; We also handle removing the no op of assigning a parameter to itself.

Function tailcall(t:tree.cnode, nextvar:int, self:word)tree.cnode 
 if inst.label.t ="if"_1 
  then assert nosons.t = 3 report"incorrect sons"
   tree(label.t, [ t_1, tailcall(t_2, nextvar, self), tailcall(t_3, nextvar, self)])
  else if inst.label.t ="SET"_1 
  then assert nosons.t = 2 report"incorrect sons 2"
   tree(label.t, [ t_1, tailcall(t_2, nextvar, self)])
  else if inst.label.t ="CALL"_1 ∧ arg.label.t = self 
  then tailcall2(t, nextvar + 1, nosons.t, empty:seq.tree.cnode)
  else t

Function tailcall2(t:tree.cnode, nextvar:int, son:int, result:seq.tree.cnode)tree.cnode 
 if son = 0 
  then tree(cnode("TAIL"_1, arg.label.t, 0), result)
  else let thispara = t_son 
  let var = toword.nextvar 
  let p = cnode("PARA"_1, toword(nosons.t - son + 1), 0)
  if @(∨, in.p, false, result)
  then let newresult = [ thispara]+ @(+, replace(cnode("LOCAL"_1, var, 0), p), empty:seq.tree.cnode, result)
   tree(cnode("SET"_1, var, 2), [ tree.p, tailcall2(t, nextvar + 1, son - 1, newresult)])
  else tailcall2(t, nextvar, son - 1, [ thispara]+ result)

---new tail ---

Function tailcall(t:tree.cnode,  self:word)boolean
 if inst.label.t ="if"_1 
  then  
    if  tailcall(t_2, self) then true else  tailcall(t_3, self)
  else if inst.label.t ="SET"_1  then    tailcall(t_2, self)
  else if inst.label.t ="LOOP"_1 then false 
  else if inst.label.t ="CALL"_1 ∧ arg.label.t = self 
  then true
  else false

Function tailcall(t:tree.cnode,self:word,nopara:int) tree.cnode
if tailcall(t,self) then
    let m = getmaxvar.t+1
       let s =  @(leftcat, newNode("LOCAL"_1), empty:seq.tree.cnode,arithseq(nopara,1,m))
       let plist=@(leftcat, newNode("PARA"_1), empty:seq.tree.cnode,arithseq(nopara,1,1))
       tree(cnode("LOOP"_1,toword.0,0),[newNode("LIT"_1,m),tailcall(s,self,t)]+plist)
else t 

function leftcat(a:seq.tree.cnode,b:tree.cnode) seq.tree.cnode [b]+a

function newNode(w:word,i:int) tree.cnode tree(cnode(w,toword.i,0))

  
function tailcall(subs:seq.tree.cnode,self:word,t:tree.cnode ) tree.cnode
 if inst.label.t ="if"_1 
  then  
  tree(label.t, [ tailcall(subs,"nomatch"_1,t_1), tailcall(subs,self,t_2), tailcall(subs,self,t_3)])
   else if inst.label.t ="SET"_1 
  then 
   tree(label.t, [ tailcall(subs,"nomatch"_1,t_1), tailcall(subs,self,t_2)])
   else if inst.label.t ="LOOP"_1 then
     tree(label.t,@(+,tailcall(subs,"nomatch"_1),empty:seq.tree.cnode,  sons.t ) )
  else if inst.label.t ="CALL"_1 ∧ arg.label.t = self 
  then  tree( cnode("EXIT"_1,self,0 ), @(+,tailcall(subs,"nomatch"_1),empty:seq.tree.cnode,  sons.t ) )
  else  if inst.label.t ="PARA"_1 then   
         subs_toint.arg.label.t 
    else 
      tree(label.t,@(+,tailcall(subs,"nomatch"_1),empty:seq.tree.cnode,  sons.t ) )
  
       
------


Function in(c:cnode, t:tree.cnode)boolean 
 if c = label.t then true else @(∨, in.c, false, sons.t)

Function getmaxvar(t:tree.cnode)int 
 @(max, getmaxvar, if inst.label.t ="SET"_1 then toint.arg.label.t else 0, sons.t)

_____________


function genapply(prg:program, term1:word, term2:word, ptyp:word, profile:seq.word)program 
    let next = getnext.library.prg 
  let p1 = nopara(allfunctions(prg)_funckey.term1) - 2 
  let p = nopara(allfunctions(prg)_funckey.term2) - 1 
      let nopara=3 + p + p1
  let newfuncmangledname = mangle("q"_1, mytype.[ next], constantseq(nopara, mytype."int"))
  assert p ≥ 0 report"illformed"+ term1 + term2 + print(allfunctions(prg)_funckey.term2)
  // assert false:[ term1, term2]// 
    let insttree =  if  term2 in  "myidentZtest3ZintZintZint myidentZtest3Zint" then 
     buildcodetree(template3(newfuncmangledname,term1,term2,p1,p,ptyp),1)
    else
    buildcodetree.@(+, template.[ @(+, tocnodepara, empty:seq.cnode, arithseq(p, -1, 3 + p)), 
  [ cnode("CALL"_1, term2, 1 + p)], 
  [ cnode("CALL"_1, term1, 2 + p1)], 
  [ cnode("LIT"_1,"2"_1, 0), cnode("FREF"_1, ptyp, 1)], 
  @(+, tocnodepara, empty:seq.cnode, arithseq(p1, -1, nopara)),
  [ cnode("CALL"_1, newfuncmangledname, nopara)]], empty:seq.cnode, template3)
  let newf = func(nopara, "int", newfuncmangledname, insttree, profile)
  program(next, replace(allfunctions.prg, key.newf , newf), callgraph.prg + getarcs.newf, newf)

 function parainst(i:int) seq.word "PARA"+toword.i

 
function getnext(p:word)word 
 let q = decode.p 
  let l = if between(q_1, 48, 57)then q else [ 49, 48, 48]+ q 
  encodeword(decode.toword(((l_1 - 48)* 10 + l_2 - 48)* 10 + l_3 - 48 + 1)+ subseq(l, 4, length.l))


function template(r:seq.seq.cnode, n:cnode)seq.cnode 
 if arg.n ="TERM2PARA"_1 
  then r_1 
  else if arg.n ="TERM2"_1 
  then r_2 
  else if arg.n ="TERM1"_1 
  then r_3 
  else if arg.n ="PTYP"_1 
  then r_4 
  else if arg.n ="TERM1PARA"_1 then r_5 
  else if arg.n ="SELF"_1 then r_6 else [ n]


function tocnodepara(i:int)cnode cnode("PARA"_1, toword.i, 0)


function template3 seq.cnode 
// template3 was created from following code.xfunction applyR2(p2:p2t, acc:resulttype, s:seq(tseqelement), i:int)resulttype ; if i > length.s then acc else iftype x:pseq(tseqelement)= s then applyR(p2, applyR(p2, acc, a.x, 1), b.x, 1)else applyR(p2, term1(acc, term2(p2, s_i)), s, i + 1)
 // 
 [ cnode("PARA"_1,"1"_1, 0), 
 cnode("PARA"_1,"2"_1, 0), 
 cnode("LIT"_1,"1"_1, 0), 
 cnode("IDXUC"_1,"X"_1, 2), 
 cnode(opGT,"X"_1, 2), 
 cnode("PARA"_1,"3"_1, 0), 
 cnode("PARA"_1,"2"_1, 0), 
 cnode("LOCAL"_1,"1"_1, 0), 
 cnode("LIT"_1,"0"_1, 0), 
 cnode("IDXUC"_1,"X"_1, 2), 
 cnode("FREF"_1,"PTYP"_1, 0), 
 cnode(opEQL,"X"_1, 2), 
 cnode("PARA"_1,"TERM1PARA"_1, 0), 
 cnode("PARA"_1,"TERM2PARA"_1, 0), 
 cnode("PARA"_1,"TERM1PARA"_1, 0), 
 cnode("PARA"_1,"TERM2PARA"_1, 0), 
 cnode("PARA"_1,"3"_1, 0), 
 cnode("LOCAL"_1,"1"_1, 0), 
 cnode("LIT"_1,"2"_1, 0), 
 cnode("IDXUC"_1,"X"_1, 2), 
 cnode("LIT"_1,"1"_1, 0), 
 cnode("CALL"_1,"SELF"_1, 4), 
 cnode("LOCAL"_1,"1"_1, 0), 
 cnode("LIT"_1,"3"_1, 0), 
 cnode("IDXUC"_1,"X"_1, 2), 
 cnode("LIT"_1,"1"_1, 0), 
 cnode("CALL"_1,"SELF"_1, 4), 
 cnode("PARA"_1,"TERM1PARA"_1, 0), 
 cnode("PARA"_1,"TERM2PARA"_1, 0), 
 cnode("PARA"_1,"TERM1PARA"_1, 0), 
 cnode("PARA"_1,"3"_1, 0), 
 cnode("PARA"_1,"TERM2PARA"_1, 0), 
 cnode("PARA"_1,"2"_1, 0), 
 cnode("PARA"_1,"1"_1, 0), 
 cnode("IDX"_1,"0"_1, 2), 
 cnode("CALL"_1,"TERM2"_1, 2), 
 cnode("CALL"_1,"TERM1"_1, 2), 
 cnode("PARA"_1,"2"_1, 0), 
 cnode("PARA"_1,"1"_1, 0), 
 cnode("LIT"_1,"1"_1, 0), 
 cnode(opADD,"X"_1, 2), 
 cnode("CALL"_1,"SELF"_1, 4), 
 cnode("if"_1,"X"_1, 3), 
 cnode("SET"_1,"1"_1, 2), 
 cnode("if"_1,"X"_1, 3)]

 function template3(mangledname:word,term1:word,term2:word,nopara1:int,nopara2:int,ptyp:word) seq.word
 // PARA 1 is index PARA 2 is seq PARA 3 is result 
    LOCAL 3 is index LOCAL 2 is seq LOCAL 1 is result //
// EQL - Q3DZbuiltinZintZint  opGT =Q3EZbuiltinZintZint //
 let CALLSELF = [toword(3+nopara1+nopara2),mangledname] 
 let CALLTERM1 = [toword(2+nopara1),term1] 
  let CALLTERM2 = [toword(1+nopara2),term2] 
 let TERM1PARA =@(+,parainst,"",arithseq(nopara1,-1,3+nopara1+nopara2))
 let TERM2PARA = @(+,parainst,"",arithseq(nopara2,-1,3+nopara2))
 "LIT 1
 LOCAL 3  LOCAL 2   LIT 1   IDXUC  2  Q3EZbuiltinZintZint  2
 LOCAL 1 
    LOCAL 2   LIT 0  IDXUC  2 FREF"+ ptyp+"   Q3DZbuiltinZintZint 2  "+ TERM1PARA+TERM2PARA+
         "LOCAL 1  
         LOCAL 2   LIT 2  IDXUC  2  
         LIT 1  
       CALL"+ CALLSELF +"  
       LOCAL 2  LIT 3  IDXUC  2 
       LIT 1   
    EXIT 3 "+TERM1PARA+" 
         LOCAL 1   
         "+TERM2PARA+"  LOCAL 2  LOCAL 3  IDX  2 CALL"+CALLTERM2+" 
      CALL"+CALLTERM1+" 
       LOCAL 2    
       LOCAL 3   LIT 1  ADD 2
    EXIT 3
 if 3
 if 3
PARA 3 
PARA 2
PARA 1
LOOP 5 "



function expandapply(p:program, thisone:int)program 
 let f = allfunctions(p)_thisone 
  let x = expandapply(p, codetree.f, profile.f)
  if codetree.f = c.x 
  then p 
  else // assert codetree.f = c.x:print.codetree.f +"<>>>"+ print.c.x // 
  replace(p.x, replacecodetree(f, c.x))

type rexpand is record p:program, c:tree.cnode

function =(a:rexpand, b:rexpand)boolean false

function merge(profile:seq.word, s:seq.rexpand, t:tree.cnode)seq.rexpand 
 s + expandapply(p.last.s, t, profile)

function expandapply(p:program, t:tree.cnode, profile:seq.word)rexpand 
 if nosons.t = 0 
  then rexpand(p, t)
  else let l = @(merge.profile,_.t, [ expandapply(p, t_1, profile)], arithseq(nosons.t - 1, 1, 2))
  let t2 = tree(label.t, @(+, c, empty:seq.tree.cnode, l))
  if inst.label.t ="APPLY"_1 
  then let f = allfunctions(p)_funckey.arg.label(t2_3)
   if nosons.t2 = 5 ∧ nopara.f = 1 ∧ inst.label.codetree.f ="PARA"_1 ∧ checkistypechangeonly(arg.label(t2_4), arg.label(t2_1))
   then rexpand(p.last.l, t2_2)
   else let p2 = genapply(p.last.l, arg.label(t2_(nosons.t2 - 1)), arg.label(t2_(nosons.t2 - 2)), arg.label(t2_nosons.t2), profile)
   rexpand(p2, tree(cnode("CALL"_1, number.fn.p2, nopara.fn.p2), subseq(sons.t2, 1, nosons.t2 - 3)+ tree.cnode("LIT"_1,"1"_1, 0)))
  else rexpand(p.last.l, t2)

function checkistypechangeonly(term1:word, term3:word)boolean 
 // check to see if APPLY just does a type change // 
  let p = codedown.term3 
  if length.p ≠ 2 ∨ last(p_2)≠"seq"_1 ∨ p_1_1 ≠ merge."empty:seq.T"
  then false 
  else let q = codedown.term1 
    length.q = 4 ∧ last(q_2)="seq"_1 ∧ q_1_1 ="+"_1 &and subseq(q,3,length.q)=["T seq","T"] 

