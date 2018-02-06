module pass2a

use buildtree


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


function opSUB word {"Q2DZbuiltinZintZint"_1 }

function opRSUB word {"Q2DZbuiltinZrealZreal"_1 }

function isconst(t:tree.cnode) boolean 
   inst.label.t in"LIT CRECORD WORD FREF" 
   

Function findconst(t:tree.cnode)tree.cnode 
  if nosons.t = 0 
  then t 
  else  
     let inst = if inst.label.t ="CALL"_1 ∧ arg.label.t ="Q5FZwordzseqZTzseqZint"_1 
   then arg.label.t 
   else inst.label.t 
   if inst ="CRECORD"_1 then t
   else 
   let l = @(+, findconst, empty:seq.tree.cnode, sons.t)
   if inst ="RECORD"_1 
  then 
       tree(if @(&and,isconst,true,l) then cnode("CRECORD"_1,"0"_1) else label.t,l)
  else  if inst ="IDXUC"_1 ∧ inst.label(l_2)="LIT"_1 ∧ inst.label(l_1)="CRECORD"_1 
  then  
     let idx = toint.arg.label(l_2)
     (l_1)_(idx+1)
   else  if inst in"Q5FZwordzseqZTzseqZint"∧ inst.label(t_2)="LIT"_1 ∧ inst.label(t_1)="CRECORD"_1 
  then // only expand when is standard sequence:that is 0 is in first field of record // 
   let cst = t_1
   let idx = toint.arg.label(t_2)
   if idx > 0 ∧  inst.label(cst_1)  ="LIT"_1 ∧ arg.label(cst_1)   ="0"_1 
   then cst_( idx + 2)
   else tree(label.t, l)
  else   if inst in [ opSUB, opRSUB]∧ inst.label(t_1)="LIT"_1 ∧ inst.label(t_2)="LIT"_1 
  then let a = toint.arg.label(t_1)
   let b = toint.arg.label(t_2)
   if inst = opSUB 
   then if between(a, -100, 100)∧ between(b, -100, 100)
    then tree.cnode("LIT"_1, toword(a - b))
    else tree(label.t, l)
   else // opRSUB // tree.cnode("LIT"_1, toword.representation(casttoreal.a - casttoreal.b))
  else tree(label.t, l)

 



function prt(f:seq.func, i:int)seq.word [ EOL]+ number(f_i)+ symboltext(f_i)+ print.codetree(f_i)

function filterlib(existing:set.word, f:func)seq.func 
 if number.f in existing then empty:seq.func else [ f]

use options.seq.func

function addlibsym(alltypes:set.libtype, s:seq.func, q:syminfo)seq.func 
// PROFILE. //
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
  PROFILE.let funcs = @(addlibsym.alltypes.r, identity, dseq.dummyfunc, newcode.r + compiled.r)
   let roots = toseq.@(∪, roots, empty:set.int, mods.r)
   let callgraph = @(+, getarcs, newgraph.empty:seq.arc.int, funcs)
   // assert false report @(+,number, "",@(+, _(funcs),empty:seq.func,     toseq.nodes.callgraph)) //
   let reachable = reachable(callgraph, roots)
   let p = program(libname(r)_1, funcs, callgraph, dummyfunc)
   let s = @(expandapply, identity, p, toseq.reachable)
   // assert false:@(+, prt(allfunctions.s),"", toseq.reachable)// 
   let s1 = @(simpleinline, identity, s, toseq.reachable)
   let s2 = @(simpleinline, identity, s1, toseq.reachable)
   let reachable2 = reachable(callgraph.s2, roots )
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
 // finds constants,, finds tail calls, and make sure"STATE"is root on state changing functions // 
  let p = findconst.codetree.f 
  let q =  tailcall(p, number.f, nopara.f)
  replacecodetree(f, if number.f in stateChangingFuncs ∧ not(inst.label.q ="STATE"_1)
   then tree(cnode("STATE"_1,"0"_1), [ q])
   else q)

function print(g:graph.int)seq.word @(+, p,"", toseq.arcs.g)

function p(a:arc.int)seq.word [ toword.tail.a]+":"+ toword.head.a

Function getarcs(f:func)seq.arc.int calls(key.f, codetree.f)

Function calls(self:int, t:tree.cnode)seq.arc.int 
 @(+, calls.self, empty:seq.arc.int, sons.t)+ if inst.label.t in"CALL FREF"
  then [ arc(self, funckey.arg.label.t)]
  else // if inst.label.t in "CALL WORD RECORD IDXUC LIT LOCAL PARA SET LOOP CONTINUE APPLY NOINLINE EQL ADD if CALLIDX PROCESS2"
  then  empty:seq.arc.int
  else  if inst.label.t in "Q3EZbuiltinZintZint xassertZbuiltinZwordzseq xlibsZbuiltin xQ2DZbuiltinZintZint xunloadlibZbuiltinZUTF8
  xabortedZbuiltinZTzprocess" then
   [ arc(self, funckey.inst.label.t)]
  else 
    assert false report [inst.label.t] //
  empty:seq.arc.int
  
 

type program is record library:word, allfunctions:seq.func, callgraph:graph.int, fnx:func

__________________________

Simple inline expansion




Function simpleinline(p:program, f:int)program 
 let fn = allfunctions(p)_f 
 let typ=functype.fn
  if not(functype.fn in "SIMPLE INLINE" )
  then p 
  else let pred = toseq.predecessors(callgraph.p, f)
  @(replacecall(typ,fn), identity, program(library.p, allfunctions.p, callgraph.p, fn), pred)

function replacecall(functype:word,simple:func,p:program, f:int)program 
 if key.simple = f 
  then p 
  else 
  let infunc = allfunctions(p)_f 
   let t =  newinline(functype,simple, dseq(tree.cnode("UNASIGNED"_1,"1"_1)),1,codetree.infunc)
   replace(p, replacecodetree(infunc, findconst.t))
  
/function diff(a:tree.cnode,b:tree.cnode,i:int) seq.word
    if i = 0 then if label.a=label.b then
       if nosons.a=nosons.b then
       diff(a,b,1) 
       else "diff sons"
    else "diff label"+inst.label.a+inst.label.b
    else if i > nosons.a then ""
    else   
      let z=diff(a_i,b_i,0)
      if z="" then diff(a,b,i+1) else z
      
    
  
/function  diff(a:seq.word,b:seq.word,i:int) seq.word
   if i > length.a then "SAME"
   else if a_i=b_i then diff(a,b,i+1)
   else "DIFF"+"&br"+subseq(a,i-1,i)+"&br"+subseq(b,i-1,i)+ diff(a,b,i+1)

Function replace(p:program, fn:func)program 
 let f = key.fn 
  let newall = replace(allfunctions.p, f, fn)
  let oldarcs = @(+, arc.f, asset.empty:seq.arc.int, toseq.successors(callgraph.p, f))
  program(library.p, newall, replacearcs(callgraph.p, oldarcs, asset.getarcs.fn), fnx.p)
  

function checksets( s:set.word,t:tree.cnode) seq.word
  if inst.label.t="SET"_1 then
     checksets(s, t_1)+ checksets(s+arg.label.t ,t_2)
  else if inst.label.t="LOCAL"_1 then
    if arg.label.t in s then "" else [arg.label.t]
 else if inst.label.t="LOOP"_1 then
   let a= toint.arg.label(t_1) 
     @(+,checksets( @(+,   toword,   s, arithseq(nosons.t-2,1,a))),"",sons.t)
 else    @(+,checksets(s+arg.label.t),"",sons.t)
     
function processpara(functype:word,simple:func, sets:seq(tree.cnode), nextset:int, sons:seq.tree.cnode,paramap:seq.tree.cnode)
 tree.cnode // add sets for complex parameters and then does inline expansion. //
 if length.paramap= length.sons then
  subinline(number.simple, paramap, dseq(tree.cnode("UNASIGNED"_1,"1"_1)),nextset,codetree.simple)
 else
   let i = length.paramap+1
   if inst.label(sons_i) in  "LIT LOCAL PARA FREF FREFB " then 
     let p = newinline(functype,simple, sets,nextset,sons_i)
     processpara(functype,simple, sets, nextset, sons,paramap+p)
   else   
     let p = newinline(functype,  simple, sets,nextset+1,sons_i)
     let t =processpara(functype,simple,sets, nextset+1, sons,paramap+tree(cnode("LOCAL"_1,toword.nextset)))
        tree(cnode("SET"_1,toword.nextset),[p,t])

function addtosetmap(sets:seq.tree.cnode,old:int,new:int,numbertoadd:int) seq.tree.cnode 
 if numbertoadd=0 then sets else 
 let i = numbertoadd-1
 addtosetmap(replace(sets,old+i,tree(cnode("LOCAL"_1,toword(new+i)) )),old,new,i)

function newinline( functype:word,simple:func, sets:seq(tree.cnode), nextset:int, code:tree.cnode)tree.cnode 
   if inst.label.code="SET"_1 then 
     let s1=newinline(functype,simple, sets,nextset,code_1)
       if inst.label.s1 in "LIT LOCAL PARA FREF FREFB "   then  
          newinline(functype,simple, replace(sets,toint(arg.label.code),s1),nextset,code_2)
        else 
        let s2=newinline(functype,simple, addtosetmap(sets,toint(arg.label.code),nextset,1),nextset+1,code_2)
     tree(cnode("SET"_1,toword.nextset),[s1,s2])
   else if inst.label.code="LOCAL"_1 then
       sets_toint(arg.label.code)
   else  if inst.label.code="LOOP"_1 then
      let firstvar=toint.arg.label(code_1)
      let  l = @(+, newinline(functype,simple, addtosetmap(sets,firstvar,nextset,nosons.code-2),nextset+nosons.code-2), empty:seq.tree.cnode, sons.code)
      tree(label.code,[tree.cnode("LIT"_1,toword.nextset)]+subseq(l,2,length.l))
   else
    let l = @(+, newinline(functype,simple, sets,nextset), empty:seq.tree.cnode, sons.code)
  if inst.label.code ="CALL"_1 ∧ arg.label.code = number.simple 
  then 
    if  functype="SIMPLE"_1 then
     subinline(number.simple, l,dseq(tree.cnode("UNASIGNED"_1,"1"_1)), nextset, codetree.simple)
    else
    processpara(functype,simple,sets,nextset,sons.code,empty:seq.tree.cnode) 
   else 
    tree(label.code, l)


function subinline(fn:word, p:seq.tree.cnode, sets:seq.tree.cnode,nextset:int, code:tree.cnode)tree.cnode 
 if inst.label.code ="PARA"_1 
  then assert between(toint.arg.label.code, 1, length.p)report"inline problem"+ fn + arg.label.code + toword.length.p 
   p_(length.p - toint.arg.label.code + 1)
  else  if inst.label.code="SET"_1 then 
      let s1=subinline(fn, p, sets ,  nextset,code_1)
         if inst.label.s1 in "LIT LOCAL PARA FREF FREFB "  then  
         subinline(fn, p, replace(sets,toint(arg.label.code),s1),  nextset,code_2)   else  
      let s2=subinline(fn, p, addtosetmap(sets,toint(arg.label.code),nextset,1) ,  nextset+1,code_2)
      tree(cnode("SET"_1,toword.nextset),[s1,s2])
   else if inst.label.code="LOCAL"_1 then
       sets_toint(arg.label.code)
   else
  let l = @(+, subinline(fn, p, sets,nextset), empty:seq.tree.cnode, sons.code)
   assert not(inst.label.code in "LOOP") report "FOUND LOOP in inline expansion"
   tree(label.code, l)

______________

Tailcall

Function tailcall(t:tree.cnode, self:word)boolean 
 if inst.label.t ="if"_1 
  then if tailcall(t_2, self)then true else tailcall(t_3, self)
  else if inst.label.t ="SET"_1 
  then tailcall(t_2, self)
  else if inst.label.t ="LOOP"_1 
  then false 
  else if inst.label.t ="CALL"_1 ∧ arg.label.t = self then true else false

Function tailcall(t:tree.cnode, self:word, nopara:int)tree.cnode 
 if tailcall(t, self)
  then let m = getmaxvar.t + 1 
   let s = @(leftcat, newNode("LOCAL"_1), empty:seq.tree.cnode, arithseq(nopara, 1, m))
   let plist = @(leftcat, newNode("PARA"_1), empty:seq.tree.cnode, arithseq(nopara, 1, 1))
   tree(cnode("LOOP"_1,"0"_1), [ newNode("LIT"_1, m), tailcall(s, self, t)]+ plist)
  else t

function leftcat(a:seq.tree.cnode, b:tree.cnode)seq.tree.cnode [ b]+ a

function newNode(w:word, i:int)tree.cnode tree.cnode(w, toword.i)

function tailcall(subs:seq.tree.cnode, self:word, t:tree.cnode)tree.cnode 
 if inst.label.t ="if"_1 
  then tree(label.t, [ tailcall(subs,"nomatch"_1, t_1), tailcall(subs, self, t_2), tailcall(subs, self, t_3)])
  else if inst.label.t ="SET"_1 
  then tree(label.t, [ tailcall(subs,"nomatch"_1, t_1), tailcall(subs, self, t_2)])
  else if inst.label.t ="LOOP"_1 
  then tree(label.t, @(+, tailcall(subs,"nomatch"_1), empty:seq.tree.cnode, sons.t))
  else if inst.label.t ="CALL"_1 ∧ arg.label.t = self 
  then tree(cnode("CONTINUE"_1, self), @(+, tailcall(subs,"nomatch"_1), empty:seq.tree.cnode, sons.t))
  else if inst.label.t ="PARA"_1 
  then subs_toint.arg.label.t 
  else tree(label.t, @(+, tailcall(subs,"nomatch"_1), empty:seq.tree.cnode, sons.t))

------

Function in(c:cnode, t:tree.cnode)boolean 
 if c = label.t then true else @(∨, in.c, false, sons.t)

function getmaxvar(t:tree.cnode)int 
 @(max, getmaxvar, if inst.label.t ="SET"_1 then toint.arg.label.t else 
   if inst.label.t = "LOOP"_1 then
      toint.arg.label(t_1)+nosons.t-3
   else 0, sons.t)

_____________

function genapply(prg:program, term1:word, term2:word, ptyp:word, profile:seq.word)program 
 let next = getnext.library.prg 
  let p1 = nopara(allfunctions(prg)_funckey.term1) - 2 
  let p = nopara(allfunctions(prg)_funckey.term2) - 1 
  let nopara = 2 + p + p1 
  let newfuncmangledname = mangle("q"_1, mytype.[ next], constantseq(nopara, mytype."int"))
  assert p ≥ 0 report"illformed"+ term1 + term2 + print(allfunctions(prg)_funckey.term2)
  let insttree = buildcodetree(template(newfuncmangledname, term1, term2, p1, p, ptyp), 1)
  let newf = func(nopara,"int", newfuncmangledname, insttree, profile)
  program(next, replace(allfunctions.prg, key.newf, newf), callgraph.prg + getarcs.newf, newf)

function parainst(i:int)seq.word {"PARA"+ toword.i }

function getnext(p:word)word 
 let q = decode.p 
  let l = if between(q_1, 48, 57)then q else [ 49, 48, 48]+ q 
  encodeword(decode.toword(((l_1 - 48)* 10 + l_2 - 48)* 10 + l_3 - 48 + 1)+ subseq(l, 4, length.l))

function template(mangledname:word, term1:word, term2:word, nopara1:int, nopara2:int, ptyp:word)seq.word 
 // PARA 1 is index PARA 2 is seq PARA 3 is result LOCAL 3 is index LOCAL 2 is seq LOCAL 1 is result // 
  // Inner loop LOCAL 3 result LOCAL 4 index LOCAL 5 length of seq // 
  // EQL-Q3DZbuiltinZintZint opGT = Q3EZbuiltinZintZint // 
  let CALLSELF = [ toword(2 + nopara1 + nopara2), mangledname]
  let CALLTERM1 = [ toword(2 + nopara1), term1]
  let CALLTERM2 = [ toword(1 + nopara2), term2]
  let TERM1PARA = @(+, parainst,"", arithseq(nopara1, -1, 2 + nopara1 + nopara2))
  let TERM2PARA = @(+, parainst,"", arithseq(nopara2, -1, 2 + nopara2))
  {"LIT 1 LOCAL 2 LIT 0 IDXUC 2 FREF"+ ptyp +"Q3DZbuiltinZintZint 2"+ TERM1PARA + TERM2PARA +"LOCAL 1 LOCAL 2 LIT 2 IDXUC 2 CALL"+ CALLSELF +"LOCAL 2 LIT 3 IDXUC 2 CONTINUE 2 LOCAL 2 LIT 1 IDXUC 2 LIT 3 LOCAL 4 LOCAL 5 Q3EZbuiltinZintZint 2 LOCAL 3"+ TERM1PARA +"LOCAL 3"+ TERM2PARA +"LOCAL 2 LIT 0 IDXUC 2 LIT 0 Q3DZbuiltinZintZint 2 LOCAL 2 LOCAL 4 LIT 1 ADD 2 IDXUC 2 LOCAL 2 LIT 0 IDXUC 2 LOCAL 2 LOCAL 4 CALLIDX 3 if 3 CALL"+ CALLTERM2 +"CALL"+ CALLTERM1 +"LOCAL 4 LIT 1 ADD 2 CONTINUE 2 if 3 LOCAL 1 LIT 1 LOOP 4 SET 5 if 3 PARA 2 PARA 1 LOOP 4"}


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
   rexpand(p2, tree(cnode("CALL"_1, number.fnx.p2), subseq(sons.t2, 1, nosons.t2 - 3)))
  else rexpand(p.last.l, t2)

function checkistypechangeonly(term1:word, term3:word)boolean 
 // check to see if APPLY just does a type change // 
  let p = codedown.term3 
  if length.p ≠ 2 ∨ last(p_2)≠"seq"_1 ∨ p_1_1 ≠ merge."empty:seq.T"
  then false 
  else let q = codedown.term1 
  length.q = 4 ∧ last(q_2)="seq"_1 ∧ q_1_1 ="+"_1 ∧ subseq(q, 3, length.q)= ["T seq","T"]


