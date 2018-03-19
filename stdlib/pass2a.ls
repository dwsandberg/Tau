module pass2a

use buildtree


use graph.word

use libscope



use oseq.int

use passcommon

use real

use seq.arc.word

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

use set.arc.word

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
  if nosons.t = 0  then t  else  
   let inst =  inst.label.t 
   if inst ="CRECORD"_1 then t
   else 
   let l = @(+, findconst, empty:seq.tree.cnode, sons.t)
  if inst ="RECORD"_1 
  then 
       tree(if @(&and,isconst,true,l) then cnode("CRECORD"_1,"0"_1) else label.t,l)
  else  
  if inst ="IDXUC"_1 ∧ inst.label(l_2)="LIT"_1 ∧ inst.label(l_1)="CRECORD"_1 
  then  
     let idx = toint.arg.label(l_2)
      if between(idx,0,nosons(l_1)-1) then
       (l_1)_(idx+1)
       else tree(label.t, l)
   else  if inst="if"_1 then
       let i2=inst.label(l_1)
       if i2=  "LIT"_1 then
        if arg.label(l_1) ="1"_1 then l_2 else l_3
       else if i2="notZbuiltinZboolean"_1 then
          tree(label.t, [l_1_1,l_3,l_2])
       else tree(label.t, l)
   else 
   if inst in"Q5FZwordzseqZTzseqZint"∧ inst.label(l_2)="LIT"_1 ∧ inst.label(l_1)="CRECORD"_1 
  then // only expand when is standard sequence:that is 0 is in first field of record // 
   let cst = l_1
   let idx = toint.arg.label(l_2)
   if idx > 0 ∧  idx &le nosons(cst)-2 &and inst.label(cst_1)  ="LIT"_1 ∧ arg.label(cst_1)   ="0"_1 
   then cst_( idx + 2)
   else tree(label.t, l)
  else  
      if length.l = 2 &and inst.label(l_1)="LIT"_1 ∧ inst.label(l_2)="LIT"_1 then
       simplecalcs(label.t,toint.arg.label(l_1),toint.arg.label(l_2),l)
  else tree(label.t, l)

function simplecalcs( label:cnode, a:int,b:int, l:seq.tree.cnode) tree.cnode
    let inst=inst.label
      if inst=  opRSUB  then  tree.cnode("LIT"_1, toword.representation(casttoreal.a - casttoreal.b)) 
     else  if not( between(a, -2147483648, 2147483648)∧ between(b, -2147483648, 2147483648)) then   tree(label,l)
      else   if inst = opSUB then tree.cnode("LIT"_1, toword(a - b))
      else   if inst = "Q2BZbuiltinZintZint"_1 then tree.cnode("LIT"_1, toword(a + b))
      else   if inst = "Q2FZbuiltinZintZint"_1 &and b &ne 0 then tree.cnode("LIT"_1, toword(a / b))
      else   if inst = "Q2AZbuiltinZintZint"_1 then tree.cnode("LIT"_1, toword(a * b))
      else   if inst = "EQL"_1 then  tree.cnode("LIT"_1, if a = b then "1"_1 else "0"_1)
      else   if inst = "Q3CQ3CZbuiltinZbitsZint"_1 then tree.cnode("LIT"_1, toword(toint(bits(a) << b)))
            else   if inst = "Q3EQ3EZbuiltinZbitsZint"_1 then tree.cnode("LIT"_1, toword(toint(bits(a) >> b)))
      else 
           //  assert inst in "Q5EZstdlibZintZint BLOCKCOUNTZinternalbcZintZint  " report "XY" +inst  //
         tree(label,l)

use bits
    
    5E ^
2A *
2B +
2F /


function prt(f:seq.func, i:int)seq.word [ EOL]+ mangledname(f_i)+ towords.returntype(f_i)+ print.codetree(f_i)

function filterlib(existing:set.word, f:func)seq.func 
 if mangledname.f in existing then empty:seq.func else [ f]




type track is record  tosyminfo: syminfo

function  ?(a:track,b:track) ordering mangled.tosyminfo.a ? mangled.tosyminfo.b

function  =(a:track,b:track) boolean mangled.tosyminfo.a=mangled.tosyminfo.b

use set.track
  
function addtoprogram(alltypes:set.libtype,map:set.track,p:program, f:word) program
   let z = find(allfunctions.p, func( 0, mytype."", f,  tree.cnode("X"_1,"X"_1), ""))
    if length.z = 1 then p else 
   let a= findelement( track(syminfoX(f)),map)
    if isempty.a then p
    else 
    addlibsym(alltypes,map,p,tosyminfo.a_1)
   


function addlibsym(alltypes:set.libtype,map:set.track,p:program, q:syminfo) program 
   let myinst = // if length.instruction.q > 0 &and (instruction.q)_1="USECALL"_1 then instruction.q
       else // funcfrominstruction(alltypes, instruction.q, replaceT(parameter.modname.q, returntype.q), length.paratypes.q)
  let trz = findconst.buildcodetree( myinst)
  // remove unneed sets // 
  let tr=newinline(  dummyfunc, dseq(tree.cnode("UNASIGNED"_1,"1"_1)),1,trz)
  let rt = if hasproto.q then  protoreturntype.q else  returntype.q 
   let options = if nosons.tr = 2 &and inst.label.tr = "OPTIONSZoptionsZwordzseqZT"_1  then 
         @(+,arg,"",@(+, label, empty:seq.cnode,  sons.(tr_1)))
        else ""
   let  profile= if "PROFILE"_1 in options then    [mangled.q ] else "noprofile"
  let tr1 = if  options="" then tr else tr_2
  let arcs = asset.calls(mangled.q, tr1)
      let isrecusive=arc(mangled.q,mangled.q) in arcs
      let hasapply =  arc(mangled.q,"APPLY"_1) in arcs
     let tr2= if isrecusive then
          tailcall(tr1, mangled.q,length.paratypes.q)
      else tr1
     let e = if hasapply then 
        expandapply(p,tr2,subseq(profile,1,1))  
    else rexpand(p,tr2) 
  let arcs2=if hasapply &or isrecusive then  asset.calls(mangled.q, c.e) else arcs 
   let flags=fixflags(c.e,length.paratypes.q,profile+options)
    let prg= if isrecusive &or hasapply  &or not( "SIMPLE"_1 in flags &or "INLINE"_1 in flags) then 
       newfunc(p.e,func(length.paratypes.q, rt, mangled.q, c.e,flags) , toseq.arcs2) 
      else
           let fn = func(length.paratypes.q, rt, mangled.q, c.e,flags) 
          let newp= program(library.p, allfunctions.p, callgraph.p ,inline.p+fn)
          newfunc(newp,fn,   toseq.arcs2) 
   @(addtoprogram(alltypes,map),head,prg,toseq(arcs2 &cup arcs))
   
function fixflags(t:tree.cnode,nopara:int,oldflags:seq.word)  seq.word
      subseq(oldflags,1,1) + let functyp=  if "FORCEINLINE"_1 in oldflags then "INLINE"_1 else 
          if "NOINLINE"_1 in oldflags then "NOINLINE"_1 else    functype(t,nopara)
      toseq( asset.subseq(oldflags,2,100)-asset."SIMPLE INLINE" + functyp )
      
 



function roots(m:mod2desc)set.word 
 if isabstract.modname.m ∨ isprivate.m 
  then empty:set.word 
  else  @(+, mangled, empty:set.word, toseq.export.m + toseq.defines.m)
  
       
use seq.pass1result

Function pass2(r:pass1result)pass1result 
 OPTIONS("PROFILE",
 // does inline expansion, finds consts, removes unreaachable functions // 
    let p1=program(libname(r)_1, invertedseq.dummyfunc,newgraph.empty:seq.arc.word,empty:seq.func)
     let roots = toseq.@(∪, roots, empty:set.word, mods.r)
      let p=@(addtoprogram(alltypes.r,@(+,track,empty:set.track,newcode.r + compiled.r)),identity,p1,roots) 
     let s2 = expandinline.p
     let statechangingfuncs = reachable(complement.callgraph.s2, toseq.predecessors(callgraph.s2,"STATE"_1))
   // only pass on functions that can be reached from roots and are in this library // 
   let g=    reachable(callgraph.s2,roots)  - asset.@(+, mangled, empty:seq.word, compiled.r)
            - asset."STATE"
   // find tail calls and constants // 
   // assert not( "qZ107toolsZintZint"_1 in g) report "P"+toseq.predecessors(callgraph.s2,"qZ107toolsZintZint"_1) //
   let rr = @(+, findconstandtail(s2,statechangingfuncs), empty:seq.func, toseq.g)
   // let rrr=if  mangledname(rr_1)="dummyfunc"_1 then subseq(rr,2,length.rr)
    else  rr //
   pass1result(rr, libname.r, newcode.r, compiled.r, mods.r, existingtypes.r, alltypes.r))

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

use opt2

function findconstandtail(p:program,stateChangingFuncs:set.word, mangledname:word)seq.func 
 // finds constants, discards builtins, and make sure"STATE"is root on state changing functions //
  let a=codedown.mangledname
    if length.a > 1 &and  ( a_2 = "builtin"  ) then empty:seq.func else 
  let f=lookupfunc(p,mangledname)
  let o = if "special"_1 in flags.f then 
    // assert mangledname in "addtobitstreamZinternalbcZintZbitzbitpackedseqZinternalbc" report "Z"+mangledname+ print.opt2.codetree.f //
    opt2.codetree.f else codetree.f
  let q = findconst.o 
    [replacecodetree(f, if mangledname.f in stateChangingFuncs ∧ not(inst.label.q ="STATE"_1)
   then tree(cnode("STATE"_1,"0"_1), [ q])
   else q)]

function print(g:graph.word)seq.word @(+, p,"", toseq.arcs.g)

function p(a:arc.word)seq.word [  tail.a]+":"+ head.a

Function getarcs(f:func)seq.arc.word calls(mangledname.f, codetree.f)

Function calls(self:word, t:tree.cnode)seq.arc.word 
 @(+, calls.self, empty:seq.arc.word, sons.t)+ if inst.label.t="FREF"_1
  then 
     [ arc(self, arg.label.t)]
  else  if inst.label.t in " WORD RECORD IDXUC LIT LOCAL PARA SET LOOP CONTINUE  NOINLINE EQL if CALLIDX PROCESS2 CRECORD  "
  then  empty:seq.arc.word
  else  //
    let  a=codedown.inst.label.t
    if length.a > 1 &and  ( a_2 = "builtin"  ) then empty:seq.arc.word
   else // [arc(self,inst.label.t)]
  
   
use invertedseq.func

use ipair.func

use seq.ipair.func

type program is record library:word, allfunctions:invertedseq.func, callgraph:graph.word, inline:seq.func

__________________________

Simple inline expansion

   Function expandinline(p:program) program
      if length.inline.p=0 then p else
      let s0=program(library.p,allfunctions.p, callgraph.p ,empty:seq.func)
     @(simple2,identity,s0,inline.p)


    Function         simple2(p:program,  simple:func) program
          let pred = predecessors(callgraph.p, mangledname.simple) - mangledname.simple
           if isempty.pred  then p else  
             // inline expands may have happen in simple so we r lookup the current version //
             assert not(mangledname.simple =" authencodingZtest3"_1) report "OOPS567"
             let s = lookupfunc(p,mangledname.simple )
             @(replacecall(s), identity, p,toseq.pred )

function replacecall(simple:func,p:program, f:word)program 
   let infunc = lookupfunc(p,f) 
   let t =  findconst.newinline(simple, dseq(tree.cnode("UNASIGNED"_1,"1"_1)),1,codetree.infunc)
   if codetree.infunc=t then p 
   else 
     let flags=fixflags(t,nopara.infunc,flags.infunc)
     if   "SIMPLE"_1 in flags &or "INLINE"_1 in flags  then 
       let newfn = func(nopara.infunc, returntype.infunc, mangledname.infunc, t, flags)
         replacefunc(program(library.p,allfunctions.p,callgraph.p,inline.p+newfn),newfn) 
     else  
      replacefunc(p, func(nopara.infunc, returntype.infunc, mangledname.infunc, t, flags))
  
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

Function replacefunc(p:program, fn:func)program 
   let newall =   add(allfunctions.p,encoding.mangledname.fn,fn)
  let oldarcs = @(+, arc.mangledname.fn, asset.empty:seq.arc.word, toseq.successors(callgraph.p, mangledname.fn))
  program(library.p, newall, replacearcs(callgraph.p, oldarcs, asset.getarcs.fn),inline.p)
  
function newfunc(p:program, fn:func,arcs:seq.arc.word)program 
     program(library.p, add(allfunctions.p,encoding.mangledname.fn,fn),  callgraph.p +  arcs,inline.p)


function lookupfunc(p:program,f:word) func
  let z = find(allfunctions.p, func( 0, mytype."", f,  tree.cnode("X"_1,"X"_1), ""))
  if length.z = 0 then dummyfunc else 
  value.z_1


function hash(f:func) int hash.mangledname.f

function checksets( s:set.word,t:tree.cnode) seq.word
  if inst.label.t="SET"_1 then
     checksets(s, t_1)+ checksets(s+arg.label.t ,t_2)
  else if inst.label.t="LOCAL"_1 then
    if arg.label.t in s then "" else [arg.label.t]
 else if inst.label.t="LOOP"_1 then
   let a= toint.arg.label(t_1) 
     @(+,checksets( @(+,   toword,   s, arithseq(nosons.t-2,1,a))),"",sons.t)
 else    @(+,checksets(s+arg.label.t),"",sons.t)
     
function processpara(simple:func, sets:seq(tree.cnode), nextset:int, sons:seq.tree.cnode,paramap:seq.tree.cnode)
 tree.cnode // add sets for complex parameters and then does inline expansion. //
 if length.paramap= length.sons then
  subinline(mangledname.simple, paramap, dseq(tree.cnode("UNASIGNED"_1,"1"_1)),nextset,codetree.simple)
 else
   let i = length.paramap+1
   if inst.label(sons_i) in  "LIT LOCAL PARA FREF FREFB " then 
     let p = newinline(simple, sets,nextset,sons_i)
     processpara(simple, sets, nextset, sons,paramap+p)
   else   
     let p = newinline(  simple, sets,nextset+1,sons_i)
     let t =processpara(simple,sets, nextset+1, sons,paramap+tree(cnode("LOCAL"_1,toword.nextset)))
        tree(cnode("SET"_1,toword.nextset),[p,t])

function addtosetmap(sets:seq.tree.cnode,old:int,new:int,numbertoadd:int) seq.tree.cnode 
 if numbertoadd=0 then sets else 
 let i = numbertoadd-1
 addtosetmap(replace(sets,old+i,tree(cnode("LOCAL"_1,toword(new+i)) )),old,new,i)
 
function iscallto(t:tree.cnode,f:word) boolean
      f= inst.label.t 

function newinline( simple:func, sets:seq(tree.cnode), nextset:int, code:tree.cnode)tree.cnode 
   if inst.label.code="SET"_1 then 
     let s1=newinline(simple, sets,nextset,code_1)
       if inst.label.s1 in "LIT LOCAL PARA FREF FREFB "   then  
          newinline(simple, replace(sets,toint(arg.label.code),s1),nextset,code_2)
        else 
        let s2=newinline(simple, addtosetmap(sets,toint(arg.label.code),nextset,1),nextset+1,code_2)
     tree(cnode("SET"_1,toword.nextset),[s1,s2])
   else if inst.label.code="LOCAL"_1 then
       sets_toint(arg.label.code)
   else  if inst.label.code="LOOP"_1 then
      let firstvar=toint.arg.label(code_1)
      let  l = @(+, newinline(simple, addtosetmap(sets,firstvar,nextset,nosons.code-2),nextset+nosons.code-2), empty:seq.tree.cnode, sons.code)
      tree(label.code,[tree.cnode("LIT"_1,toword.nextset)]+subseq(l,2,length.l))
   else
    let l = @(+, newinline(simple, sets,nextset), empty:seq.tree.cnode, sons.code)
  if iscallto(code , mangledname.simple )
  then 
    if "SIMPLE"_1 in flags.simple then
     subinline(mangledname.simple, l,dseq(tree.cnode("UNASIGNED"_1,"1"_1)), nextset, codetree.simple)
    else
    processpara(simple,sets,nextset,sons.code,empty:seq.tree.cnode) 
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
  else  iscallto(t,self) 

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
  else if iscallto(t,self) 
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

function noparamangled(a:word) int
 length.codedown.a-2


function genapply(prg:program, term1:word, term2:word, ptyp:word, profile:seq.word,next:word) func
  let p1 = noparamangled.term1  - 2 
  let p = noparamangled.term2 - 1 
  let nopara = 2 + p + p1 
  let newfuncmangledname = mangle("q"_1, mytype.[ next], constantseq(nopara, mytype."int"))
  assert p ≥ 0 report"illformed"+ term1 + term2 + print(lookupfunc(prg,term2))
  let insttree = buildcodetree(template(newfuncmangledname, term1, term2, p1, p, ptyp))
   func(nopara,mytype."int", newfuncmangledname, insttree, profile)
 
function parainst(i:int)seq.word {"PARA"+ toword.i }

function getnext(p:word)word 
 let q = decode.p 
  let l = if between(q_1, 48, 57)then q else [ 49, 48, 48]+ q 
  encodeword(decode.toword(((l_1 - 48)* 10 + l_2 - 48)* 10 + l_3 - 48 + 1)+ subseq(l, 4, length.l))

function template(mangledname:word, term1:word, term2:word, nopara1:int, nopara2:int, ptyp:word)seq.word 
 // PARA 1 is index PARA 2 is seq PARA 3 is result LOCAL 3 is index LOCAL 2 is seq LOCAL 1 is result // 
  // Inner loop LOCAL 3 result LOCAL 4 index LOCAL 5 length of seq // 
  // EQL-Q3DZbuiltinZintZint opGT = Q3EZbuiltinZintZint ADD = Q2BZbuiltinZintZint // 
  let CALLSELF = [ mangledname,toword(2 + nopara1 + nopara2)]
  let CALLTERM1 = [term1, toword(2 + nopara1)]
    let CALLTERM2 = [term2, toword(1 + nopara2)]
   let TERM1PARA = @(+, parainst,"", arithseq(nopara1, -1, 2 + nopara1 + nopara2))
  let TERM2PARA = @(+, parainst,"", arithseq(nopara2, -1, 2 + nopara2))
   {"X LIT 1 LOCAL 2 LIT 0 IDXUC 2 FREF"+ ptyp +"Q3DZbuiltinZintZint 2"+ TERM1PARA + TERM2PARA +"LOCAL 1 LOCAL 2 LIT 2 IDXUC 2 "
  + CALLSELF +"LOCAL 2 LIT 3 IDXUC 2 CONTINUE 2 LOCAL 2 LIT 1 IDXUC 2 LIT 3 LOCAL 4 LOCAL 5 Q3EZbuiltinZintZint 2 
     LOCAL 3"+
     TERM2PARA 
    +"LOCAL 2 LIT 0 IDXUC 2 LIT 0 Q3DZbuiltinZintZint 2 LOCAL 2 LOCAL 4 LIT 1 Q2BZbuiltinZintZint 2 IDXUC 2 LOCAL 2 LIT 0 IDXUC 2 LOCAL 2 LOCAL 4 CALLIDX 3 if 3 "
    + CALLTERM2 
  + TERM1PARA 
    +"LOCAL 3 LOCAL 6" 
  +CALLTERM1 +
  "LOCAL 4 LIT 1 Q2BZbuiltinZintZint 2 
  CONTINUE 2 SET 6 if 3 LOCAL 1 LIT 1 LOOP 4 SET 5 if 3 PARA 2 PARA 1 LOOP 4"}

  




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
  then let f = lookupfunc(p,arg.label(t2_3))
   if nosons.t2 = 5 ∧ nopara.f = 1 ∧ inst.label.codetree.f ="PARA"_1 ∧ checkistypechangeonly(arg.label(t2_4), arg.label(t2_1))
   then rexpand(p.last.l, t2_2)
   else 
     let prg = p.last.l
     let term1=arg.label(t2_(nosons.t2 - 1))
     let term2=arg.label(t2_(nosons.t2 - 2))
     let ptyp= arg.label(t2_nosons.t2)  
     let next = getnext.library.prg 
     let newf = genapply(prg, term1, term2, ptyp, profile,next)
     let p2 = newfunc(program(next,allfunctions.prg,callgraph.prg,inline.prg),newf,getarcs.newf)
   rexpand(p2, tree(cnode( mangledname.newf,"0"_1), subseq(sons.t2, 1, nosons.t2 - 3)))
  else rexpand(p.last.l, t2)

function checkistypechangeonly(term1:word, term3:word)boolean 
 // check to see if APPLY just does a type change // 
  let p = codedown.term3 
  if length.p ≠ 2 ∨ last(p_2)≠"seq"_1 ∨ p_1_1 ≠ merge."empty:seq.T"
  then false 
  else let q = codedown.term1 
  length.q = 4 ∧ last(q_2)="seq"_1 ∧ q_1_1 ="+"_1 ∧ subseq(q, 3, length.q)= ["T seq","T"]


module opt2

use buildtree

use stdlib

use passcommon

use tree.cnode

use seq.word

use seq.tree.cnode

use set.word

use seq.int
   
Function opt2(t:tree.cnode) tree.cnode
 if inst.label.t &ne "LOOP"_1 then  t else
  let newloop=
    if  inst.label.t_2="if"_1 &and inst.label.t_2_3="SET"_1 &and inst.label.t_2_3_2="LOOP"_1  then
            let innerloop=removeRECORD(t_2_3_2)
                 //  assert false report "JK"+printb(0,t_2_3_2) //
            if inst.label.innerloop="nogo"_1 then innerloop else 
            let set=t_2_3 
            let oldif = t_2
             let newset=tree(label.set,[set_1,   removeRECORD(t_2_3_2) ])
             let newif=tree(label.oldif,[oldif_1,oldif_2,newset])
              tree(label.t,[t_1,newif]+subseq(sons.t,3,nosons.t))
    else   removeRECORD(t) 
  if inst.label.newloop="nogo"_1 then t else  newloop 
    
function nogo tree.cnode tree(cnode("nogo"_1,"0"_1))

function removeRECORD(loop:tree.cnode) tree.cnode
 let first=toint.arg.label(loop_1)
         if  not (inst.label.loop_2 = "if"_1 ) then nogo else 
        let checked=asset(look(loop_2_3)+look(loop_2_1))
        let a= toseq( @(+,toword,empty:set.word,arithseq(nosons.loop-2,1,first))-checked)
        let b = toseq(checked-asset."1 2 3 4 5 6 7 8 9 10 11 12")
         // assert false report a+"/"+b // 
      if length.a &ne 1 &or length.b &ne 1   &or    not(cnode("LOCAL"_1,a_1) = label.loop_2_2 )     then nogo
    else 
        let z=decode(b_1)
        let x=decode("X"_1)_1
        let i= findindex(x,z)
        let expand=[toint.encodeword(subseq(z,1,i-1))]
        let size=toint.encodeword(subseq(z,i+1,100 ))
        let map = constantseq(expand_1,0)+1 
           let if1=ghj(map,expand,loop_2_1)
            let if2=     tree(cnode("RECORD"_1,"0"_1),   @(+,makelocal,empty:seq.tree.cnode,arithseq(size,1,first)))
            let if3=ghj(map,expand,loop_2_3)
            let init=  @(+,fix3(loop_3),empty:seq.tree.cnode,arithseq(2,1,0))+loop_4
           let newloop=tree(label.loop, [loop_1,tree(label.loop_2,[if1,if2,if3])]+init)
            newloop 

function   makelocal(i:int) tree.cnode tree.cnode("LOCAL"_1,toword.i)
 

function look(t:tree.cnode) seq.word
  // returns all local variables that are not accessed like " IDXUC(LOCAL x,LIT y) ".
     Also returns   "jXi" where j is loop variable of form RECORD(s1,s2, ... ,si) //
      if inst.label.t="CONTINUE"_1 then 
          @( aaa, checkrecord,"",sons.t ) +  @( +,look,"",sons.t )
          else
      if  inst.label.t="LOCAL"_1 then [arg.label.t]
      else if inst.label.t="IDXUC"_1 &and inst.label.t_2="LIT"_1
          &and inst.label.t_1="LOCAL"_1 then ""
      else @(+,look,"",sons.t)

function checkrecord(t:tree.cnode) word
    if  inst.label.t="SET"_1 then checkrecord(t_2)
    else   
      if inst.label.t="RECORD"_1 then toword.nosons.t
      else "X"_1
    
function  aaa(s:seq.word,t:word) seq.word
       if t="X"_1 then s+[toword(length(s)+1)] else s+merge([toword(length(s)+1)]+"X"+t)
 
function ghj(map:seq.int, expand:seq.int ,   t:tree.cnode) tree.cnode
     let inst=inst.label.t
    if inst = "LOCAL"_1  then  
       tree.cnode(inst,toword.mapit(map,arg.label.t))
    else if inst = "SET"_1  then 
      tree(cnode(inst,toword.mapit(map, arg.label.t)),[ghj(map,expand,t_1),ghj(map,expand,t_2)])
    else if inst="IDXUC"_1 &and inst.label.t_2="LIT"_1 
          &and inst.label.t_1="LOCAL"_1 &and toint.arg.label.t_1 in expand then
           tree.cnode("LOCAL"_1, toword( mapit(map,arg.label.t_1)+toint.arg.label.t_2)) 
    else if   inst="CONTINUE"_1 then
     tree(label.t,@(+,handlecontinue(map,expand,t),empty:seq.tree.cnode,arithseq(nosons.t,1,1)))  
    else  tree(label.t,@(+,ghj(map,expand),empty:seq.tree.cnode,sons.t))
         
function handlecontinue(map:seq.int,expand:seq.int,t:tree.cnode,son:int)   seq.tree.cnode
       if son in expand then 
         @(+,ghj(map,expand),empty:seq.tree.cnode,sons.t_son) 
        else [ghj(map,expand,t_son)]
        
 function fix3(t:tree.cnode, i:int) tree.cnode
        tree(cnode("IDXUC"_1,"0"_1),
           [t,tree.cnode("LIT"_1,toword.i)])

function mapit  ( map:seq.int,arg:word) int
  let i = toint.arg
   if i > length.map then last.map+i else i+map_i
