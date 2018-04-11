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
  
   
function isoption(w:word)   boolean  w in "PROFILE FORCEINLINE NOINLINE STATE "

use seq.program

function optdivide(inst:seq.word,i:int) int
// look for options at end of instruction //
    if inst_i="1"_1 &and isoption( inst_(i-1) ) then optdivide(inst,i-2) else i
    
    
    
function addtoprogram(alltypes:set.libtype,map:set.track,p:program, f:word) program
if isoption.f then // ignore options // p else 
      let asfunc = find(allfunctions.p, func( 0, mytype."", f,  tree.cnode("X"_1,"X"_1), ""))
    if length.asfunc = 1 then // already added // p else 
   let a= findelement( track(syminfoX(f)),map)
    if isempty.a then p
    else 
    let q = tosyminfo.a_1 
     let myinst =  funcfrominstruction(alltypes, instruction.q, replaceT(parameter.modname.q, returntype.q), length.paratypes.q)
    let instend = optdivide(myinst,length.myinst)
   let options =  subseq(myinst,instend,length.myinst)
  let trz = buildcodetree( subseq(myinst,1,instend))
  // remove APPLY and unneeded sets // 
  let tr=inline(  p,inline.p ,dseq(tree.cnode("UNASIGNED"_1,"1"_1)),empty:seq.tree.cnode,1,trz)
  let tr1=if inst.label.tr="STATE"_1 then tr_1 else tr
  let rt = if hasproto.q then  protoreturntype.q else  returntype.q 
  let arcs = asset.calls(mangled.q, tr1)
  // assert not (arc(mangled.q,"APPLY"_1) in arcs )report [f] //
      let isrecusive=arc(mangled.q,mangled.q) in arcs
     let tr2= if isrecusive then
          tailcall(tr1, mangled.q,length.paratypes.q)
      else tr1
  let arcs2=if  isrecusive then  asset.calls(mangled.q, tr2) else arcs 
  let flags=fixflags(tr2,length.paratypes.q,if inst.label.tr="STATE"_1 then options+"STATE" else options)
  let fn=func(length.paratypes.q, rt, mangled.q, tr2,flags)  
  let p2 =     program(library.p, add(allfunctions.p,encoding.mangledname.fn,fn),  callgraph.p +  toseq.arcs2,
           if isrecusive  &or not( "SIMPLE"_1 in flags &or "INLINE"_1 in flags) then inline.p else inline.p+mangled.q,
      if "STATE"_1 in flags.fn then hasstate.p+mangledname.fn else hasstate.p)
    @(addtoprogram(alltypes,map),head,p2,toseq(arcs2 ))
   
function fixflags(t:tree.cnode,nopara:int,oldflags:seq.word)  seq.word
      let functyp=  if "FORCEINLINE"_1 in oldflags then "INLINE"_1 else 
          if "NOINLINE"_1 in oldflags then "NOINLINE"_1 else    functype(t,nopara)
      toseq( asset.oldflags-asset."SIMPLE INLINE" + functyp )
 
function roots(m:mod2desc)set.word 
 if isabstract.modname.m ∨ isprivate.m 
  then empty:set.word 
  else  @(+, mangled, empty:set.word, toseq.export.m + toseq.defines.m)
  
       
use seq.pass1result



Function pass2(r:pass1result)pass1result 
 PROFILE.
 // does inline expansion, finds consts, removes unreaachable functions // 
    let p1=program(libname(r)_1, invertedseq.dummyfunc,newgraph.empty:seq.arc.word,asset."","")
     let roots = toseq.@(∪, roots, empty:set.word, mods.r)
      let p=@(addtoprogram(alltypes.r,@(+,track,empty:set.track,newcode.r + compiled.r)),identity,p1,roots) 
     let s2 = expandinline.p
     let statechangingfuncs =  reachable(complement.callgraph.s2, hasstate.p) &cap nodes.callgraph.s2
    // only pass on functions that can be reached from roots and are in this library // 
   let g=    reachable(callgraph.s2,roots)  - asset.@(+, mangled, empty:seq.word, compiled.r)
   // find tail calls and constants // 
   // assert not( "qZ107toolsZintZint"_1 in g) report "P"+toseq.predecessors(callgraph.s2,"qZ107toolsZintZint"_1) //
   let rr = @(+, findconstandtail(s2,statechangingfuncs), empty:seq.func, toseq.g)
   // let rrr=if  mangledname(rr_1)="dummyfunc"_1 then subseq(rr,2,length.rr)
    else  rr //
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

use opt2

use seq.seq.func



function findconstandtail(p:program,stateChangingFuncs:set.word, mangledname:word)seq.func 
 // finds constants, discards builtins, and make sure"STATE"is root on state changing functions //
  let a=codedown.mangledname
    if length.a > 1 &and  ( a_2 = "builtin"  ) then empty:seq.func else 
  let f=lookupfunc(p,mangledname)
  let q = if true  then 
       let y = opt2.codetree.f 
      let x =removerecords.y 
       // assert  y=codetree.f &or mangledname in "
     addtobitstreamZinternalbcZintZbitzbitpackedseqZinternalbc 
     buildcodetreeZbuildtreeZwordzseq
     siQ7AetypeZprocesstypesZlibtypezsetZlibtype
     addwordseqZpersistantZlinklists2Zwordzseq
     callsZsymbolZsyminfo" report "X"+mangledname  //
       inline(  p,empty:set.word,dseq(tree.cnode("UNASIGNED"_1,"1"_1)),empty:seq.tree.cnode,1,x)
     else codetree.f
     let newflags=if "STATE"_1 in flags.f  &or not ( mangledname.f in stateChangingFuncs)
       then flags.f  else flags.f+"STATE" 
     [func(nopara.f, returntype.f, mangledname.f, q, newflags)]


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

type program is record library:word, allfunctions:invertedseq.func, callgraph:graph.word, inline:set.word,hasstate:seq.word

__________________________

Simple inline expansion

use seq.program

    calls(codetree.f)


   Function expandinline(p:program) program
       if isempty.inline.p then  p else 
       let canidates= @(&cup,  predecessors(callgraph.p ), asset."",toseq.inline.p)
           // canidates will contain functions with just FREF's //
           let s0=program(library.p,allfunctions.p, callgraph.p , asset."" ,hasstate.p) 
           let s1=@(simple3.inline.p,identity,s0,toseq.canidates)
           let  usesapply=predecessors(callgraph.s1,"APPLY"_1 )
           expandinline.@(simple3(inline.p &cup asset."APPLY"),identity,s1,toseq.usesapply)
         
     

   Function simple3(inline:set.word,p:program,f:word) program
    let infunc = lookupfunc(p,f) 
         let oldarcs = arcstosuccessors(callgraph.p,f)
     let z= (@(+,head,empty:set.word,toseq.oldarcs) &cap inline ) -f
      if isempty.z then p else 
       // inline may introduce new calls that are not in z so pass full set of possible inline expansions //
   let t =  inline(p,inline, dseq(tree.cnode("UNASIGNED"_1,"1"_1)),empty:seq.tree.cnode,1,codetree.infunc)
       let flags=fixflags(t,nopara.infunc,flags.infunc)
       let newfn =func(nopara.infunc, returntype.infunc, f, t, flags)
       let newall =   add(allfunctions.p,encoding.f,newfn)
        program(library.p, newall, replacearcs(callgraph.p, oldarcs, asset.getarcs.newfn),
    if   "SIMPLE"_1 in flags &or "INLINE"_1 in flags  then  inline.p+f else inline.p ,"")


   
  
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

  


function lookupfunc(p:program,f:word) func
  let z = find(allfunctions.p, func( 0, mytype."", f,  tree.cnode("X"_1,"X"_1), ""))
  if length.z = 0 then dummyfunc else 
  value.z_1


function hash(f:func) int hash.mangledname.f

/function checksets( s:set.word,t:tree.cnode) seq.word
  if inst.label.t="SET"_1 then
     checksets(s, t_1)+ checksets(s+arg.label.t ,t_2)
  else if inst.label.t="LOCAL"_1 then
    if arg.label.t in s then "" else [arg.label.t]
 else if inst.label.t="LOOP"_1 then
   let a= toint.arg.label(t_1) 
     @(+,checksets( @(+,   toword,   s, arithseq(nosons.t-2,1,a))),"",sons.t)
 else    @(+,checksets(s+arg.label.t),"",sons.t)
     
        
function explodeinline(prg:program,inlinename:set.word,inlinetree:tree.cnode ,simple:boolean,  nextset:int, paras:seq.tree.cnode)
 tree.cnode // add sets for complex parameters and then does inline expansion. //
    if simple then
      inline(prg,inlinename,dseq(tree.cnode("UNASIGNED"_1,"1"_1)),paras,nextset,inlinetree)
    else 
     let pmap=@(addtoparamatermap,identity,parametermap(empty:seq.tree.cnode,nextset,empty:seq.ipair.tree.cnode),paras)
      let a = inline(prg,inlinename,dseq(tree.cnode("UNASIGNED"_1,"1"_1)),paramap.pmap,nextset.pmap,inlinetree)
    @(addsets,identity,a,addnodes.pmap)
    

  type parametermap is record paramap:seq.tree.cnode ,nextset:int,addnodes:seq.ipair(tree.cnode)
  
  use seq.ipair.tree.cnode
  
  use  ipair.tree.cnode
  
 
 function addtoparamatermap(p:parametermap,t:tree.cnode) parametermap
    if inst.label.t in "LIT LOCAL PARA FREF FREFB WORD"  then  parametermap(paramap.p+t,nextset.p,addnodes.p)
    else parametermap(paramap.p+tree(cnode("LOCAL"_1,toword.nextset.p)),nextset.p+1,addnodes.p+ipair(nextset.p,t))

 function addsets(t:tree.cnode,a:ipair(tree.cnode)) tree.cnode
       tree(cnode("SET"_1,toword.index.a),[value.a,t])


function addtosetmap(sets:seq.tree.cnode,old:int,new:int,numbertoadd:int) seq.tree.cnode 
 if numbertoadd=0 then sets else 
 let i = numbertoadd-1
 addtosetmap(replace(sets,old+i,tree(cnode("LOCAL"_1,toword(new+i)) )),old,new,i)
 
   
function inline(pp:program,inlinename:set.word, sets:seq(tree.cnode),paramap:seq.tree.cnode, nextset:int, code:tree.cnode)tree.cnode 
   let inst=inst.label.code   
    if nosons.code=0 &and inst in "LIT LOCAL PARA FREF FREFB WORD" then
     if inst="LOCAL"_1 then
       sets_toint(arg.label.code)
     else  if inst ="PARA"_1 &and toint.arg.label.code &le length.paramap
      then     paramap_(length.paramap - toint.arg.label.code + 1)
  else code
    else if inst="CRECORD"_1 then code
    else if inst="SET"_1 then 
     let s1=inline(pp,inlinename, sets,paramap,nextset+1,code_1)
       if inst.label.s1 in "LIT LOCAL PARA FREF FREFB WORD" 
       &or  (inst.label.s1 = "getaddressZbuiltinZTzseqZint"_1 
           &and inst.label.s1_1="LOCAL"_1 &and inst.label.s1_2="LIT"_1 ) then  
          inline(pp,inlinename,replace(sets,toint(arg.label.code),s1),paramap,nextset,code_2)
        else 
        let s2=inline(pp,inlinename,addtosetmap(sets,toint(arg.label.code),nextset,1),paramap,nextset+1,code_2)
     tree(cnode("SET"_1,toword.nextset),[s1,s2])
   else  if inst.label.code="LOOP"_1 then
      let firstvar=toint.arg.label(code_1)
      let  l = @(+, inline(pp,inlinename,addtosetmap(sets,firstvar,nextset,nosons.code-2),paramap,nextset+nosons.code-2), empty:seq.tree.cnode, sons.code)
      tree(label.code,[tree.cnode("LIT"_1,toword.nextset)]+subseq(l,2,length.l))
   else 
       let l = @(+, inline(pp,inlinename, sets,paramap,nextset), empty:seq.tree.cnode, sons.code)
     // look for simplifications //
   if inst ="RECORD"_1 
  then 
       tree(if @(&and,isconst,true,l) then cnode("CRECORD"_1,"0"_1) else label.code,l)
  else  
  if inst ="IDXUC"_1 ∧ inst.label(l_2)="LIT"_1  then 
     let idx = toint.arg.label(l_2)
     if   inst.label(l_1)="CRECORD"_1   then  
      if between(idx,0,nosons(l_1)-1) then
       (l_1)_(idx+1)
       else tree(label.code, l)
     else if inst.label(l_1)="getaddressZbuiltinZTzseqZint"_1
       &and inst.label(l_1_2)="LIT"_1 then 
       tree(label.code, [ l_1_1,tree(cnode("LIT"_1,toword(idx+toint.arg.label(l_1_2))))])
     else tree(label.code, l)  
   else  if inst="if"_1 then
       let i2=inst.label(l_1)
       if i2=  "LIT"_1 then
        if arg.label(l_1) ="1"_1 then l_2 else l_3
       else if i2="notZbuiltinZboolean"_1 then
          tree(label.code, [l_1_1,l_3,l_2])
       else tree(label.code, l)
   else 
   if inst in"Q5FZwordzseqZTzseqZint"∧ inst.label(l_2)="LIT"_1 ∧ inst.label(l_1)="CRECORD"_1 
  then // only expand when is standard sequence:that is 0 is in first field of record // 
   let cst = l_1
   let idx = toint.arg.label(l_2)
   if idx > 0 ∧  idx &le nosons(cst)-2 &and inst.label(cst_1)  ="LIT"_1 ∧ arg.label(cst_1)   ="0"_1 
   then cst_( idx + 2)
   else tree(label.code, l)
  else  
      if length.l = 2 &and inst.label(l_1)="LIT"_1 ∧ inst.label(l_2)="LIT"_1 then
       simplecalcs(label.code,toint.arg.label(l_1),toint.arg.label(l_2),l)
  else if  inst ="APPLY"_1  &and ( nosons.code &ne 5 &or nosons(l_1) > 2 )then
   expandapply(pp,inlinename,nextset,code,l)
  else    if inst in inlinename
  then // inline expansion //
   if inst ="APPLY"_1 
  then 
    if nosons.code = 5  ∧ checkistypechangeonly(pp,inlinename,arg.label(l_4),arg.label(l_3), l_1)
   then 
      inline(pp,inlinename,sets,paramap,nextset, l_2)
   else 
     // let term1=arg.label(code_(nosons.code - 1))
     let term2=arg.label(code_(nosons.code - 2))
     let ptyp= arg.label(code_nosons.code)  
     let p1 = noparamangled.term1  - 2 
     let p2 = noparamangled.term2 - 1 
     let nopara = 2 + p2 + p1 
     assert p2 ≥ 0 report"illformed"+ term1 + term2 + print(lookupfunc(pp,term2))
     let thetree=buildcodetree(   template2( term1, term2, p1, p2, ptyp) )
      explodeinline(pp,empty:set.word,thetree,false,nextset,subseq(l, 1,length.l - 3)) //
      expandapply(pp,inlinename,nextset,code,l)
    else 
        let  f=lookupfunc(pp,inst)
    explodeinline(pp,inlinename,codetree.f,"SIMPLE"_1 in flags.f,nextset,l) 
  else   
  tree(label.code, l)

 function expandapply(pp:program,inlinename:set.word, nextset:int, code:tree.cnode,l:seq.tree.cnode)tree.cnode 
     let term1=arg.label(code_(nosons.code - 1))
     let term2=arg.label(code_(nosons.code - 2))
     let ptyp= arg.label(code_nosons.code)  
     let p1 = noparamangled.term1  - 2 
     let p2 = noparamangled.term2 - 1 
     let nopara = 2 + p2 + p1 
     assert p2 ≥ 0 report"illformed"+ term1 + term2 + print(lookupfunc(pp,term2))
     let thetree=buildcodetree(   template2( term1, term2, p1, p2, ptyp) )
      explodeinline(pp,inlinename,thetree,false,nextset,subseq(l, 1,length.l - 3)) 

______________

Tailcall

Function tailcall(t:tree.cnode, self:word)boolean 
 if inst.label.t ="if"_1 
  then if tailcall(t_2, self)then true else tailcall(t_3, self)
  else if inst.label.t ="SET"_1 
  then tailcall(t_2, self)
  else if inst.label.t ="LOOP"_1 
  then false 
  else   inst.label.t= self 

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
  else if  inst.label.t= self  
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


   
   
   
   
   
 
function parainst(i:int)seq.word {"PARA"+ toword.i }

 
  function template2( term1:word, term2:word, nopara1:int, nopara2:int, ptyp:word)seq.word 
 // PARA 1 is seq PARA 2 is result LOCAL 10 is result of inner loop LOCAL 3 is seq LOCAL 2 is stk LOCAL 1 is accumulator  // 
  // Inner loop LOCAL 6 result LOCAL 7 index LOCAL 5 length of seq // 
  // EQL-Q3DZbuiltinZintZint opGT = Q3EZbuiltinZintZint ADD = Q2BZbuiltinZintZint // 
  let CALLTERM1 = [term1, toword(2 + nopara1)]
    let CALLTERM2 = [term2, toword(1 + nopara2)]
   let TERM1PARA = @(+, parainst,"", arithseq(nopara1, -1, 2 + nopara1 + nopara2))
  let TERM2PARA = @(+, parainst,"", arithseq(nopara2, -1, 2 + nopara2))
"X"+ " LIT 1
         LOCAL 3 LIT 0 IDXUC 2 FREF"+ ptyp + "Q3DZbuiltinZintZint 2
          LOCAL 1 LOCAL 2 LOCAL 3 LIT 3 IDXUC 2 STKRECORD 2 LOCAL 3 LIT 2 IDXUC 2   CONTINUE 3    
            LOCAL 3 LIT 1 IDXUC 2  
    LIT 6 
    LOCAL 7 LOCAL 5 Q3EZbuiltinZintZint 2  
      LOCAL 6"+
              TERM2PARA 
    +           "LOCAL 3 LIT 0 IDXUC 2 LIT 0 Q3DZbuiltinZintZint 2
                 LOCAL 3 LOCAL 7 LIT 1 Q2BZbuiltinZintZint 2 IDXUC 2 
                  LOCAL 3 LIT 0 IDXUC 2 
                  LOCAL 3 
                  LOCAL 7 
                 CALLIDX 3 
               if 3 "
             + CALLTERM2   
            + TERM1PARA 
            + "LOCAL 6 LOCAL 8" 
           +CALLTERM1 +
              "LOCAL 7 LIT 1 
           Q2BZbuiltinZintZint 2 
         CONTINUE 2 
       SET 8    
     if 3    
     LOCAL 1 
     LIT 1 
    LOOP 4 
   SET 5 
        LOCAL 2 LIT 0  Q3DZbuiltinZintZint 2 
        LOCAL 10 
        LOCAL 10   LOCAL 2 LIT 0 IDXUC 2   LOCAL 2 LIT 1 IDXUC 2  CONTINUE 3
        if 3 
       SET 10 
      if 3 
 PARA 2
 LIT 0 
 PARA 1
 LOOP 5 "  
 
  
function checkistypechangeonly(prg:program,inlinename:set.word,term1:word,term2:word, term3:tree.cnode)boolean 
 // check to see if APPLY just does a type change // 
  let q =  codedown.term1
  if length.q = 4 ∧ last(q_2)="seq"_1 ∧ q_1_1 ="+"_1 ∧ subseq(q, 3, length.q)= ["T seq","T"] then
     let f = lookupfunc(prg,term2)
       // let k=   inline(prg,inlinename,dseq(tree.cnode("UNASIGNED"_1,"1"_1)),empty:seq.tree.cnode,1, codetree.f)
        assert k=codetree.f report print.k+">>>>"+print.codetree.f //
     if  nopara.f = 1 ∧ inst.label.codetree.f ="PARA"_1 then
       if inst.label.term3="CRECORD"_1 &and nosons.term3=2   
          &and cnode("LIT"_1,"0"_1)=label.term3_1 &and cnode("LIT"_1,"0"_1)=label.term3_1
          then 
          // let z = [term1,term2]+print(term3)
             assert z in ["Q2BZbitszseqZTzseqZT tobitsZbitsZbit LIT 0 LIT 0 CRECORD 2",
                          "Q2BZbitszseqZTzseqZT tobitsZfileioZbyte LIT 0 LIT 0 CRECORD 2",
                          "Q2BZalphawordzseqZTzseqZT alphawordZstdlibZword LIT 0 LIT 0 CRECORD 2",
                          "Q2BZwordzseqZTzseqZT towordZstdlibZalphaword LIT 0 LIT 0 CRECORD 2",
                          "Q2BZalphawordzseqzseqZTzseqZT toalphaseqZstdlibZwordzseq LIT 0 LIT 0 CRECORD 2",
                          "Q2BZwordzseqzseqZTzseqZT towordseqZstdlibZalphawordzseq LIT 0 LIT 0 CRECORD 2",
                          "Q2BZbytezseqZTzseqZT byteZfileioZint LIT 0 LIT 0 CRECORD 2",
                          "Q2BZmytypezseqZTzseqZT mytypeZlibscopeZwordzseq LIT 0 LIT 0 CRECORD 2",
                          "Q2BZwordzarczseqZTzseqZT identityZwordzarczseqZT LIT 0 LIT 0 CRECORD 2",
                          "Q2BZsyminfozseqZTzseqZT identityZsyminfozseqZT LIT 0 LIT 0 CRECORD 2",
                          "Q2BZlibtypezarczseqZTzseqZT identityZlibtypezarczseqZT LIT 0 LIT 0 CRECORD 2",
                          "Q2BZbitzseqZTzseqZT bitZbitsZint LIT 0 LIT 0 CRECORD 2"] report "V"+z  //
          true
          else 
        // assert false report "Z"+term1+term2+print(term3) //
        false
     else 
       // if nosons.codetree.f=1 &and label.(codetree.f)_1=cnode("PARA"_1,"1"_1) then
        assert false report "Z"+term1+term2+print(term3)+print.codetree.f
        false
       else //
     false
  else false 

 // let p = codedown.term3 
      if length.p ≠ 2 ∨ last(p_2)≠"seq"_1 ∨ p_1_1 ≠ merge."empty:seq.T"
      then false 
     else true //

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
   if inst.label.t="LOOP"_1 then
     let x=removeRECORD.t
       if inst.label.x="nogo"_1 then 
       tree(label.t,@(+,opt2,empty:seq.tree.cnode,sons.t))
       else x
    else
      tree(label.t,@(+,opt2,empty:seq.tree.cnode,sons.t))



    
function nogo tree.cnode tree(cnode("nogo"_1,"0"_1))

function removeRECORD(loop:tree.cnode) tree.cnode
 let first=toint.arg.label(loop_1)
         if  not (inst.label.loop_2 = "if"_1 ) then nogo else 
        let checked=asset(look(loop_2_3)+look(loop_2_1))
        let a= toseq( @(+,toword,empty:set.word,arithseq(nosons.loop-2,1,first))-checked)
        let b = toseq(checked-asset."1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25")
         // assert false report a+"/"+b // 
      if length.a &ne 1 &or length.b &ne 1   &or    not(cnode("LOCAL"_1,a_1) = label.loop_2_2 )     then nogo
    else 
        let z=decode(b_1)
        let x=decode("X"_1)_1
        let i= findindex(x,z)
        let expand=[toint.encodeword(subseq(z,1,i-1))+first-1]
        let size=toint.encodeword(subseq(z,i+1,100 ))
        let map = constantseq(first,0)+(size-1) 
           let if1=ghj(first,map,expand,loop_2_1 )
            let if2=     tree(cnode("RECORD"_1,"0"_1),   @(+,makelocal,empty:seq.tree.cnode,arithseq(size,1,first)))
            let if3=ghj(first,map,expand,loop_2_3 )
            let init=  @(+,fix3(loop_3),empty:seq.tree.cnode,arithseq(size,1,0))+loop_4
           let newloop=tree(label.loop, [loop_1,tree(label.loop_2,[if1,if2,if3])]+init)
            assert true report "B"+printb(0,newloop)
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
 
function ghj(first:int,map:seq.int, expand:seq.int ,   t:tree.cnode) tree.cnode
     let inst=inst.label.t
    if inst = "LOCAL"_1  then  
       tree.cnode(inst,toword.mapit(map,arg.label.t))
    else if inst = "SET"_1  then 
      tree(cnode(inst,toword.mapit(map, arg.label.t)),[ghj(first,map,expand,t_1),ghj(first,map,expand,t_2)])
    else  
      if inst="IDXUC"_1 &and inst.label.t_2="LIT"_1 
          &and inst.label.t_1="LOCAL"_1 &and toint.arg.label.t_1  in expand then
           tree.cnode("LOCAL"_1, toword( mapit(map,arg.label.t_1)+toint.arg.label.t_2)) 
    else if   inst="CONTINUE"_1 then
         if inst.label(t_1)="SET"_1 then    
          let newt = tree(label.t_1 ,[ t_1_1,tree(  label.t,   [t_1_2]+subseq(sons.t,2,nosons.t)  )])
          ghj(first,map,expand,newt)
         else 
          assert inst.label.(t_1 )= "RECORD"_1 report "CONT"+printb(0,t)
          tree(label.t,@(+,handlecontinue(first,map,expand,t),empty:seq.tree.cnode,arithseq(nosons.t,1,1)))  
    else  tree(label.t,@(+,ghj(first,map,expand),empty:seq.tree.cnode,sons.t))
         
 
         
function handlecontinue(first:int,map:seq.int,expand:seq.int,t:tree.cnode,son:int)   seq.tree.cnode
       if son+first-1 in expand then 
         @(+,ghj(first,map,expand),empty:seq.tree.cnode,sons.t_son) 
        else [ghj(first,map,expand,t_son)]
        
Function printb(level:int, t:tree.cnode)seq.word 
 // for printing code tree // 
  let inst = inst.label.t 
  {"&br"+ constantseq(level,"_"_1)+
   if inst="if"_1 then
     "if"+printb(level + 1,t_1)
     +"&br"+ constantseq(level,"_"_1)+"then"
     +printb(level + 1,t_2)
     +"&br"+ constantseq(level,"_"_1)+"else"
     +printb(level + 1,t_3)
   else 
   (if inst in"PARA LIT CONST LOCAL FREF WORD FLAT"
   then [ inst, arg.label.t]
   else if inst in"CALL CALLB"
   then [ inst, toword.nosons.t, arg.label.t]
   else if inst ="SET"_1 then [ inst, arg.label.t]
   else [ inst,toword.nosons.t])+ @(+, printb(level + 1),"", sons.t)}

 function fix3(t:tree.cnode, i:int) tree.cnode
        tree(cnode("IDXUC"_1,"0"_1),
           [t,tree.cnode("LIT"_1,toword.i)])

function mapit  ( map:seq.int,arg:word) int
  let i = toint.arg
   if i > length.map then last.map+i else i+map_i
   
   
   
_____________

function check(var:word,parent:boolean,t:tree.cnode) int
 // returns 10000 if does not check. Returns max var used in tree if does checkout. parent indicates if the parent is IDXUC //
  if inst.label.t="LOCAL"_1 &and (arg.label.t = var) then 
   if parent then toint(arg.label.t) else 10000 
  else 
   @(max, check(var,inst.label.t="IDXUC"_1),if inst.label.t ="SET"_1 then toint.arg.label.t else 
   if inst.label.t = "LOOP"_1 then
      toint.arg.label(t_1)+nosons.t-3
   else 0,sons.t)
  
   
    
Function  removerecords(x:tree.cnode) tree.cnode
 let t = tree(label.x,@(+,removerecords,empty:seq.tree.cnode,sons.x))
   // assert not (inst.label.t="SET"_1 &and inst.label.t_1 in "CRECORD RECORD" &and label.t_1_1=label.t_1_2)
     report (if  check( arg.label.t,false,t_2)  then "check"else "" )+printb(0,t_2) +"VAR"+arg.label.t //
   if inst.label.t="SET"_1 &and inst.label.t_1 in "CRECORD RECORD"  
    then let chk=   check( arg.label.t,false,t_2) 
      if chk=10000 then t else 
             fix2(t,empty:seq.tree.cnode,1,chk+1)
else t

function fix2(   t:tree.cnode, replacements:seq.tree.cnode ,i:int,varbase:int) tree.cnode
 // replaces " fld1 fld2 RECORD 2 exp SET y "  with  " fld1 fld2 exp SET v2  SET v1 " //
   if i > nosons.(t_1) then  fix3(arg.label.t,replacements, t_2)
   else 
   let s=t_1_i
   if inst.label.s in "LIT LOCAL PARA FREF" then fix2(t,replacements+s,i+1,varbase)
   else 
     let var = toword(varbase+ i)
         tree(cnode("SET"_1, var) ,[ s ,fix2(t,replacements+tree(cnode("LOCAL"_1, var)),i+1,varbase)])
       


function fix3(var:word,replacements:seq.tree.cnode,t:tree.cnode) tree.cnode
// replaces IDXUC(LOCAL var,LIT i ) with replacements_(i+1) //
   if inst.label.t="IDXUC"_1 &and inst.label.t_2="LIT"_1 
          &and inst.label.t_1="LOCAL"_1 &and arg.label.t_1  = var then
            replacements_(toint.arg.label.t_2  + 1)
    else
     if inst.label.t="SET"_1 &and inst.label.t=var then t else 
     tree(label.t,@(+,fix3(var,replacements),empty:seq.tree.cnode,sons.t))
