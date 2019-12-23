#!/usr/local/bin/tau


Module prettylib

run prettylib testing2

use display

use format

use libscope

use main2

use pretty

use renamemodule

use seq.tree.word

use stack.tree.word 

use stacktrace

use stdlib

use textio

use tree.word

function plist(t:seq.word,i:int,parano:int,names:seq.word) seq.word
 if i = 1 
  then if length.names > 0 
   then"("+(if names_parano =":"_1 then""else [ names_parano]+":")+ t_i + plist(t, i + 1, parano + 1, names)
     else t
  else if t_i =".a"_1 ∨ t_i =". a"_1 
  then subseq(t, i, i + 1)+ plist(t, i + 2, parano, names)
  else if parano ≤ length.names 
  then","+(if names_parano =":"_1 then""else [ names_parano]+":")+ t_i + plist(t, i + 1, parano + 1, names)
   else  ")"+subseq(t,i,length.t) 


Function testing2 seq.word
// htmlcode("stdlib") //
  // callgraphwithin("testall","testall test11 test5 testencodings")doclibrary."stdlib"// 
  prettylib("stdlib2", "")
 


Function prettylib(libname:seq.word, namemap:seq.word)seq.word 
// Pretty prints lib source.  // 
  // Warning:Discards text before first module. Multiple modules in the same file are broken into multiple files. // 
  // Will move a beginning comment inside parentheses and fail on(a + b)* b. // 
  // namemap is form changing module names in form"oldname1 newname1 oldname2 newname2..."// 
  // To avoid destroying source it is wise to map library name to a new directory and test to make sure pretty printing did not corrupt source. //
  let discard = setmap.namemap 
prettyit(   firstPass(libname_1)  ,[mapname(libname_1  ),"/"_1] ,1,[""]) _1


function prettyit(lib:seq.seq.word,modname:seq.word,i:int,result:seq.seq.word)seq.seq.word
 if i > length.lib 
  then let x = createfile([ merge(modname +".ls")], result)
   ["Finished prettylib"]
  else let p = lib_i 
  let key = p_1 
  if key in"module"
  then let firstmod = length.modname < 3 
   let x = if firstmod then 0 else createfile([ merge(modname +".ls")], result)
         let name=mapname(p_2)
  let  newfilename=subseq(modname,1,max(length.modname-1,2))+name
    // assert false report newfilename //
   prettyit(lib, newfilename, i + 1, [ processtotext("&keyword Module"+ name + subseq(p, 3, length.p))])
  else let toadd = if key in"use"
   then"&{ block &keyword use"+ mapname(p_2)+ subseq(p, 3, length.p)+"&}"
   else if key in"Library library"
   then let u = findindex("uses"_1, p, 3)
       let e = findindex("exports"_1, p, 3)
    {"&{ block &keyword Library"+ mapname(p_2)+ alphasort.@(+, mapname,"", subseq(p, 3, u - 1))+"&br &keyword"+ subseq(p, u, e - 1)+"&br &keyword exports"+ alphasort.@(+, mapname,"", subseq(p, e + 1, length.p))+"&}"} 
   else prettyparagraph.p 
 prettyit(lib,modname,i+1,if toadd="" then result else result+[processtotext.toadd] )
 
 Function htmlcode(libname:seq.word)seq.word 
  let lib=firstPass(libname_1) 
  let modules=  @(+,findmodules,"",lib)
  {"&{ noformat <h1> Source code for Library"+ libname +"</h1> &}"+ @(+, ref,"", modules)+ @(+, prettyparagraph,"", lib)}

Function ref(modname:word)seq.word 
 {"&{ noformat <a href = &quot"+ merge("#"_1, modname)+"&quot >"+ modname +"</a> &}"}

 function findmodules(p:seq.word) seq.word 
    if p_1="module"_1 then [p_2] else ""
 
function prettyparagraph( p:seq.word) seq.word
 let key=p_1
  if key in"Library library use"
  then"&{ block &keyword"+ p +"&}"
  else if key ="module"_1 
  then"&{ block &{ noformat <hr id = &quot"+ p_2 +"&quot > &} &keyword"+ p +"&}"
  else if key ="skip"_1 
  then"&{ block &{ noformat"+ subseq(p, 2, length.p)+"&} &}"
  else if key in"export"
  then"&keyword"+ subseq(p, 3, length.p)
  else if key in"record"
  then"&keyword type"+ p_2 +"is"+ p_1 + decodefld(p, 4 + toint(p_3),"")
  else if key in"parsedfunc Parsedfunc"
  then let z = p 
   let nopara= toint(z_4)
   let headlength=toint(z_2)
   let head =(if key ="parsedfunc"_1 
    then"&keyword function"
    else"&keyword Function")+ z_3 + plist(subseq(z, 5, headlength + 2 - nopara), 1, 1, subseq(z, headlength + 2 - nopara + 1, headlength + 2))
   let tr=x(z,headlength+4,empty:stack.tree.word)
   // assert not(label.tr="builtin"_1) report "XXXX"+label.tr_1 + z_3 //
   let tr1 = if label.tr ="builtin"_1  then if
      label(tr_1)= z_3 
    then tree("builtin"_1, [ tree("usemangle"_1)])
    else if label.(tr_1)="1"_1 then
         tree("builtin"_1,[tree("NOOP"_1)])
        else if label(tr_1)="STATE"_1  &and label(tr_1_1)= z_3 then
          tree("builtin"_1,[tree("STATE"_1,[tree("usemangle"_1)])])
        else 
       // assert false report print.tr //
       tr
    else tr
 let zz=  prettytree2(defaultcontrol, tr1, head)
    //  assert not(z_3="blockit"_1) &or label.tr="export"_1 report print.tr_2_2  +z //
 zz
 else ""

function decodefld(s:seq.word,i:int,result:seq.word ) seq.word
 if i > length.s 
  then result 
  else let k = toint(s_i)
  let fld = [ s_(i + k)]+":"+ print.mytype.subseq(s, i + 1, i + k - 1)
     decodefld(s,i+k+1,if result="" then fld else result+","+fld)


function gatherarg(s:seq.word,i:int) seq.word
 if i > length.s 
  then""
  else if s_i in"0123456789"then [ s_i]+ gatherarg(s, i + 1)else""

function x(s:seq.word,i:int,stk:stack.tree.word) tree.word
 if i > length.s 
  then top.stk 
  else let w = s_i 
  if w ="FREF"_1 
  then x(s, i + 2, push(stk, tree(s_(i + 1))))
  else if w ="SET"_1 
  then let t = tree("let"_1, [ tree(s_(i + 1))]+ top(stk, 2))
     x(s,i+2,push(pop(stk,2),t))
  else if w in"LIT PARAM"
  then // let a = gatherarg(s, i + 1)// 
     // x(s,i+length.a,push(stk,tree(merge(a)))) //
   assert length.s < i + 2 ∨ not(s_(i + 2)="46"_1)report"?"
      x(s,i+2,push(stk,tree(s_(i+1))))
  else if w in"WORDS"
  then let size = toint(s_(i + 1))
      let txt= subseq(s,i+2,i+1+size) 
     let t= tree( "$wordlist"_1  ,@(+,tree,empty:seq.tree.word,txt))
     x(s,i+2+size,push(stk,t))
  else if w in"COMMENT"
  then let size = toint(s_(i + 1))
      let txt= subseq(s,i+2,i+1+size) 
   let t = tree("comment"_1, @(+, tree, [ top.stk], txt))
     x(s,i+2+size,push(pop.stk,t))
  else if w ="RECORD"_1 
  then let noargs = toint(s_(i + 1))
      let t= tree("$build"_1 ,subseq(top(stk,noargs),3,noargs))
       x(s,i+2,push(pop(stk,noargs),t))
  else if w ="APPLY"_1 
  then let noargs = toint(s_(i + 1))
     let args=top(stk,noargs)
     // assert false report print.tree("X"_1,args) //
   let term2 = codedown.label(args_(noargs - 2))
     let noargs2=length.term2-2-1
   let term1 = codedown.label(args_(noargs - 1))
     let noargs1=length.term1-2-2
   let t = tree("@"_1, [ tree(term1_1_1, subseq(args, 1, noargs1)), 
   tree(term2_1_1, subseq(args, noargs1 + 1, noargs1 + noargs2)), 
   args_(noargs1 + noargs2 + 1), 
   args_(noargs1 + noargs2 + 2)])
       x(s,i+2,push(pop(stk,noargs),t))
  else if w ="if"_1 
  then x(s, i + 1, push(pop(stk, 3), tree(w, top(stk, 3))))
  else if subseq(s, i, i + 1)="assertZbuiltinZwordzseq if"
  then x(s, i + 2, push(pop(stk, 3), tree("assert"_1, top(stk, 3))))
  else if w ="PRECORD"_1 
  then let noargs = toint(s_(i + 1))
      let args=top(stk,noargs) 
       let t=   tree("process"_1,  [ tree(getname.codedown.label(args_(noargs-1)),subseq(args,1,noargs-4))])
        x(s,i+2,push(pop(stk,noargs),t))
  else if w in"FORCEINLINE PROFILE"
  then x(s, i + 1, push(pop(stk, 1), tree(w, [ top.stk])))
  else if w="siQ7AeoftypeQ3ATZQ24typesiQ7Aezlocal "_1 then 
       x(s,i+1,push(stk,tree.merge("sizeoftype:T")))
  else  let a = codedown.w 
  assert length.a > 1 report "JJJ"+w+s+toword.i+stacktrace
   let noargs=length.a-2
    x(s,i+1,push(pop(stk,noargs),tree(getname.a,top(stk,noargs))))
    
 function getname(a:seq.seq.word) word
    let b=a_1_1 
  if length(a_2)= 1 
  then b 
  else let x = decode.b 
  let c = towordsX.decode.b 
  if length.c > 1 ∧ last.c ="T"_1 
  then merge(subseq(c, 1, length.c - 1)+ print.mytype.subseq(a_2, 1, length(a_2) - 1))
     else b
