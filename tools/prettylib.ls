#!/usr/local/bin/tau

run prettylib testing2

module prettylib

use stdlib

use main2

use textio

use display

use stack.tree.word 

use tree.word

use seq.tree.word

use libscope

use pretty


Function testing2 seq.word
 // callgraphwithin("testall","testall test11 test5 testencodings")  
 doclibrary."stdlib" //
  let x= prettyit(  firstPass("useful"_1),"junk"+"/" ,1,[""]) 
 @(+,   +("&br &br"),"", x)
 
@(+,   +("&br &br"),"", subseq(firstPass("test4"_1),1,20))

use format

/Function prettylib(libname:seq.word, namemap:seq.word)seq.word 
 // Pretty prints lib source. Does not create files for modules where the pretty printed version does not give the same parse tree. // 
  // Warning:Discards text before first module. Multiple modules in the same file are broken into multiple files. // 
  // Will move a beginning comment inside parentheses and fail on(a + b)* b. // 
  // namemap is form changing module names in form"oldname1 newname1 oldname2 newname2..."// 
  let lib = if length.namemap > 0 then maplib(tolibdesc(libname_1), namemap)else tolibdesc(libname_1)
  let libheader = ["#!/usr/local/bin/tau", 
  "Library"+ libname + alphasort.@(+, modname,"", subseq(modules.lib, 2, length.modules.lib))+ EOL +"uses"+ dependentlibs.lib + EOL +"exports"+ alphasort.exports.lib]
  assert @(∧, checkpretty.libheader, true, modules.lib)report"failed"
  {"PASSED"}



function prettyit(lib:seq.seq.word,modname:seq.word,i:int,result:seq.seq.word)seq.seq.word
if i > length.lib then 
let x = createfile([ merge( modname+".ls")], result) result
else 
 let p=lib_i  let key=p_1 
 if key in "module" then 
   let firstmod=length.modname < 3  
    let x = if firstmod then 0 else 
      createfile([ merge( modname+".ls")], result)
  let  newfilename=subseq(modname,1,max(length.modname-1,2))+p_2
    // assert false report newfilename //
 prettyit(lib,newfilename ,i+1, if firstmod then  ["#!/usr/local/bin/tau"]+result+[processtotext(" &keyword "+p)] else 
 [processtotext(" &keyword "+p)]  )
 else
 let toadd=
 if key in "  Library library use" then "&keyword "+p
 else if key="skip"_1 then subseq(p,2,length.p)
 else if key in "export" then "&keyword "+subseq(p,3,length.p)
 else if key in  "  Function function" then 
  let z = lib_(i+1)
  prettytree2(defaultcontrol,
 x(z,2,empty:stack.tree.word),"&keyword "+subseq(p,1,length.p-2))
 else if key in "record" then 
 "&keyword type"+ p_2 + "is"+ p_1+decodefld(p, 4+toint(p_3),"")
 else ""
 prettyit(lib,modname,i+1,if toadd="" then result else result+[processtotext.toadd] )

     function decodefld(s:seq.word,i:int,result:seq.word ) seq.word
    if i > length.s then result else
   let k=toint(s_i)
      let fld=[s_(i+k)]+":"+print.mytype(subseq(s,i+1,i+k-1))
     decodefld(s,i+k+1,if result="" then fld else result+","+fld)

function x(s:seq.word,i:int,stk:stack.tree.word) tree.word
 if i > length.s then 
 top.stk else
 let w=s_i
   if w="FREF"_1 then
    x(s,i+2,push(stk,tree(s_(i+1))))
  else if w="SET"_1 then
     let t=tree("let"_1,[ tree(s_(i+1))]+top(stk,2))
     x(s,i+2,push(pop(stk,2),t))
  else if w="LIT"_1 then
     x(s,i+2,push(stk,tree(s_(i+1))))
    else if w="WORDS"_1 then 
      let size=toint(s_(i+1))
      let txt= subseq(s,i+2,i+1+size) 
     let t= tree("$wordlist"_1 ,@(+,tree,empty:seq.tree.word,txt))
     x(s,i+2+size,push(stk,t))
    else if w="RECORD"_1 then
     let noargs=toint(s_(i+1))
      let t= tree("$build"_1 ,subseq(top(stk,noargs),3,noargs))
       x(s,i+2,push(pop(stk,noargs),t))
    else if w="APPLY"_1 then
     let noargs=toint(s_(i+1))
     let args=top(stk,noargs)
     // assert false report print.tree("X"_1,args) //
     let term2=codedown.label.args_(noargs-2)
     let noargs2=length.term2-2-1
     let term1=codedown.label.args_(noargs-1)
     let noargs1=length.term1-2-2
      let t= tree("@"_1 ,[tree(term1_1_1,subseq(args,1,noargs1)),tree(term2_1_1,subseq(args,noargs1+1,noargs1+noargs2)),
      args_(noargs1+noargs2+1),args_(noargs1+noargs2+2)])
       x(s,i+2,push(pop(stk,noargs),t))
    else if w="if"_1 then
      x(s,i+1,push(pop(stk,3),tree(w,top(stk,3))))
    else  if subseq(s,i,i+1)="assertZbuiltinZwordzseq if" then
       x(s,i+2,push(pop(stk,3), tree("assert"_1,top(stk,3))))  
 else
 let a=codedown(w) 
   let noargs=length.a-2
    x(s,i+1,push(pop(stk,noargs),tree(getname.a,top(stk,noargs))))

 function getname(a:seq.seq.word) word
    let b=a_1_1 
     if length.a_2=1 then b
    else let x=decode(b)
     let c= towordsX.decode(b)
      if length.c > 1 &and last.c="T"_1 then 
      merge(subseq(c,1,length.c-1)+print.mytype.subseq(a_2,1,length.a_2-1))
     else b
