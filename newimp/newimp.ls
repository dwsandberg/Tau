#!/usr/local/bin/tau

Library newimp other symbol pass2  cvttoinst libdescfunc newparse groupparagraphs codegen altgen codetemplates
 uses stdlib
 exports newimp  
 
Module borrow 

* usegraph include newimp pass2 newparse other libdescfunc borrow borrow2 
cvttoinst Symbol codegen altgen main exclude real seq set graph stack stdlib
bits tree ipair stacktrace


use libscope


function mytype(seq.word) mytype export

function towords(mytype) seq.word export

function =(mytype,mytype) boolean export

function mangle(word, mytype, seq.mytype)  word export

function replaceT(mytype, mytype) mytype export

function print(mytype) seq.word export

function abstracttype(mytype) word export

function parameter(mytype) mytype export

function iscomplex(mytype) boolean export

function  codedown(word) seq.seq.word export

Function libname(liblib)seq.word export

Function mods(liblib)seq.libmod export

Function types(liblib)seq.libtype export

Function returntype(libsym)seq.word export


Function instruction(libsym)seq.word export

Function fsig(libsym)word export

Function library(libmod)word export

Function parameterized(libmod)boolean export

Function modname(libmod)word export

Function defines(libmod)seq.libsym export

Function exports(libmod)seq.libsym export

Function libmod(parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym, library:word)libmod 
 export

Function liblib(a:seq.word, c:seq.libtype, d:seq.libmod)liblib export 

Function libsym(returntype:mytype, manglename:word, inst:seq.word)libsym export

Function isabstract(a:mytype)boolean export

Function print(l:libsym)seq.word export

Function emptyliblib(libname:word) liblib
export


Module newimp

run newimp test1


use stdlib

use cvttoinst

use libdescfunc

use codegen

use fileio

use other

use set.word

use pass2

use borrow

use seq.libmod

use seq.libsym

use Symbol

use seq.symbol

use set.symbol

use seq.mytype


use seq.seq.seq.word


use textio

use groupparagraphs

Function findlibclause(a:seq.seq.word, i:int)seq.word 
 assert i < length.a report"No Library clause found"
  let s = a_i 
  if s_1 ="Library"_1 then s else findlibclause(a, i + 1)


function gettext2(libname:word, e:seq.word, a:word)seq.seq.seq.word
 @(+, identity, empty:seq.seq.seq.word, groupparagraphs("module Module", gettext.[ merge([ libname]+"/"+ a +".ls")]))
 
 function print2(l:libsym) seq.word // print.l+"mn:"+// ""+ fsig.l+instruction.l

Function X(libname:seq.word)seq.word
let p1=process.X2(libname,emptysymbolset,empty:set.firstpass)
if aborted.p1 then message.p1 else // "OK"+@(+,modname,"",mods.result.p1) //
let l=result.p1  
 // @(seperator."&br  &br",print2, "",defines.last.mods.l)
 //
//  @(seperator."&br  &br",fsig, "",exports.(mods.l)_2)
//    
let known=@(+,tosymbol,emptysymbolset ,defines.last.mods.l)
// @(seperator."&br  &br",print2, "",toseq.known) //
let mods=tofirstpass.l 
// @(+,print,"",toseq.exports.(last.mods))
//
let  p2=process.X2("test6",known,asset.mods)
if aborted.p2 then message.p2 else 
@(seperator."&br  &br",print, "",defines.last.mods.result.p2)
 
 use process.liblib
 
  use set.firstpass


function X2(libname:seq.word, insyms:symbolset,  inmods:set.firstpass) liblib
let a = gettext.[ merge( libname+"/"+ libname +".ls")]
  let s = findlibclause(a, 1)
  let u = findindex("uses"_1, s, 3)
  let e = findindex("exports"_1, s, 3)
  let uses = subseq(s, u + 1, e - 1)
  let filelist = subseq(s, 2, min(u - 1, e - 1))
  let exports = subseq(s, e + 1, length.s)
  let allsrc = @(+, gettext2(s_2, exports), empty:seq.seq.seq.word, filelist)
  let p1=pass1(allsrc,exports,insyms,inmods)
  // let kk=      (symset.p1)_("wordencodingZstdlib"_1)  
  // // assert false report  
   @(+,print5,"",toseq.symset.p1)  //
 let intercode= pass2(symset.p1,toseq.roots.p1,insyms) 
 let newlibname=merge("X"+libname)
 let liblib=libdesc( roots.p1 ,intercode ,newlibname,mods.p1,symset.p1) 
 let bc=codegen5(intercode,newlibname,// if libname="test6" then emptyliblib.libname_1 else // liblib)
 let z2 = createlib(bc, newlibname, "") 
 liblib
 

  @(seperator."&br  &br",print, "",defines.last.mods.liblib)
  
  @(+,modname,"",mods.liblib)

 print.intercode
 
   
 function print5(s:symbol) seq.word
   let d=decode(mangledname.s)
   if isdefined.s &and ( modname.s=mytype."internal"
    &or   subseq(d,1,15)=   decode("siQ7AeoftypeQ3A"_1) ) then
    "&br"+print2.s else ""

 
/ type libmod is record parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym, library:word

function print2(full:boolean,l:libsym) seq.word 
   if full  then  "&br"+fsig.l+":"+print.mytype.returntype.l+instruction.l
   else [fsig.l] 


function print(l:libmod) seq.word
   "&br &br"+if parameterized.l then [modname.l]+".T" else [modname.l]
   +"&br defines:"+ @(+,print2(modname.l="$other"_1),"",defines.l ) 
    +"&br exports:"+ @(+,print2(modname.l="$other"_1),"",defines.l ) 
  
   

Function test1 seq.word
// X("imp2")
//
  let y=X("small") 
  test2 +"&br &br"+y

use main

use prims

use process.seq.word

Function test2 seq.word
 let l=loadlibrary("Xtest6"_1)
   let p2 = process.execute.mangle("test6"_1, mytype."test6", empty:seq.mytype)
    if aborted.p2 then message.p2 else result.p2 
 
 "JKL"
