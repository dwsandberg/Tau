#!/usr/local/bin/tau

Library newimp other symbol pass2  cvttoinst libdescfunc newparse
 uses stdlib
 exports newimp  
 
Module borrow 

use libdesc

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

function tolibdesc(word) libdesc export

Function src(moddesc)seq.seq.word export

Function modules(l:libdesc)seq.moddesc export

Function exports(l:libdesc) seq.word export

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

use libscope

use seq.libmod

use seq.libsym

use Symbol

use seq.symbol

use set.symbol

use seq.mytype

Function X(libname:seq.word)seq.word 
 let p1=pass1(libname) 
 // @(+,print5,"",toseq.symset.p1) //
 let intercode= pass2(symset.p1,toseq.roots.p1) 
 let newlibname="testx"_1
 let liblib=libdesc( roots.p1 ,intercode ,newlibname,mods.p1) 
 let bc=codegen5(intercode,newlibname,liblib)
 let z2 = createlib(bc, newlibname, "") 
 print.intercode
 
  @(+,print,"",mods.liblib)
  
 function print5(s:symbol) seq.word
   if isdefined.s &and nopara.s=1 &and resulttype.s=(paratypes.s)_1 then
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
  X("stdlib")
