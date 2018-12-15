#!/usr/local/bin/tau

Library newimp     
 uses stdlib
 exports main newimp



Module newimp

Run test2
In testmain.c change       mainZmainZintzseq  to mainZmain2Zintzseq 
Run shell cmd  cp imp2.dylib stdlib.dylib
Run shell cmd cc stdlib/*.c -o taumain


* usegraph exclude seq

run newimp test2

Function test2 seq.word
  compilelib2("imp2"_1)  


use stdlib

use main2

use seq.mytype

use libscope

use prims

use process.seq.word

use seq.liblib

use seq.libmod

use seq.libsym

use textio

Function test1 seq.word
// compilelib2("imp2"_1) //
let zx1=createfile("stat.txt",["start"])
let t=mainA(decode."imp2"_1)
assert t="OK" report "HH"+t
 let x1=unloadlib."imp2"
 let x2=loadlib("imp2",0)
 //  let t2=mainA(decode("imp2"_1)+32+decode("main2"_1)+32+decode("compstdlib"_1))  //
  let t2=mainA(decode("test4"_1)+32+decode("test4"_1)+32+decode("test4"_1))   
t2+"&br &br"+{ if length.loadedlibs > 3 then @(seperator."&br  &br",print, "",defines.last.mods.loadedlibs_4) else "" }
+@(+,libname,"",loadedlibs)

let x=createfile("stat.txt",[t2+"&br &br"+{ if length.libs > 3 then @(seperator."&br  &br",print, "",defines.last.mods.libs_4) else "" }
+@(+,libname,"",libs)])
"KL"

