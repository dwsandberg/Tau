#!/usr/local/bin/tau

Library newimp     
 uses stdlib
 exports main newimp



Module newimp

* usegraph exclude seq

run newimp test1


use stdlib

use main2

use seq.mytype

use libscope

use prims

use process.seq.word

use seq.liblib

use seq.libmod

use seq.libsym


Function test1 seq.word
// compilelib2("imp2"_1) //
let t=compilelib2("imp2"_1)
assert t="OK" report "HH"+t
let t2=compilelib2("test6"_1)
assert t2="OK" report "HHH"+t2
// @(+,libname,"",libs)
"&br &br"+@(seperator."&br  &br",print, "",defines.last.mods.last.libs)
//
 //  let p2 = process.execute.mangle("gentau2"_1, mytype."genhash", empty:seq.mytype) //
 let p2 = process.execute.mangle("test6"_1, mytype."test6", empty:seq.mytype)
    (if aborted.p2 then message.p2 else result.p2 )
+"&br &br"+@(seperator."&br  &br",print, "",defines.last.mods.last.libs)



 
