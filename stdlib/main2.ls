#!/bin/sh tau tools callgraphwithin stdlib main2

Module main2

use UTF8

use bits


use compilerfront

use format

/use interpreter

use libraryModule

use standard

use symbol

use textio

use timestamp

use words

use seq.byte

use otherseq.char

use process.compileinfo

use set.modref

use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use seq.symbolref

use seq.symdef

use set.symdef

use otherseq.word

use set.word

use encoding.seq.char

use seq.seq.char

use seq.seq.mytype

use process.seq.word

use seq.seq.word

use set.seq.word

use process.seq.seq.word

use seq.seq.seq.word

/use maindict

/Function loaddictionary(file:fileresult)int // loaddict(file)// 0

/use mytype

/use process.compileinfo

Function subcompilelib(libname:seq.word)seq.word
let info = getlibraryinfo2.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
{ let b=unloadlib.[ libname]}
let cinfo = 
   {result.process.}
 compilerfront("all", libname, ["Library" + libname] + info << 3, dependentlibs, exports)
 compilerback(cinfo,libname,dependentlibs)
 
use process.compileinfo


use seq.symdef

use libdesc

use mangle


Function entrypoint(arg:UTF8) UTF8
 let wordargs=towords.arg
 let p = process.subcompilelib.[first.wordargs]
 HTML.if aborted.p then
   "COMPILATION ERROR:" + space + message.p 
 else if first.wordargs="stdlib"_1 then "OK" else
     callentrypoint( toUTF8(wordargs << 1))
     

Function astext(info:compileinfo)seq.seq.word
for acc = empty:seq.seq.word, p ∈ prg.info do acc + [ print.sym.p + print.code.p]/for(acc)

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let info = getlibraryinfo2.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
{ let b=unloadlib.[ libname]} compilerfront(option, libname, info << 3, dependentlibs, exports)

Export compilerfront(option:seq.word, libname:seq.word, allsrc:seq.seq.word, dependentlibs:seq.word, exports:seq.word)compileinfo

/use seq.libraryModule

_______________

Function addlibrarywords(l:liblib)int
let discard = addencodingpairs.words.l
1 