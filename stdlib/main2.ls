Module main2

use UTF8

use bits

use codegennew

use compilerfront

use format

use inputoutput

use interpreter

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

Function subcompilelib(libname:seq.word)seq.word
{OPTION PROFILE}
let info = getlibrarysrc.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
let cinfo = 
 compilerfront("all"
 , last.libname
 , ["Library" + libname] + info << 3
 , libmodules2.dependentlibs
 , exports
 )
let bc = codegen(last.libname, dependentlibs, cinfo)
let z2 = createlib(bc, last.libname, subseq(dependentlibs, 1, 1))
"OK"

Function entrypoint(arg:UTF8)UTF8 compile.arg

Function compile(arg:UTF8)UTF8
let wordargs = towords.arg
let p = process.subcompilelib.[first.wordargs]
HTML.if aborted.p then"COMPILATION ERROR in libray:" + wordargs + EOL + message.p
else if length.wordargs = 1 ∨ wordargs_2 ∈ ". ."then"finished compiling" + first.wordargs
else callentrypoint.toUTF8(wordargs << 1)

Function astext(info:compileinfo)seq.seq.word
for acc = empty:seq.seq.word, p ∈ prg.info do acc + [print.sym.p + print.code.p]/for(acc)

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let info = getlibrarysrc.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
{let b=unloadlib.[libname]}compilerfront(option, last.libname, info << 3, dependentlibs, exports)

Function compilerfront(option:seq.word, lib:word, allsrc:seq.seq.word, dependentlibs:seq.word, exports:seq.word)compileinfo
compilerfront(option, lib, allsrc, libmodules2.dependentlibs, exports)

_______________

Function addlibrarywords(l:liblib)int
let discard = addencodingpairs.words.l
1

Function libmodules2(dependentlibs:seq.word)loadedresult
for org = empty:loadedresult, ll ∈ loadedLibs do
 let libname = (libname.ll)_1
 if libname ∈ dependentlibs then toloadedresult(org, libinfo.ll, libname)else org
/for(org) 