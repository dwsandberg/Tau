Module main2

use UTF8

use bits

use codegennew

use compilerfront

use format

use inputoutput

use libraryModule

use standard

use symbol

use textio

use timestamp

use words

use bitcast:UTF8

use seq.byte

use otherseq.char

use process.compileinfo

use process.int

use bitcast:int

use seq.liblib

use compilerfrontT.libllvm

use pass2T.libllvm

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
let p = compileinfo:libllvm("all", getlibrarysrc.libname)
assert not.aborted.p report message.p
let cinfo = result.p
let a = break(first.src.cinfo, "uses exports", true)
let dependentlibs = a_2 << 1
let bc = codegen(last.libname, dependentlibs, cinfo)
let z2 = createlib(bc, last.libname, subseq(dependentlibs, 1, 1))
"OK"

Function entrypoint(arg:UTF8)UTF8 compile.arg

Function compile(arg:UTF8)UTF8
let wordargs = towords.arg
let p = process.subcompilelib.[first.wordargs]
if aborted.p then HTMLformat("COMPILATION ERROR in libray:" + wordargs + EOL + message.p)
else if length.wordargs = 1 ∨ wordargs_2 ∈ ". ."then
 HTMLformat("finished compiling" + first.wordargs)
else callentrypoint.toUTF8(wordargs << 1)

function callentrypoint(arg:UTF8)UTF8
let t = entrypointaddress.last.loadedLibs
if not(t > 0)then HTMLformat."callentrypoint address ERROR"
else
 let p = createthreadB(t, typeref."UTF8 UTF8", [bitcast:int(toptr.arg)], 4)
 if aborted.p then HTMLformat.message.p else bitcast:UTF8(toptr.result.p)

Function astext(info:compileinfo)seq.seq.word
for acc = empty:seq.seq.word, p ∈ prg.info do acc + [print.sym.p + print.code.p]/for(acc)

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let p = compileinfo:libllvm(option, getlibrarysrc.libname)
assert not.aborted.p report message.p
result.p

Function compilerfront:libllvm(option:seq.word, allsrc:seq.seq.word)compileinfo
let t = break(allsrc_1, "uses exports", true)
compilerfront4:libllvm(option, allsrc, depententinfo:libllvm(t_2 << 1))

Function createthreadB:libllvm(a:int, b:mytype, c:seq.int, d:int)process.int createthreadB(a, b, c, d)

function funcaddress:libllvm(sym:symbol)int funcaddress.sym

_______________

Function addlibrarywords(l:liblib)int
let discard = addencodingpairs.words.l
1

Export type:libllvm

type libllvm is a:int

Function depententinfo:libllvm(dependentlibs:seq.word)loadedresult
for org = empty:loadedresult, ll ∈ loadedLibs do
 let libname = (libname.ll)_1
 if libname ∈ dependentlibs then toloadedresult(org, libinfo.ll, libname)else org
/for(org)

Function OUTPUT(r:UTF8)int createfile("stdout", toseqbyte(toUTF8.htmlheader + r)) 