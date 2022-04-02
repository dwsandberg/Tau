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

Function subcompilelib(info:seq.seq.word)seq.bits
{OPTION PROFILE}
let p = compileinfo:libllvm("all", info)
assert not.aborted.p report message.p
let cinfo = result.p
codegen(last.extractValue(info, "Library")
, extractValue(src.cinfo, "uses")
, cinfo
)

use process.seq.bits

Function entrypoint(arg:UTF8)UTF8 compile.getlibrarysrc.[first.towords.arg]

Function compile(info:seq.seq.word)UTF8
let libname = extractValue(info, "Library")
let p = process.subcompilelib.info
assert not.aborted.p report"COMPILATION ERROR in libray:" + libname + EOL + message.p
let discard = createfile("built/" + first.libname + ".bc", result.p)
toUTF8("Finished creating program" + libname)

Function entrywrapper(t:int, newarg:UTF8)UTF8
let p2 = 
 createthread(funcaddress.deepcopySym.typeref."UTF8 UTF8"
 , funcaddress.deepcopySym.seqof.typeword
 , t
 , [bitcast:int(toptr.newarg)]
 , 4
 )
let r = if aborted.p2 then HTMLformat.message.p2 else bitcast:UTF8(toptr.result.p2)
let discard = createfile("stdout", toseqbyte(toUTF8.htmlheader + r))
r

Function astext(info:compileinfo)seq.seq.word
for acc = empty:seq.seq.word, p ∈ prg.info do acc + [print.sym.p + print.code.p]/for(acc)

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let p = compileinfo:libllvm(option, getlibrarysrc.libname)
assert not.aborted.p report message.p
result.p

Function compilerfront(option:seq.word, info:seq.seq.word)compileinfo
let p = compileinfo:libllvm(option, info)
assert not.aborted.p report message.p
result.p

Function compilerfront:libllvm(option:seq.word, allsrc:seq.seq.word)compileinfo
compilerfront4:libllvm(option, allsrc, dependentinfo:libllvm(extractValue(allsrc, "uses")))

function funcaddress:libllvm(sym:symbol)int funcaddress.sym

use typedict

function buildargcode:libllvm(sym:symbol, typedict:typedict)int
{needed because the call interface implementation for reals is different than other types is some implementations}
for acc = 1, typ ∈ paratypes.sym + resulttype.sym do acc * 2 + if basetype(typ, typedict) = typereal then 1 else 0 /for(acc)

_______________

Function addlibrarywords(l:liblib)int
let discard = addencodingpairs.words.l
1

Export type:libllvm

type libllvm is a:int

Function dependentinfo:libllvm(dependentlibs:seq.word)loadedresult
for org = empty:loadedresult, ll ∈ loadedLibs do
 let libname = (libname.ll)_1
 if libname ∈ dependentlibs then toloadedresult(org, libinfo.ll, libname)else org
/for(org) 