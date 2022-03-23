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

Function subcompilelib(args:seq.word)seq.word
{OPTION PROFILE}
let libname = [first.args]
let info = getlibrarysrc.libname
let p = compileinfo:libllvm("all", getlibrarysrc.libname)
assert not.aborted.p report message.p
let cinfo = result.p
let a = break(first.src.cinfo, "uses exports", true)
let dependentlibs = a_2 << 1
let bc = codegen(last.libname, dependentlibs, cinfo)
let z2 = createfile("built/"+ last.libname+".bc", bc )
"OK"

Function entrypoint(arg:UTF8)UTF8 compile.arg

Function compile(arg:UTF8)UTF8
let wordargs = towords.arg
let p = process.subcompilelib.wordargs 
assert not.aborted.p report ("COMPILATION ERROR in libray:" + wordargs + EOL + message.p)
toUTF8.("Finished creating program"+space)+arg

 
Function entrywrapper(t:int,newarg:UTF8) UTF8
 let p2 = 
    createthread(funcaddress.deepcopySym.typeref."UTF8 UTF8" 
   , funcaddress.deepcopySym.seqof.typeword
   , t
   , [bitcast:int(toptr.newarg)]
   , 4
   )
 let r=if aborted.p2 then HTMLformat.message.p2 else bitcast:UTF8(toptr.result.p2)
  let discard=createfile("stdout", toseqbyte(toUTF8.htmlheader + r))
  r
 


Function astext(info:compileinfo)seq.seq.word
for acc = empty:seq.seq.word, p ∈ prg.info do acc + [print.sym.p + print.code.p]/for(acc)

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let p = compileinfo:libllvm(option, getlibrarysrc.libname)
assert not.aborted.p report message.p
result.p

Function compilerfront:libllvm(option:seq.word, allsrc:seq.seq.word)compileinfo
let t = break(allsrc_1, "uses exports", true)
compilerfront4:libllvm(option, allsrc, dependentinfo:libllvm(t_2 << 1))

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
