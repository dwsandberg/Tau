Module main2

use UTF8

use bits

use codegennew

use compilerfront

use format

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

/use maindict

/Function loaddictionary(file:fileresult)int // loaddict(file)// 0

/use mytype

/use process.compileinfo

Function subcompilelib(libname:seq.word)seq.word
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
{ let b = unloadlib.[ libname]}
let cinfo =
 { result.process.}
 compilerfront("all"
 , libname
 , ["Library" + libname] + getlibrarysrc.libname
 , dependentlibs
 , exports
 )
let prg4 = asset.prg.cinfo
let libdesc = libdesc(cinfo, prg4)
let bc =
 codegen(prg4
 , roots.cinfo ∪ asset.liblibflds.libdesc
 , last.libname
 , libdesc
 , typedict.cinfo
 , isempty.dependentlibs
 )
let z2 = createlib(bc, last.libname, dependentlibs)
"OK"

Function main(argin:seq.byte)int
let args2 =
 for acc = empty:seq.seq.word, @e ∈ break(char1.";", empty:seq.char, decodeUTF8.UTF8.argin)do acc + towords.@e /for(acc)
let libname = args2_1
let compileresult =
 if first.libname = first."L"then"OK"
 else
  let p = process.subcompilelib.libname
  if aborted.p then"COMPILATION ERROR:" + space + message.p else result.p
let output =
 if length.args2 = 1 ∨ subseq(compileresult, 1, 1) ≠ "OK"then compileresult
 else
  { execute function specified in arg }
  let lib = args2_1
  let src =
   ["module $X","use standard"] + subseq(args2, 2, length.args2 - 1)
   + ["Function runitx seq.word" + args2_(length.args2)]
  let p2 =
   process.compilerfront("pass1","runit", src,"stdlib" + lib,"$X")
  if aborted.p2 then message.p2
  else
   let theprg = asset.prg.result.p2
   let p3 =
    process.interpret(typedict.result.p2
    , getCode(theprg, symbol(moduleref."runit $X","runitx", seqof.typeword))
    )
   if aborted.p3 then message.p3 else result.p3
createfile("stdout", toUTF8bytes.output)

Function astext(info:compileinfo)seq.seq.word
for acc = empty:seq.seq.word, p ∈ prg.info do acc + [ print.sym.p + print.code.p]/for(acc)

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
{ let b = unloadlib.[ libname]}
let allsrc = getlibrarysrc.libname
compilerfront(option, libname, allsrc, dependentlibs, exports)

Export compilerfront(option:seq.word, libname:seq.word, allsrc:seq.seq.word, dependentlibs:seq.word, exports:seq.word)compileinfo

/use seq.libraryModule

_______________

Function addlibrarywords(l:liblib)int
let discard = addencodingpairs.words.l
1 