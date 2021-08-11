Module main2

use UTF8

use bits

use codegennew

use fileio

use format

use groupparagraphs

use interpreter

use libdesc

use pass1

use pass2

use postbind

use standard

use symbol

use program

use textio

use timestamp

use seq.byte

use otherseq.char


use process.liblib

use seq.liblib

use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use otherseq.word

use set.word

use encoding.seq.char

use seq.seq.char

use process.seq.word

use seq.seq.word

use set.seq.word

use process.seq.seq.word

use seq.seq.seq.word


/use maindict

/Function loaddictionary(file:fileresult)int // loaddict(file)// 0

function loadlibs(dependentlibs:seq.word, i:int, time:int)int
 if i > length.dependentlibs then time
 else
  let stamp = loadlibrary.dependentlibs_i
   assert stamp ≥ time report"library" + dependentlibs_i + "is out of date" + toword.time + toword.stamp
    loadlibs(dependentlibs, i + 1, stamp)

use set.symdef

use seq.program

use mytype


Function subcompilelib( libname:seq.word)seq.word
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
 { let b = unloadlib.[ libname]}
let cinfo=compilerfront("all",libname,["Library"+libname]+getlibrarysrc.libname,dependentlibs,exports)
let prg4=program.asset.prg.cinfo
let libdesc= libdesc(cinfo,prg4 )
let uses = uses(prg4 , roots.cinfo /cup  asset.libdesc)
let bc = codegen(prg4,  uses, last.libname, libdesc, alltypes.cinfo , isempty.dependentlibs)
let z2 = createlib(bc, last.libname, dependentlibs)
     "OK"
     
     
  
Function main(argin:seq.byte)int
let args2 = for acc = empty:seq.seq.word, @e = break(char1.";", empty:seq.char, decodeUTF8.UTF8.argin)do
 acc + towords.@e
/for(acc)
let libname = args2_1
let compileresult = if first.libname = first."L"then"OK"
else let p = process.subcompilelib( libname)
 if aborted.p then "COMPILATION ERROR:" + space + message.p else result.p
let output = if length.args2 = 1 ∨ subseq(compileresult, 1, 1) ≠ "OK"then compileresult
else
 { execute function specified in arg }
 let lib = args2_1
let src = ["module $X","use standard"] + subseq(args2, 2, length.args2 - 1)
+ ["Function runitx seq.word" + args2_(length.args2)]
let p2=process.compilerfront("pass1", "runit",src,"stdlib" + lib,"$X")
  if aborted.p2 then message.p2
  else
   let p3 = process.interpret(typedict.result.p2, getCode(program.asset.prg.result.p2
   , symbol(moduleref."$X","runitx", seqof.typeword)))
   if aborted.p3 then message.p3 else result.p3
createfile("stdout", toUTF8bytes.output)

use process.compileinfo

 Function astext(info:compileinfo) seq.seq.word
  for acc = empty:seq.seq.word, p = prg.info do
  acc + [ print.sym.p + print.code.p]
 /for(acc)
 
 use program

/Function print(a:seq.seq.word)seq.word
 for acc ="", @e = a do acc + " /br  /br" + @e /for(acc)

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
 { let b = unloadlib.[ libname]}
 let allsrc = getlibrarysrc.libname
   compilerfront(option,libname,allsrc,dependentlibs,exports)

Function compilerfront(option:seq.word,libname:seq.word
,allsrc:seq.seq.word,dependentlibs:seq.word,exports:seq.word) compileinfo
  { assert false report allsrc @ +("", @e)}
   { let libinfo=libinfo.dependentlibs}
let lib ="?"_1
let libinfo=libmodules2.dependentlibs
let libpasstypes=for acc=empty:set.passtypes,m=mods.libinfo do 
         acc+passtypes(modname.m,empty:set.mytype,typedict.m)
         /for(acc)
 let mode= if option="text" then "text"_1 else "body"_1
 { figure out how to interpret text form of type }
let modsx = resolvetypes(libpasstypes,allsrc, lib)
{ figure out how to interpret text form of symbol }
let t5 = resolvesymbols(allsrc, lib, modsx,asset.mods.libinfo )
{ parse the function bodies }
let prg10 = program.passparse(modules.t5, lib, modsx, toseq.code.t5+prg.libinfo,allsrc,mode)
let typedict0= buildtypedict(empty:set.symbol,types.t5+types.libinfo) 
 {assert isempty.mods.libinfo report print(typedict0)+
  "NNN"+for txt="",t=types.t5 do txt+print.t+EOL /for(txt)  }
let compiled=for acc=empty:set.symbol,sd=prg.libinfo do 
        if not.isabstract.module.sym.sd  then   acc+sym.sd  else acc 
    /for(acc)
     pass1(exports , t5 , prg10 ,compiled ,typedict0,option)
     
  
  
  use seq.seq.mytype
  
  use typedict
  
use set.passtypes
    
use seq.symdef

use seq.libraryModule

use firstpass

use seq.passsymbols

use set.passsymbols

use passsymbol

use passparse

 
Function loadlibbug seq.word " bug10 "

use seq.symbolref
  
  
 
  
      
_______________

use words

Function addlibrarywords(l:liblib)int let discard = addencodingpairs.words.l
 1 