Module main2

use UTF8

use otherseq.char

use seq.seq.char

use codegennew

use fileio

use seq.firstpass

use set.firstpass

use format

use groupparagraphs

use interpreter

use libdesc

use process.liblib

use seq.liblib

use seq.mytype

use set.mytype

use pass1

use pass2

use postbind

use process.runitresult

use standard

use seq.symbol

use set.symbol

use symbol

use textio

use timestamp

use otherseq.word

use process.seq.word

use process.seq.seq.word

use seq.seq.seq.word

use seq.seq.word

use set.seq.word

use set.word

use baseTypeCheck

/use maindict

/Function loaddictionary(file:fileresult)int
// loaddict(file) // 0

function loadlibs(dependentlibs:seq.word, i:int, time:int)int
 if i > length.dependentlibs then time
 else
  let stamp = loadlibrary.dependentlibs_i
   assert stamp ≥ time report"library" + dependentlibs_i + "is out of date" + toword.time + toword.stamp
    loadlibs(dependentlibs, i + 1, stamp)

function subcompilelib(option:seq.word, libname :seq.word)seq.seq.word
 let info=getlibraryinfo.libname
 let dependentlibs =  info_1   
 let filelist = info_2  
 let exports =  info_3  
  // let b = unloadlib.[ libname]//
  let allsrc = getlibrarysrc.libname
  let link = pass1(groupparagraphs("module Module", allsrc), exports, libmodules.dependentlibs)
  let prg2 = postbind(alltypes.link, dict.link, roots.link,result.link, templates.link)
   let prg3 = allsrc @ +(empty:seq.seq.word, @e) @ processOption(prg2, @e)
    if option = "pass1"then
   toseq.toset.prg3 @ +(empty:seq.seq.word, print(prg3, @e))
   else
    let prg4 = pass2(prg3, alltypes.link)
     let libdesc = libdesc(alltypes.link, prg4, templates.link, mods.link, exports)
     let uses = uses(prg4, asset.roots.link + libdesc)
     let defines = defines(prg4, uses - compiled.link)
      if option = "pass2"then defines @ +(empty:seq.seq.word, print(prg4, @e))
      else if option ="baseTypeCheck" then 
       toseq.toset.prg4 @ +(["base type check"], baseTypeCheck(alltypes.link, prg4,@e))  
      else
       let bc = codegen(prg4, defines, uses, last.libname, libdesc, alltypes.link,isempty.dependentlibs)
       let z2 = createlib(bc, last.libname, dependentlibs)
        ["OK"]

Function compilelib2(libname:seq.word)seq.word
 let p1 = process.subcompilelib("all", libname)
  if aborted.p1 then"COMPILATION ERROR:" + space + message.p1
  else
   let aa =(result.p1)_1
    if subseq(aa, 1, 1) = "OK"then aa else"COMPILATION ERROR:" + space + aa
  
 use bits
 
 use seq.byte 
  
Function main(argin:seq.byte) int 
 let arg=argin @+(empty:seq.int,toint.@e) 
 let args2 = break(char1.";",empty:seq.char, decodeUTF8.UTF8.arg) @ +(empty:seq.seq.word, towords.@e)
 let libname = args2_1
 let compileresult=if first.libname=first."L" then "OK"
  else 
   let p = process.compilelib2.libname
    if aborted.p then message.p else result.p   
 let output = if length.args2 = 1 ∨  subseq(compileresult, 1, 1) &ne "OK" then compileresult
 else
  // execute function specified in arg //
  let p2 = process.runit.args2
   if aborted.p2 then message.p2 
   else 
     let p3=process.interpret(alltypes.result.p2, code.result.p2)
      if aborted.p3 then message.p3 else result.p3
     createhtmlfile("stdout",   output  )

  
Function testcomp(s:seq.seq.word)seq.seq.word
 let exports ="testit"
 let allsrc = groupparagraphs("module Module", s)
 let r = pass1(allsrc, exports, libmodules."stdlib")
  toseq.toset.result.r @ +(empty:seq.seq.word, print(result.r, @e))

Function firstPass(libname:seq.word)seq.seq.word subcompilelib("pass1", libname)

Function secondPass(libname:seq.word)seq.seq.word subcompilelib("pass2", libname)

type runitresult is record code:seq.symbol, alltypes:typedict

Function runit(b:seq.seq.word)runitresult
 let lib = b_1
 let src = ["module $X","use standard"] + subseq(b, 2, length.b - 1)
 + ["Function runitx seq.word" + b_(length.b)]
 let link = pass1([ src],"$X", libmodules("stdlib" + lib))
 let prg2 = postbind(alltypes.link, dict.link, roots.link, result.link, templates.link)
  runitresult(code.lookupcode(prg2, symbol("runitx","$X","word seq")), alltypes.link)

Function compile(option:seq.word, libname:seq.word)seq.seq.word subcompilelib(option, libname)

Function print(a:seq.seq.word)seq.word a @ +(""," &br  &br" + @e)

_______________



Function addlibrarywords(l:liblib) int let discard=addencodingpairs(words.l) 1

use encoding.seq.char
