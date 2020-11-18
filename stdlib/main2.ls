Module main2

use UTF8

use codegennew

use fileio

use seq.firstpass

use set.firstpass

use format

use groupparagraphs

use libdesc

use process.liblib

use seq.liblib

use seq.mytype

use set.mytype

use pass1

use pass2new

use prims

use stdlib

use seq.symbol

use set.symbol

use symbol

use textio

use timestamp

use otherseq.word

use process.seq.word

use seq.seq.seq.word

use set.seq.word

use set.word

use postbind

function loadlibs(dependentlibs:seq.word, i:int, time:int)int
 if i > length.dependentlibs then time
 else
  let stamp = loadlibrary.dependentlibs_i
   assert stamp ≥ time report"library" + dependentlibs_i + "is out of date" + toword.time + toword.stamp
    loadlibs(dependentlibs, i + 1, stamp)

function subcompilelib(option:seq.word,libname:word)seq.seq.word
 let a = gettext.[ merge([ libname] + "/" + libname + ".ls")]
 let s = findlibclause(a, 1)
 let u = findindex("uses"_1, s, 3)
 let e = findindex("exports"_1, s, 3)
 let dependentlibs = subseq(s, u + 1, e - 1)
 let filelist = subseq(s, 2, min(u - 1, e - 1))
 let exports = subseq(s, e + 1, length.s)
 // let b = unloadlib.[ libname] //
 let allsrc= getlibrarysrc.libname 
 let link = pass1(groupparagraphs("module Module",allsrc), exports, libmodules.dependentlibs)
 let prg2= postbind(alltypes.link, dict.link, roots.link,result.link,   templates.link)
 let prg3=@(processOption, identity, prg2, @(+, identity, empty:seq.seq.word, allsrc))
 if option="pass1" then  @(+,print.prg3,empty:seq.seq.word, toseq.toset.prg3)
 else 
  let prg4 = pass2(prg3,alltypes.link)
 //   assert false report  "XXX"+print(prg4, symbol("char1(word seq)","stdlib","char")) //
  let libdesc = libdesc(alltypes.link,prg4, templates.link, mods.link, exports)
  let uses = uses(prg4,asset.roots.link + libdesc)
  let defines  = defines(prg4,  uses - compiled.link )
 // let t= @(+,checkkind2(alltypes.link,prg3),"",toseq.toset.result.link)   
     let t=@(+,checkkind2(alltypes.link,prg4),"",toseq.toset.prg4) 
      assert  isempty.t report t  //
 if option="pass2" then 
    @(+,print.prg4,empty:seq.seq.word, defines)
else   
 let bc=codegen(prg4 ,defines ,uses ,libname,libdesc,alltypes.link)
 let z2 = createlib(bc, libname, dependentlibs)
 // let save = @(+, bindingformat.symset.link, empty:seq.seq.word, mods.link)
 let name = merge("pass1/" + libname + "." + print.currenttime + ".txt") 
 let z = createfile([ name], save) //
 [ "OK" ]
 
use process.seq.seq.word
 
Function compilelib2(libname:word)seq.word
 let p1 = process.subcompilelib("all",libname)
  if aborted.p1 then"COMPILATION ERROR:" + space + message.p1
  else
   let aa = (result.p1)_1
    if subseq(aa, 1, 1) = "OK"then aa else"COMPILATION ERROR:" + space + aa

use otherseq.char

use seq.seq.char

use seq.seq.word

Function main(arg:seq.int)outputformat
 let args2=@(+,  towords,empty:seq.seq.word,break(char1(";"),decodeUTF8.UTF8(arg),1))
 let libname = args2_1_1
 let p = process.compilelib2.libname
 let output = if aborted.p then message.p
 else if length.args2=1 &or not( subseq(result.p, 1, 1) = "OK") then result.p
 else // execute function specified in arg //
 let p2=process.runit.args2
 if aborted.p2 then message.p2 else  interpret(alltypes.result.p2,code.result.p2)
 outputformat.toseqint.toUTF8(htmlheader + processpara.output)

  
    
  use interpreter


Function testcomp(s:seq.seq.word)seq.seq.word
 let exports ="testit"
 let allsrc = groupparagraphs("module Module", s)
 let r = pass1(allsrc, exports, libmodules."stdlib")
  @(+, print.result.r, empty:seq.seq.word, toseq.toset.result.r)

Function firstPass(libname:word)seq.seq.word
 subcompilelib("pass1",libname)

Function secondPass(libname:word)seq.seq.word
 subcompilelib("pass2",libname)
 

use process.runitresult
 
type runitresult is record code:seq.symbol,alltypes:typedict
  
 Function runit(b:seq.seq.word) runitresult
    let lib=b_1
   let src=["module $X","use stdlib"]+subseq(b,2,length.b-1)+[ " Function runitx seq.word "+b_length.b ] 
   let link = pass1([src], "$X", libmodules("stdlib"+lib))
   let prg2= postbind(alltypes.link, dict.link, roots.link,result.link,   templates.link)
    runitresult(code.lookupcode(prg2,symbol("runitx","$X","word seq")),alltypes.link)

 
 Function compile(option:seq.word, libname:seq.word )seq.seq.word
   subcompilelib(option,libname_1)

