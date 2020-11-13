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

use mangle

use seq.mytype

use set.mytype

use parse

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

function subcompilelib(libname:word)seq.word
subcompilelib("all",libname)_1


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
 let link = pass1(groupparagraphs("module Module",allsrc), exports, dependentlibs.dependentlibs)
 let prg2= postbind(alltypes.link, dict.link, roots.link,result.link,   templates.link)
 let prg3=@(processOption, identity, prg2, @(+, identity, empty:seq.seq.word, allsrc))
 if option="pass1" then  @(+,print.prg3,empty:seq.seq.word, toseq.toset.prg3)
 else 
  let prg4 = pass2(prg3,alltypes.link)
  let libdesc = libdesc(prg4, templates.link, mods.link, exports, roots.link)
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
 
Function compilelib2(libname:word)seq.word
 let p1 = process.subcompilelib.libname
  if aborted.p1 then"COMPILATION ERROR:" + space + message.p1
  else
   let aa = result.p1
    if subseq(aa, 1, 1) = "OK"then aa else"COMPILATION ERROR:" + space + aa

Function main(arg:seq.int)outputformat
 let args = towords.UTF8(arg + 10 + 10)
 let libname = args_1
 let p = process.compilelib2.libname
 let output = if aborted.p then message.p
 else if subseq(result.p, 1, 1) = "OK" ∧ length.args = 3 then
 // execute function specified in arg //
  let p2 = process.execute.mangle([ args_3], [ args_2])
   if aborted.p2 then message.p2 else result.p2
 else if subseq(result.p, 1, 1) = "OK" ∧ not(length.args = 1)then
 "not correct number of args:" + args
 else result.p
  outputformat.toseqint.toUTF8(htmlheader + processpara.output)

Function testcomp(s:seq.seq.word)seq.seq.word
 let exports ="testit"
 let allsrc = groupparagraphs("module Module", s)
 let r = pass1(allsrc, exports, dependentlibs."stdlib")
  @(+, print.result.r, empty:seq.seq.word, toseq.toset.result.r)

Function firstPass(libname:word)seq.seq.word
 subcompilelib("pass1",libname)

Function secondPass(libname:word)seq.seq.word
 subcompilelib("pass2",libname)
