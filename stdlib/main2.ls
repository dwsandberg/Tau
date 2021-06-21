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

use pro2gram

use textio

use timestamp

use seq.byte

use otherseq.char

/use seq.firstpass

/use set.firstpass

use process.liblib

use seq.liblib

use seq.mytype

use set.mytype

use process.runitresult

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

function subcompilelib(option:seq.word, libname:seq.word)seq.seq.word
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
 { let b = unloadlib.[ libname]}
 let allsrc = getlibrarysrc.libname
 let link = pass1(["Library"+libname]+allsrc, exports, libmodules.dependentlibs)
   let prg4 =  pass2.result.link
    let cinfo= cinfo.link
    let libdesc= libdesc(cinfo,prg4 /cup templates.link)
   let roots=for acc= empty:set.symbol, m =mods.cinfo do 
     for acc2=acc, r=exports.m do  
      if issimple.modname.m then acc2+(symbolrefdecode.cinfo)_toint.r else acc2 /for(acc2)
    /for(acc)
   let uses = uses(prg4, roots /cup  asset.libdesc)
   let defines=definesX(prg4, uses,isempty.dependentlibs )
    {let discard =symbolref.libdesc_1
    let discard2=symbolref.libdesc_2
     let xx= for acc=empty:set.symbol,sym=toseq.(asset.symbolrefdecode.addprg(cinfo,prg4,false) -uses ) 
      do
          if  isabstract.module.sym then acc else acc +sym
        /for(acc)}
     {assert false report "DIFFXXX"+ 
       print.toseq.(uses-xx  )  +"DIFFTTT"+ 
       print.toseq.(xx -uses ) } 
      let bc = codegen(prg4, defines, uses, last.libname, libdesc, alltypes.cinfo.link , isempty.dependentlibs)
     let z2 = createlib(bc, last.libname, dependentlibs)
     ["OK"]
     
   /  function uses(p:pro2gram, processed:set.symbol, toprocess:set.symbol)set.symbol
   if isempty.toprocess then processed
 else
  let q = asset.for acc = empty:seq.symbol, @e = toseq.toprocess do
   acc
   + let d = getCode(p, @e)
     if isempty.d then constantcode.@e else d
  /for(acc)
  uses(p, processed ∪ toprocess, q - processed)

function definesX(p:pro2gram, uses:set.symbol,isbase:boolean)seq.symbol
 for acc = empty:seq.symbol, sym = toseq.uses do
  if isconstantorspecial.sym ∨ isabstract.module.sym 
     /or library.module.sym="compiled"_1
  then acc 
  else if not.isbase  /and name.module.sym /in "standard tausupport fileio" then acc
  else  acc+sym
 /for(acc)


use mytype

Function compilelib2(libname:seq.word)seq.word
let p1 = process.subcompilelib("all", libname)
if aborted.p1 then"COMPILATION ERROR:" + space + message.p1
 else
  let aa =(result.p1)_1
   if subseq(aa, 1, 1) = "OK"then aa else"COMPILATION ERROR:" + space + aa

Function main(argin:seq.byte)int
let args2 = for acc = empty:seq.seq.word, @e = break(char1.";", empty:seq.char, decodeUTF8.UTF8.argin)do
 acc + towords.@e
/for(acc)
let libname = args2_1
let compileresult = if first.libname = first."L"then"OK"
else let p = process.compilelib2.libname
 if aborted.p then message.p else result.p
let output = if length.args2 = 1 ∨ subseq(compileresult, 1, 1) ≠ "OK"then compileresult
else
 { execute function specified in arg }
 let p2 = process.runit.args2
  if aborted.p2 then message.p2
  else
   let p3 = process.interpret(alltypes.result.p2, code.result.p2)
   if aborted.p3 then message.p3 else result.p3
createfile("stdout", toUTF8bytes.output)

Function testcomp(s:seq.seq.word)seq.seq.word
let exports ="testit"
let r = pass1(s, exports, libmodules."stdlib")
for acc = empty:seq.seq.word, p = tosymdefs.result.r do
  acc + [ print.sym.p + print.code.p]
 /for(acc)

type runitresult is code:seq.symbol, alltypes:type2dict

Function runit(b:seq.seq.word)runitresult
let lib = b_1
let src = ["module $X","use standard"] + subseq(b, 2, length.b - 1)
+ ["Function runitx seq.word" + b_(length.b)]
let link = pass1(  src ,"$X", libmodules("stdlib" + lib))
let prg2 =  result.link 
runitresult(getCode(prg2, symbol(moduleref."$X","runitx", seqof.typeword)), alltypes.cinfo.link)

Function compile(option:seq.word, libname:seq.word)seq.seq.word subcompilelib(option, libname)

Function print(a:seq.seq.word)seq.word
 for acc ="", @e = a do acc + " /br  /br" + @e /for(acc)

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
 { let b = unloadlib.[ libname]}
 let allsrc = getlibrarysrc.libname
  { assert false report allsrc @ +("", @e)}
  let link = pass1(  allsrc , exports, libmodules.dependentlibs)
  let prg3 =  result.link 
   {if option = "pass1"then compileinfo(alltypes.link, prg3, roots.link)
   else let prg4 = pass2.prg3
    compileinfo(alltypes.link, prg4, roots.link)
    }
    addprg(cinfo.link,if option = "pass1"then prg3 else pass2.prg3,true)
    
    cvtL2( alltypes.link,if option = "pass1"then prg3 else pass2.prg3 ,  mods.link,exports )

_______________

Function addlibrarywords(l:liblib)int let discard = addencodingpairs.words.l
 1 