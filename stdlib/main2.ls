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

use set.symdef

use seq.program

Function subcompilelib(option:seq.word, libname:seq.word)seq.seq.word
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
 { let b = unloadlib.[ libname]}
 let allsrc = getlibrarysrc.libname
 { let cinfo=compilerfront(option,libname,allsrc,dependentlibs,exports)
    let prg4=pro2gram.asset.prg.cinfo
}
let libinfo=libinfo.dependentlibs
let link = pass1(["Library"+libname]+allsrc, exports, mods.libinfo,simple.libinfo,abstract.libinfo)
let prg4 =  pass2.result.link /cup templates.link
let cinfo= cinfo.link
let libdesc= libdesc(cinfo,prg4 )
let uses = uses(prg4 , roots.cinfo /cup  asset.libdesc)
    {let discard =symbolref.libdesc_1
    let discard2=symbolref.libdesc_2
     let xx= for acc=empty:set.symbol,sym=toseq.(asset.symbolrefdecode.addprg(cinfo,prg4,false) -uses ) 
      do
          if  isabstract.module.sym then acc else acc +sym
        /for(acc)}
     {assert false report "DIFFXXX"+ 
       print.toseq.(uses-xx  )  +"DIFFTTT"+ 
       print.toseq.(xx -uses ) } 
      let bc = codegen(prg4,  uses, last.libname, libdesc, alltypes.cinfo , isempty.dependentlibs)
     let z2 = createlib(bc, last.libname, dependentlibs)
     ["OK"]
     

function compare(a:program,b:program) seq.word
 for acc="",sym = toseq.a do
  if  getCode(a,sym)= getCode(b,sym)  then acc else acc+print.sym
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
let libinfo=libinfo."stdlib"
let r = pass1(s, exports, mods.libinfo,simple.libinfo,abstract.libinfo)
for acc = empty:seq.seq.word, p = tosymdefs.result.r do
  acc + [ print.sym.p + print.code.p]
 /for(acc)

type runitresult is code:seq.symbol, alltypes:type2dict

function runit(b:seq.seq.word)runitresult
let lib = b_1
let src = ["module $X","use standard"] + subseq(b, 2, length.b - 1)
+ ["Function runitx seq.word" + b_(length.b)]
let libinfo=libinfo("stdlib" + lib)
let link = pass1(  src ,"$X",mods.libinfo,simple.libinfo,abstract.libinfo)  
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
   compilerfront(option,libname,allsrc,dependentlibs,exports)

Function compilerfront(option:seq.word,libname:seq.word
,allsrc:seq.seq.word,dependentlibs:seq.word,exports:seq.word) compileinfo
  { assert false report allsrc @ +("", @e)}
  let libinfo=libinfo.dependentlibs
  let link = pass1(  allsrc , exports, mods.libinfo,simple.libinfo,abstract.libinfo)
  let prg3 =  result.link 
  addprg(cinfo.link,if option = "pass1"then prg3 else pass2.prg3 /cup templates.link)
    
use seq.libraryModule

use program

use seq.firstpass

use seq.myinternaltype

Function loadlibbug seq.word " bug10 "

use seq.symbolref
  
  
  type libinfo is mods:seq.firstpass,simple:program,abstract:program 
 
  function  libinfo(   dependentlibs:seq.word) libinfo
  for acc = libinfo(empty:seq.firstpass,emptyprogram,emptyprogram), l = loadedLibs do 
  if(libname.l)_1 ∈ dependentlibs then  
    for ab = abstract.acc,simple=simple.acc,c=code.l do
       let sym=(decoderef.l)_toint.first.c
       if isunbound.sym then next(ab,simple) 
       else
       let code=  for acc2=empty:seq.symbol,r=c << 1 do  
          acc2+ (decoderef.l)_toint.r /for(acc2)
        if isabstract.module.sym then 
           next(map(ab,sym,code ), simple) 
        else next(ab,map(simple,sym,code  ) )
       /for( libinfo( mods.acc+cvtnewmods(newmods.l,decoderef.l), simple,  ab )   )
  else acc
  /for(acc)
 
  

function  cvtnewmods(ll:seq.libraryModule,decoderef:seq.symbol) seq.firstpass
for acc=empty:seq.firstpass,m=ll  do
   let e=  for acc2=empty:set.symbol,r=exports.m do  acc2+ (decoderef)_toint.r /for(acc2)
   let d= for acc2=empty:set.symbol,r=defines.m do 
      let sym=(decoderef)_toint.r
      if isunbound.sym then acc2 else 
      acc2+ sym /for(acc2)
   let types=  for acc2=empty:seq.myinternaltype, t=types.m do
      acc2+myinternaltype(if isabstract.modname.m then "undefined"_1
    else "defined"_1, abstracttype.first.t, module2.first.t, t << 1 )
      /for(acc2)
         acc+firstpass(modname.m, uses.m, d, e, types)
 /for(acc)
 
_______________

Function addlibrarywords(l:liblib)int let discard = addencodingpairs.words.l
 1 