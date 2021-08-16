Module main2

use UTF8

use bits

use codegennew

use fileio

use format

use groupparagraphs

use interpreter

use libdesc

/use pass1

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
let prg10=
for  abstract=empty:seq.passsymbols, simple=empty:seq.passsymbols, m=toseq.modules.t5 do
   if isabstract.modname.m then next(abstract+m,simple) else next(abstract,simple+m)
   /for(
program.passparse( asset.abstract,asset.simple, lib,  toseq.code.t5+prg.libinfo,allsrc,mode))
let typedict= buildtypedict(empty:set.symbol,types.t5+types.libinfo) 
if mode="text"_1 then
      let zz1=tosymdefs.prg10  
     let discard=for acc = symbolref.sym.zz1_1,d= zz1 do  if paragraphno.d > 0
       then symbolref.sym.d else acc /for(acc)
        compileinfo( zz1,emptytypedict,empty:seq.libraryModule, allsrc)  
  else  
 {assert isempty.mods.libinfo report print(typedict0)+
  "NNN"+for txt="",t=types.t5 do txt+print.t+EOL /for(txt)  }
let compiled=for acc=empty:set.symbol,sd=prg.libinfo do 
        if not.isabstract.module.sym.sd  then   acc+sym.sd  else acc 
    /for(acc)
 let templates=for acc=empty:seq.symdef,p=tosymdefs.prg10 do  if para.module.sym.p = typeT then
  acc+prescan2.p else acc /for(program.asset.acc)
  let simple=for   simple=empty:seq.passsymbols  ,f=toseq.modules.t5  do
        if issimple.module.f  then simple + f else simple  
    /for(simple)
 let roots = for acc = empty:seq.symbol, f = simple do acc +  
  if name.module.f ∉ exports ∨ not.issimple.module.f then empty:seq.symbol else toseq.exports.f
 /for(acc)
   let pb=postbind(  t5 , roots ,  prg10  ,  templates  ,compiled,typedict)
  let mods=tolibraryModules(typedict,emptyprogram,  toseq.modules.t5,exports) 
let result=processOptions(prg.pb,simple,"COMPILETIME NOINLINE INLINE PROFILE STATE")
  compileinfo(tosymdefs.if option = "pass1"then result  else pass2.result  /cup templates, typedict.pb
  ,mods
,empty:seq.seq.word) 

     
  
  
  use seq.seq.mytype
  
  use typedict
  
use set.passtypes
    
use seq.symdef

use seq.libraryModule


use seq.passsymbols

use set.passsymbols

use passsymbol

use passparse

 
Function loadlibbug seq.word " bug10 "

use seq.symbolref
  
  
 ______________
 
 use set.modref
 
 
  
 Function tolibraryModules(alltypes: type2dict ,prg:program, t5:seq.passsymbols,exports:seq.word) seq.libraryModule
 for acc = empty:seq.libraryModule,typedec=empty:seq.seq.mytype, m2 =  t5 do
    if name.module.m2 /nin exports then next(acc,typedec) else
     let exps=  for acc3 = empty:seq.symbolref, e = toseq.exports.m2 do acc3 + symbolref.e /for(acc3)
    let defines=if isabstract.module.m2 then
      for acc3 = empty:seq.symbolref, e = toseq(defines.m2 ) do acc3 + symbolref.e /for(acc3)
     else exps
      let d2=if isabstract.module.m2 then defines.m2 else exports.m2
     let types = for acc5 = empty:seq.seq.mytype, s =  toseq.d2 do 
        if istype.s    then
           if isseq.resulttype.s then acc5+[resulttype.s,typeint]
           else 
                       let c= for c=empty:seq.mytype,t=flatflds(alltypes, resulttype.s) do
                 c+if isencoding.t /or t=typeword /or print.t="char" then typeint else t /for(c)
           acc5+ ([ resulttype.s]+c)
        else   acc5
       /for(acc5)
    next(acc
    + libraryModule(module.m2, 
 exps    ,if isabstract.module.m2 /and para.module.m2=typeT then 
  for accy=empty:seq.mytype,   m=toseq.uses.m2 do  accy+addabstract(typeref3(m, name.m ), para.m) /for(accy)
else empty:seq.mytype
    ,defines,types),typedec+types)
   /for(       acc   )
  
 ---------
 
 use seq.symtextpair
  
 type loadedresult is mods:seq.passsymbols,types:seq.seq.mytype ,prg:seq.symdef
 
 Export  mods(loadedresult ) seq.passsymbols
 
 Export  types(loadedresult ) seq.seq.mytype
 
 Export prg(loadedresult )seq.symdef
 
 Export type:loadedresult
 
 Function libmodules2(dependentlibs:seq.word) loadedresult
 for mods = empty:seq.passsymbols,types=empty:seq.seq.mytype,prg=empty:seq.symdef, l = loadedLibs do  
  if(libname.l)_1 ∈ dependentlibs then  
     let t= toloadedresult.l
      next(mods+mods.t, types+types.t,prg+prg.t)
  else  next(mods,types,prg)
  /for(loadedresult(mods,types,prg))
 
 function  toloadedresult(ll:liblib) loadedresult
  let  prg=        for acc=empty:seq.symdef, c=code.ll do
              let sym= (decoderef.ll)_(toint.c_1)
              let code=for acc2=empty:seq.symbol,r=c << 1 do
                   acc2+(decoderef.ll)_(toint.r)
                   /for(acc2)
                acc+symdef(sym,code)
                /for(acc)
 for   mods=empty:seq.passsymbols, types1=empty:seq.seq.mytype, m=newmods.ll do
    let defines=for defines=empty:set.symbol,r=defines.m do defines+( decoderef.ll)_toint.r
            /for(defines)
      let modx=for exports=empty:seq.symbol,types=empty:seq.mytype,r=exports.m do  
          let sym=( decoderef.ll)_toint.r  
          next(exports+sym,if name.sym="type"_1 then types+resulttype.sym else types)
      /for( passsymbols(modname.m, empty:set.modref,defines,asset.exports , empty:set.symbol  , asset.types, empty:seq.symtextpair))
      next( mods+modx, types1+types.m)
   /for(loadedresult(mods,types1,prg))  
   
   use libdesc
   
   use seq.symdef
   
   use seq.symbolref
   
  use seq.modref
 
 
   
      
_______________

use words

Function addlibrarywords(l:liblib)int let discard = addencodingpairs.words.l
 1 