Module main2

use UTF8

use bits

use codegennew

use fileio

use format


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

/use process.compileinfo

Function subcompilelib( libname:seq.word)seq.word
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
 { let b = unloadlib.[ libname]}
let cinfo={result.process.}compilerfront("all",libname,["Library"+libname]+getlibrarysrc.libname,dependentlibs,exports)
 {assert false report "XX"+print.length.symbolrefdecode}
let prg4=program.asset.prg.cinfo
let libdesc= libdesc(cinfo,prg4 )
  let bc = codegen(prg4, roots.cinfo ∪ asset.liblibflds.libdesc, last.libname, libdesc, alltypes.cinfo, isempty.dependentlibs)
let z2 = createlib(bc, last.libname, dependentlibs)
     "OK"
     
     
  
Function main(argin:seq.byte)int
let args2 = for acc = empty:seq.seq.word, @e = break(char1.";", empty:seq.char, decodeUTF8.UTF8.argin)do
 acc + towords.@e
/for(acc)
let libname = args2_1
let compileresult = if first.libname = first."L"then"OK"
else
 let p = process.subcompilelib.libname
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
   let theprg=program.asset.prg.result.p2
   let p3 = process.interpret( typedict.result.p2, getCode(theprg, symbol(moduleref."internallib $X","runitx", seqof.typeword)))
   if aborted.p3 then message.p3 else result.p3
createfile("stdout", toUTF8bytes.output)

use process.compileinfo

 Function astext(info:compileinfo) seq.seq.word
  for acc = empty:seq.seq.word, p = prg.info do
  acc + [ print.sym.p + print.code.p]
 /for(acc)
 
 
 use libraryModule

Function compilerfront(option:seq.word, libname:seq.word)compileinfo
let info = getlibraryinfo.libname
let dependentlibs = info_1
let filelist = info_2
let exports = info_3
 { let b = unloadlib.[ libname]}
 let allsrc = getlibrarysrc.libname
   compilerfront(option,libname,allsrc,dependentlibs,exports)

Function compilerfront(option:seq.word, libname:seq.word, allsrc:seq.seq.word, dependentlibs:seq.word, exports:seq.word)compileinfo
  { assert false report allsrc @ +("", @e)}
   { let libinfo=libinfo.dependentlibs}
let lib =libname_1
let libinfo=libmodules2.dependentlibs
let libpasstypes=for acc=empty:set.passtypes,m=mods.libinfo do 
         let tmp=for tmp=empty:set.mytype, t=types.libinfo do
          let mt=abstractModref.first.t 
          let mt2= if isabstract.mt then replaceT(parameter.first.t,mt) else mt 
           if mt2=modname.m then tmp+first.t else tmp
           /for(tmp)
         acc+passtypes(modname.m,tmp,typedict.m)
         /for(acc)
 { assert isempty.libpasstypes report for txt ="types", t = types.libinfo do txt + print.first.t /for(txt)+"passtypes"+ for txt ="", p = toseq.libpasstypes do txt + print.p /for(txt)}
 let mode= if option="text" then "text"_1 else "body"_1
 { figure out how to interpret text form of type }
let modsx = resolvetypes(libpasstypes,allsrc, lib)
{ figure out how to interpret text form of symbol }
    let t5 = resolvesymbols(allsrc, lib, modsx,asset.mods.libinfo )
  {assert false report  for libs=empty:seq.word, p=toseq.modules.t5 do 
  libs+library.modname.p +name.modname.p +EOL /for( libs) }
{ parse the function bodies }
     let prg10 = for abstract = empty:seq.passsymbols, simple = empty:seq.passsymbols, m = toseq.modules.t5 do
   if isabstract.modname.m then next(abstract+m,simple) else next(abstract,simple+m)
     /for(program.passparse(asset.abstract, asset.simple, lib, toseq.code.t5 + prg.libinfo, allsrc, mode))
{let discard10= for  acc=empty:set.word ,   sd=tosymdefs.prg10 do
 for acc2= acc+library.module.sym.sd ,sym=code.sd do 
  assert library.module.sym /nin ". " report "KK"+print.sym.sd+print.sym
 acc2+library.module.sym /for(acc2)
/for(toseq.acc+toword.cardinality.acc)
assert false report discard10}
let typedict= buildtypedict(empty:set.symbol,types.t5+types.libinfo) 
if mode="text"_1 then
      let zz1=tosymdefs.prg10  
      let discard = for acc = symbolref.sym.zz1_1, d = zz1 do
       if paragraphno.d > 0 then symbolref.sym.d else acc
      /for(acc)
        compileinfo( zz1,emptytypedict,empty:seq.libraryModule, allsrc,empty:set.symbol)  
  else  
 {assert isempty.mods.libinfo report print(typedict0)+
  "NNN"+for txt="",t=types.t5 do txt+print.t+EOL /for(txt)  }
       let templates = for acc = empty:seq.symdef, p = tosymdefs.prg10 do
        if para.module.sym.p = typeT then acc + p else acc
       /for(program.asset.acc)
  let roots = for acc = [symbol(modTausupport,"outofbounds",seqof.typeword)], f = toseq.modules.t5 do 
    if name.module.f ∉ exports then acc
    else if issimple.module.f then acc+toseq.exports.f 
    else 
         for acc2 = empty:seq.symbol, sym = toseq.defines.f do acc2 + getCode(prg10, sym)/for(for acc3 = acc, sym2 = toseq.asset.acc2 do
          if isabstract.module.sym2 ∨ isconstantorspecial.sym2 ∨ isBuiltin.sym2 then acc3 else acc3 + sym2
        /for(acc3) ) 
 /for(acc)
   let pb=postbind(   roots ,  prg10 ,  templates  ,typedict)
   { assert false report "LL"+toword.length.tosymdefs.prg.pb }
  { let x=tosymdefs.prg.pb 
 assert length.x > 4000 report for txt=print.length.x,sd={tosymdefs.prg10} x do
  if "COMPILETIME"_1 /in getoption.code.sd then txt+print.sym.sd +EOL else txt /for(txt) }
  let mods=tolibraryModules(typedict,emptyprogram,  toseq.modules.t5,exports) 
let result=processOptions(prg.pb,toseq.modules.t5,"COMPILETIME NOINLINE INLINE PROFILE STATE")
   compileinfo(tosymdefs.if option = "pass1"then result  else pass2.result  /cup templates, typedict.pb
  ,mods
,empty:seq.seq.word,asset.roots) 
    
  
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
 
 
  
 Function tolibraryModules(alltypes: typedict ,prg:program, t5:seq.passsymbols,exports:seq.word) seq.libraryModule
 for acc = empty:seq.libraryModule,typedec=empty:seq.seq.mytype, m2 =  t5 do
    if name.module.m2 /nin exports then next(acc,typedec) else
      let d2=if isabstract.module.m2 then defines.m2 else exports.m2
     let exps=  for acc3 = empty:seq.symbolref, e = toseq.d2 do 
      if isunbound.e then acc3 else
     acc3 + 
      symbolref.e /for(acc3)
     let types = for acc5 = empty:seq.seq.mytype, s =  toseq.d2 do 
        if istype.s    then
           if isseq.resulttype.s then acc5+[resulttype.s,typeint]
           else 
                       let c= for c=empty:seq.mytype,t=flatflds(alltypes, resulttype.s) do
                 c+if isencoding.t /or t=typeword /or t=typechar then typeint else t /for(c)
           acc5+ ([ resulttype.s]+c)
        else   acc5
       /for(acc5)
    next(acc+ libraryModule(module.m2,  exps ,types),typedec+types)
   /for(       acc   )
  
 ---------
 
 use seq.symtextpair
  
 type loadedresult is mods:seq.passsymbols,types:seq.seq.mytype ,prg:seq.symdef
 
 Export  mods(loadedresult ) seq.passsymbols
 
 Export  types(loadedresult ) seq.seq.mytype
 
 Export prg(loadedresult )seq.symdef
 
 Export type:loadedresult
 
 Function libmodules2(dependentlibs:seq.word) loadedresult
 for org=loadedresult(empty:seq.passsymbols,empty:seq.seq.mytype,empty:seq.symdef), ll = loadedLibs do  
  if(libname.ll)_1 ∈ dependentlibs then  
      toloadedresult(org,ll)
  else  org
  /for(org)
  
  function  externalname(sym:symbol,ll:liblib,prg:program,idx:int) seq.word
         if library.module.sym=(libname.ll)_1 then  [merge( libname.ll+"$$"+toword.idx)]
       else
        let externalname=externalname.getCode(prg,sym)
        if isempty.externalname then  [merge( libname.ll+"$$"+toword.idx)]  
         else externalname
  
  
 function  toloadedresult(org:loadedresult,ll:liblib) loadedresult
  let orgprg=program.asset.prg.org
  let  prg0=        for acc=orgprg, c=code.ll do
              let sym= (decoderef.ll)_(toint.c_1)
              let code=for acc2=empty:seq.symbol,r=c << 1 do
                   acc2+(decoderef.ll)_(toint.r)
                   /for(if isabstract.module.sym   then  acc2 else 
                    let externalname=externalname(sym,ll,orgprg,(toint.r))
                   addoption(acc2,externalname) )
                 symdef(sym,code) /cup acc
                /for(acc)
   let prg=   for  acc=prg0,idx=1,sym=decoderef.ll do
        if isconstantorspecial.sym ∨ isabstract.module.sym then next(acc,idx+1)
      else
         let code=getCode(prg0,sym)
         let externalname=externalname.code
         if not.isempty.externalname then next(acc,idx+1)
         else 
           next(symdef(sym,addoption(code, externalname(sym,ll,emptyprogram,idx))) /cup acc,idx+1)
      /for(acc)
 for   mods=mods.org, types1=types.org, m=newmods.ll do
        let modx=for exports=empty:seq.symbol,types=empty:seq.mytype,r=exports.m do  
 let sym =(decoderef.ll)_(toint.r)
          next(exports+sym,if name.sym="type"_1 then types+resulttype.sym else types)
      /for( passsymbols(modname.m, empty:set.modref,empty:set.symbol,asset.exports , empty:set.symbol  , asset.types, empty:seq.symtextpair))
      next( mods+modx, types1+types.m)
   /for(loadedresult(mods,types1,tosymdefs.prg))  
   
    
   use seq.symdef
   
   use seq.symbolref
   
  use seq.modref
 
 
   
_______________

use words

Function addlibrarywords(l:liblib)int let discard = addencodingpairs.words.l
 1 