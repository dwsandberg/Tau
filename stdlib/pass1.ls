Module pass1


use parse

use standard

use symbol

use firstpass

use textio

use words

use otherseq.passsymbols

use seq.passsymbols

use set.passsymbols


use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use set.word

use seq.seq.passsymbols

use seq.seq.word

use seq.seq.seq.word

use seq.program

use set.symdef

use set.passtypes

use passsymbol

use fileio

function =(a:passsymbols, b:passsymbols)boolean module.a = module.b

function roots(exported:seq.word, f:passsymbols)seq.symbol
 if name.module.f ∉ exported ∨ not.issimple.module.f then empty:seq.symbol else toseq.exports.f

Function print(b:passsymbols)seq.word
" /br  /br" + print.module.b + " /br defines" + printdict.defines.b
 + " /br unresolvedexports"
 + printdict.unresolvedexports.b
 
Function printdict(s:set.symbol)seq.word
 for acc ="", @e = toseq.s do acc + print.@e /for(acc)

 

function print( name:seq.word,d0:       set.passsymbols) seq.word
for txt="/p",x=toseq.d0 do   txt+print.modname.x
 +{for txt2="",k=toseq.defines.x do txt2+print.k+EOL /for(txt2)
+toword.cardinality.exports.x+EOL 
+for txt2="",k=toseq.exports.x do txt2+print.k+EOL /for(txt2) 
+for txt2="",k=toseq.uses.x do txt2+print.k+EOL /for(txt2)
+}toword.cardinality.unresolvedexports.x+EOL
+for txt2="typedict /br",k=toseq.typedict.x do txt2+print.k+EOL /for(txt2)
+{for txt2="prg /br",k= tososymdefs.prg.x do txt2+print.sym.k+print.code.k+EOL /for(txt2)
+}for txt2="types /br",k= types.x do txt2+print.k+EOL /for(txt2)
/for(
let discard=createfile(name,txt) "")

use set.seq.mytype

use passparse

Function pass1(  exports:seq.word, t5:prg6, prg10:program,compiled:set.symbol,typedict:type2dict,option:seq.word) compileinfo
 {let prg11 =addabstract(data.prg10,typedict)}    
 let templates=for acc=empty:seq.symdef,p=tosymdefs.prg10 do  if para.module.sym.p = typeT then
  acc+prescan2.p else acc /for(program.asset.acc)
  let simple=for   simple=empty:seq.passsymbols  ,f=toseq.modules.t5  do
        if issimple.module.f  then simple + f else simple  
    /for(simple)
 let roots = for acc = empty:seq.symbol, @e = simple do acc + roots(exports, @e)/for(acc)
 let d1 = expanduse2.modules.t5 
 let allsymbols=asset.allsymbols.d1
  let dict2= if true then   buildtypedict(empty:set.symbol,types.d1)  else   addtypes(typedict,allsymbols) 
 {let discard= check(typedict,dict2)}
 let prg2=postbind(dict2,  allsymbols , roots ,  prg10  ,  templates  ,compiled)
  {assert false report "K"+print.toseq.(allsymbols.tosymdefs.prg2 -allsymbols.toseq.prg11)}
 let mods=tolibraryModules(typedict,emptyprogram,  toseq.modules.t5,exports) 
let result=processOptions(prg2,simple,"COMPILETIME NOINLINE INLINE PROFILE STATE")
  compileinfo(tosymdefs.if option = "pass1"then result  else pass2.result  /cup templates, dict2
  ,mods
,empty:seq.seq.word) 
 
 
function allsymbols(s:seq.symdef) set.symbol 
  for acc=empty:seq.symbol ,   sd=s do  acc+sym.sd+code.sd /for(asset.acc)
  
 
 
  use pass2
  
 use typedict
 

 use seq.libraryModule
 
 use seq.symbolref
 
 use seq.seq.mytype
 
 
 Function tolibraryModules(alltypes: type2dict ,prg:program, t5:seq.passsymbols,exports:seq.word) seq.libraryModule
 for acc = empty:seq.libraryModule, m2 =  t5 do
    if name.module.m2 /nin exports then acc else
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
    acc
    + libraryModule(module.m2, 
 exps    ,if isabstract.module.m2 /and para.module.m2=typeT then cvttomytypes.uses.m2 else empty:seq.mytype
    ,defines,types)
   /for(acc)
   
   
 
 use postbind
 
 use program
 
 use seq.modref

use seq.symdef

  use set.modref
  
  use seq.symtextpair
     
 use mytype


use seq.commoninfo

use symboldict


  

function print(s:seq.modref) seq.word for acc="",m=s do acc+print.m+EOL /for(acc)

function expanduse2(modset1:set.passsymbols)expanduseresult
 let z2= for acc=empty:seq.modref,f= toseq.expanduse(modset1) do acc+modname.f /for(acc)
for      allsymbols=empty:seq.symbol,types=empty:seq.seq.mytype, f= z2 do 
     let template =  findelement(passsymbols(  if issimple.f /or para.f =typeT then f else moduleref([name.f], typeT)), modset1)
    assert not.isempty.template report"Cannot find module" + print.f
   let f2=template_1
     let with = para.f
      next(
      for acc = allsymbols, @e = toseq.defines.f2 do 
      if isunbound.@e then acc else acc + replaceTsymbol(with, @e) /for(acc)
      ,types+replaceTmyinternaltype(with, types.f2))
/for (expanduseresult(allsymbols,types))
  
  type expanduseresult is allsymbols:seq.symbol,types:seq.seq.mytype
  
function expanduse(modset1:set.passsymbols)set.passsymbols
 for modset = modset1, use1 = toseq.for acc = empty:set.modref, @e = toseq.modset1 do acc /cup uses.@e /for(acc)do
let x = findelement(passsymbols(use1), modset)
if not.issimple.use1 ∧ para.use1 ≠ typeT then
  if isempty.x then
  let template =  findelement(passsymbols( moduleref([name.use1], typeT)), modset)
  assert not.isempty.template report"Cannot find module" + print.use1
   let f = template_1
   let with = para.use1
     modset
    + passsymbols(replaceT(with, module.f)
    , for acc = empty:set.modref, @e = toseq.uses.f do acc + replaceT(with, @e)/for(acc))
  else modset
 else assert not.isempty.x report"Cannot find module" + print.use1
  modset
/for(
if cardinality.modset > cardinality.modset1 then expanduse.modset else modset1)

 


  
function cvttomytypes(in:set.modref) seq.mytype
for acc=empty:seq.mytype,   m=toseq.in do  acc+addabstract(typeref3(m, name.m ), para.m) /for(acc)



