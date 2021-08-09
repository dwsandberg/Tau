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

Export result(linkage)program

Export compiled(linkage)set.symbol

Export templates(linkage)program

Export cinfo(linkage)compileinfo

Export type:linkage

type linkage is result:program, compiled:set.symbol, templates:program,cinfo:compileinfo

function =(a:passsymbols, b:passsymbols)boolean module.a = module.b


Function print(b:passsymbols)seq.word
" /br  /br" + print.module.b + " /br defines" + printdict.defines.b
 + " /br unresolvedexports"
 + printdict.unresolvedexports.b


function issimple2(s:symbol)seq.symbol if isabstract.module.s then empty:seq.symbol else [ s]

use  groupparagraphs

/use program

use seq.program

use set.symdef


use set.passtypes

use passsymbol

use fileio

/type passsymbols is modname:modref, uses:set.modref, defines:set.symbol, exports:set.symbol, unresolvedexports:set.symbol
, typedict:set.mytype, text:seq.symtextpair , types:seq.seq.mytype, prg:program


types and prg is not set in new 

function print( name:seq.word,d0:       set.passsymbols) seq.word
for txt="/p",x=toseq.d0 do   txt+print.modname.x
 +{for txt2="",k=toseq.defines.x do txt2+print.k+EOL /for(txt2)
+toword.cardinality.exports.x+EOL 
+for txt2="",k=toseq.exports.x do txt2+print.k+EOL /for(txt2) 
+for txt2="",k=toseq.uses.x do txt2+print.k+EOL /for(txt2)
+}toword.cardinality.unresolvedexports.x+EOL
+for txt2="typedict /br",k=toseq.typedict.x do txt2+print.k+EOL /for(txt2)
+{for txt2="prg /br",k= toseq.data.prg.x do txt2+print.sym.k+print.code.k+EOL /for(txt2)
+}for txt2="types /br",k= types.x do txt2+print.k+EOL /for(txt2)
/for(
let discard=createfile(name,txt) "")

use set.seq.mytype

Function pass1(allsrc1:seq.seq.word, exports:seq.word, librarymods:seq.passsymbols
, libprg:program )linkage
 let libpasstypes=for acc=empty:set.passtypes,m=librarymods do 
acc+passtypes(modname.m,empty:set.mytype,typedict.m)
 /for(acc)
let lib ="?"_1
let modsx = resolvetypes(libpasstypes,allsrc1, lib)
 let t5 = resolvesymbols(allsrc1, lib, modsx,asset.librarymods )
let compiled=for acc=empty:set.symbol,sd=toseq.data.libprg do 
        if not.isabstract.module.sym.sd  then   acc+sym.sd  else acc 
    /for(acc)
  let d0 =modules.t5 
 let prg10= for  acc=libprg /cup program.code.t5,f=toseq.d0 do
     if issimple.module.f  then
       bind3(acc,  d0, f)
    else if para.module.f = typeT then 
        prescan2.bind3(acc,  d0, f)
    else acc 
  /for(acc)
let templates=for acc=empty:seq.symdef,p=toseq.data.prg10 do  if para.module.sym.p = typeT then
  acc+p else acc /for(program.asset.acc)
 let split = split(toseq.d0)
 let simple = simple.split 
 let abstract = abstract.split
 let roots = for acc = empty:seq.symbol, @e = simple do acc + roots(exports, @e)/for(acc)
 let d1 = expanduse2.d0
  let dict2=buildtypedict(empty:set.symbol,types.d1) 
 {let dict4=addtypes(buildtypedict(empty:set.symbol,typeflds.split),asset.allsymbols.d1)
 }let prg2=postbind(dict2, asset.allsymbols.d1, roots ,  prg10  ,  templates  ,compiled,typeflds.split)
 let dict3=buildtypedict(data.prg2+symdef( (defines.split)_1,toseq.defines.split),typeflds.split  ) 
 let mods=tolibraryModules(dict3,emptyprogram,  simple + abstract,exports) 
 let cinfo=cvtL2( dict3 ,emptyprogram,  mods)
 linkage(processOptions(prg2,simple,"COMPILETIME NOINLINE INLINE PROFILE STATE"), compiled,   
 templates,cinfo)
  
 use typerep
 
 Function processOptions(prg:program,mods:seq.passsymbols,option:seq.word) program
  for acc=prg ,  m=mods     do   
   if name.module.m /in option then
    for  acc2=acc  , sym=toseq.exports.m do 
          addoption(acc2,sym,[name.module.m]) 
       /for(acc2)
   else acc 
  /for(acc)

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
        if istype.s then
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
 
 



 

use seq.commoninfo

use symboldict

let uses=for  uses=set.modref,    allsymbols=empty:seq.symbol,types=empty:seq.seq.mytype, f= toseq.expanduse(modset1) do 
         next( for uses1=uses, u=toseq.uses.f do
          if issimple.u  /or para.u =typeT  then uses1 else use1+u
          /for(uses1)
         allsymbols+toseq.defines.f,types+types.f) 
 /for(        expanduse(empty:set.modref,uses,templates))

  
function  expanduse(processed:set.modref,toprocess :set.modref,templates:set.passsymbols) set.modref
  for old = processed, new=empty:set.modref ,use1 = toseq.toprocess do
      let template =  findelement(
        firstpass( if issimple.use1 /or para.use1 =typeT then use1 else moduleref([name.use1], typeT)), templates)
     assert not.isempty.template report"Cannot find module" + print.use1
     let f = template_1
     let with = para.use1
     next(old+replaceT(with, use1)
    , for acc = new, @e = toseq.uses.f do 
         if issimple.modname.f /or para.modname.f =typeT then acc
         else let n=replaceT(with, @e)
            if n /in old then acc else acc + replaceT(with, @e)
      /for(acc) )
  /for ( let new1=new-old
         if isempty.new1 then processed else
          expanduse(old,new1,templates))

function print(s:seq.modref) seq.word for acc="",m=s do acc+print.m+EOL /for(acc)

function expanduse2(modset1:set.passsymbols)expanduseresult
{let z= for acc=empty:seq.modref,f= toseq.modset1  do acc+modname.f /for(
toseq.expanduse(empty:set.modref,asset.acc,modset1))}
 let z2= for acc=empty:seq.modref,f= toseq.expanduse(modset1) do acc+modname.f /for(acc)
 {assert false report "XK"+print.toseq(asset.z2-asset.z)}
for      allsymbols=empty:seq.symbol,types=empty:seq.seq.mytype, f= z2 do 
  {if issimple.modname.f /or para.modname.f =typeT then
    next(allsymbols+toseq.defines.f,types+types.f) 
    else }
     let template =  findelement(firstpass(  if issimple.f /or para.f =typeT then f else moduleref([name.f], typeT)), modset1)
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
let x = findelement(firstpass(use1), modset)
if not.issimple.use1 ∧ para.use1 ≠ typeT then
  if isempty.x then
  let template =  findelement(firstpass( moduleref([name.use1], typeT)), modset)
  assert not.isempty.template report"Cannot find module" + print.use1
   let f = template_1
   let with = para.use1
     modset
    + firstpass(replaceT(with, module.f)
    , for acc = empty:set.modref, @e = toseq.uses.f do acc + replaceT(with, @e)/for(acc)
    , empty:set.symbol
      ,  empty:set.symbol
    ,  empty:set.symbol
    , typedict.f
    , empty:seq.seq.mytype
    , emptyprogram,text.f)
  else modset
 else assert not.isempty.x report"Cannot find module" + print.use1
  modset
/for(
if cardinality.modset > cardinality.modset1 then expanduse.modset else modset1)

use seq.modref



 type typesplit is abstract :seq.passsymbols,simple :seq.passsymbols,defines:set.symbol
 ,typeflds : seq.seq.mytype
   
function  newdict boolean false

function split(s:seq.passsymbols) typesplit
  for  abstract=empty:seq.passsymbols,simple=empty:seq.passsymbols,defines=empty:set.symbol 
   ,fldtypes=empty:seq.seq.mytype
  ,f=s do
     if issimple.module.f  then
       next( abstract, simple + f,defines /cup defines.f,fldtypes+types.f)
    else if para.module.f = typeT then 
       next(abstract+f,simple,defines /cup defines.f,fldtypes+types.f)
    else next(abstract ,simple,defines /cup defines.f,if newdict then fldtypes else fldtypes+types.f )
  /for(typesplit( abstract, simple,defines,fldtypes))
 
function bind3(p:program,  modset:set.passsymbols, f:passsymbols)program
  for acc = p, text = text.f do 
   if (text.text)_1 ∈ "Builtin builtin"then   
    let sym=sym.text
    let code2 = 
     for acc2 = empty:seq.symbol, @e = arithseq(length.paratypes.sym, 1, 1)do acc2 + Local.@e /for(acc2)
     + if issimple.module.sym then [ sym, Words."BUILTIN", Optionsym]
     else
      [ if issimplename.sym then symbol(moduleref("builtin", typeT), [ wordname.sym], paratypes.sym, resulttype.sym)
      else symbol4(moduleref("builtin", typeT), wordname.sym,(nametype.sym)_1, paratypes.sym, resulttype.sym)]
             map(acc , sym.text, code2)   
   else 
  let code = parsedcode.parse.formsymboldict(modset,f,"?"_1,"body"_1 ,empty:set.symdef,text.text)
 map(acc, sym.text, if length.code = 1 ∧ isconst.code_1 then code + [ Words."VERYSIMPLE", Optionsym]else code)
 /for(acc)



use seq.symdef

  
  use set.modref
  
  use seq.symtextpair
     
 

  
function cvttomytypes(in:set.modref) seq.mytype
for acc=empty:seq.mytype,   m=toseq.in do  acc+addabstract(typeref3(m, name.m ), para.m) /for(acc)


function roots(exported:seq.word, f:passsymbols)seq.symbol
 if name.module.f ∉ exported ∨ not.issimple.module.f then empty:seq.symbol else toseq.exports.f

use mytype

function getmod(s:seq.word, i:int)seq.word
 if s_i ∈ "."then getmod(s, i + 2) + s_(i + 1)
 else empty:seq.word 