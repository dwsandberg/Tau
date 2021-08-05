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

Function pass1(allsrc1:seq.seq.word, exports:seq.word, librarymods:seq.passsymbols
, libsimple:program,libtemplates:program)linkage
let libpasstypes=for acc=empty:set.passtypes,m=librarymods do 
 let types= for acc2=empty:set.mytype,t=types.m  do  acc2+ fixtype.t /for(acc2)
acc+passtypes(module.m,empty:set.mytype,types)
 /for(acc)
let compiled=for acc=empty:set.symbol,sd=toseq.data.libsimple do  acc+sym.sd /for(acc)
let lib ="?"_1
let modsx = resolvetypes(libpasstypes,allsrc1, lib)
let typedict=for typedict=empty:set.mytype, m=toseq.modsx do typedict /cup defines.m /for(typedict)
let allsrc=groupparagraphs("module Module", allsrc1)
let a = for acc = asset.librarymods, @e = allsrc do gathersymbols(acc,typedict,modsx, @e)/for(acc)
let d0 =resolveunresolvedexports.a
 let split = split(toseq.d0)
 let simple = simple.split 
 let abstract = abstract.split
  let prg1 = for acc = libsimple, @e = simple do bind3(acc,   d0, @e)/for(acc)
 let templates = for acc = libtemplates, @e = abstract do 
 prescan2.bind3(acc,  d0, @e)/for(acc)
 let roots = for acc = empty:seq.symbol, @e = simple do acc + roots(exports, @e)/for(acc)
  { let z=for  acc=empty:set.symdef ,  sd=  toseq.data.templates do
     acc+symdef(sym.sd,code.postbind (sd,dict2,  compiled))
  /for (program.acc) }
    let d1 = expanduse.d0
let allsymbols1 = for acc = empty:set.symbol, @e = toseq.d1 do acc ∪ defines.@e /for(acc)
let typeflds  = for typeflds = empty:seq.seq.mytype, @e = toseq.d1 do typeflds + types.@e /for( typeflds)
let dict2=buildtypedict(empty:set.symbol,typeflds)
   let prg2=postbind(dict2, allsymbols1, roots ,  prg1,  templates,compiled)
   let dict3=buildtypedict(data.prg2+symdef( (defines.split)_1,toseq.defines.split),typeflds  ) 
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
   
   
 function print(s:seq.mytype) seq.word  for txt="",t=s do txt+print.t /for(txt)
 
 use postbind
 
 use program
 



function resolveunresolvedexports(modset:set.passsymbols)set.passsymbols
  for modset1 = modset,count=0 , orgcount=0,f = toseq.modset do 
      if cardinality.unresolvedexports.f = 0 then next(modset1,count,orgcount)
 else
  let dict = builddict(modset1, f)
  let new = for exports=exports.f,unresolvedexports=empty:set.symbol, s = toseq.unresolvedexports.f do 
        let x = findelement2(dict, s)
        if cardinality.x = 1 then
          assert resulttype.x_1 = resulttype.s report"export return type missmatch" + print.s + print.x_1
          next( exports  ∪ x,   unresolvedexports)
        else
            next( exports,    unresolvedexports + s)
    /for(firstpass(module.f, uses.f, defines.f, exports, unresolvedexports,  types.f, prg.f,text.f))
  next(replace(modset1, new),count+cardinality.unresolvedexports.new,orgcount+cardinality.unresolvedexports.f)
  /for( if count=0 then modset1 
      else  assert count < orgcount /or  count = 0 report "unresolved exports"
    + for acc ="", x = for acc = empty:seq.symbol, @e = toseq.modset do 
      acc +toseq.unresolvedexports.@e /for(acc)do
     acc + print.x
    /for(acc)
     resolveunresolvedexports.modset1)

 
 Function ?(a:passsymbols, b:passsymbols)ordering toalphaseq.print.module.a ? toalphaseq.print.module.b

  

function formsymboldict(modset:set.passsymbols, f:passsymbols,mode:seq.word ) symboldict
 let dict=builddict(modset,f)
 let typedict= for typedict=empty:set.mytype, sym = toseq.dict do
  if istype.sym then  typedict+resulttype.sym else typedict
  /for(typedict)
symboldict(dict,[commoninfo("",module.f,"?"_1,typedict,mode_1)])

use seq.commoninfo

use symboldict


function builddict(modset:set.passsymbols, f:passsymbols)set.symbol
 for acc = defines.f , @e = toseq.uses.f do 
 if issimple.@e /or para.@e=typeT then 
    let e =  findelement(firstpass(@e), modset)
    if isempty.e then acc else acc ∪ exports.e_1 
 else 
   let template=findelement(firstpass( moduleref([name.@e], typeT)), modset)
   assert not.isempty.template report"Cannot find module" +  name.@e
   if isempty.template then acc else 
     for acc2 = acc, export = toseq.exports.template_1 do acc2 + replaceTsymbol(para.@e, export) /for(acc2)
/for(acc)

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
    , asset.for acc = empty:seq.symbol, @e = toseq.defines.f do 
      if isunbound.@e then acc else acc + replaceTsymbol(with, @e) /for(acc)
    ,  empty:set.symbol
    ,  empty:set.symbol
    , replaceTmyinternaltype(with, types.f), prg.f,text.f)
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
let dict= formsymboldict(modset,f,"body")
 for acc = p ∪ prg.f, text = text.f do 
  {if (text.text)_1 ∈ "Builtin builtin"then
    let sym=sym.text
    let code2 = 
     for acc2 = empty:seq.symbol, @e = arithseq(nopara.sym, 1, 1)do acc2 + Local.@e /for(acc2)
     + if issimple.module.sym then [ sym, Words."BUILTIN", Optionsym]
     else
      [ if issimplename.sym then symbol(moduleref("builtin", typeT), [ wordname.sym], paratypes.sym, resulttype.sym)
      else symbol4(moduleref("builtin", typeT), wordname.sym,(nametype.sym)_1, paratypes.sym, resulttype.sym)]
    map(p , sym, code2)
  else }
 let dict2= symboldict(asset.dict,[commoninfo(text.text,modname.common.dict,"?"_1,types
 .common.dict,mode.common.dict)])
 let code = parsedcode.parse.dict2
 map(acc, sym.text, if length.code = 1 ∧ isconst.code_1 then code + [ Words."VERYSIMPLE", Optionsym]else code)
 /for(acc)

Function bindinfoX(types:set.mytype, input:seq.word,mode:seq.word) symboldict
symboldict(empty:set.symbol,[commoninfo(input,moduleref."?","?"_1,types,mode_1)])

function fldcode(constructor:symbol, indexfunc:seq.symbol, syms:seq.symbol, i:int, inknownoffset:int, offsetx:seq.word, inprg:program
,isseq:boolean,b:bindinfo,modname:modref)program
 if length.syms = 1 ∧ not.isseq then
  map(map(inprg, first.syms, [ Local.1]), constructor, [ Local.1])
 else
  let recordtype=if issimple.modname then first.types.b else addabstract(first.types.b ,typeT)
  for       flds = empty:seq.symdef,
    idx = 1
    , knownsize = if isseq then {2} 1 else 0
    , unknownsize = empty:seq.symbol
    , constructflds = if isseq then [ PreFref, indexfunc_2 , Local.1 ] else  empty:seq.symbol
         , fldtype = if isseq then [ typeint] + types.b << 2 else types.b << 1 
     do
       let size = knownsize.fldtype
       let usize = if size = 1 then unknownsize else unknownsize + symbol(builtinmod.fldtype,"typesize", typeint) + PlusOp
            if(text.b)_idx ∈ ":"then 
            next(flds, idx + 1, knownsize + size, usize, constructflds)
       else  
       let code =  fldsym(modname
      ,(text.b)_ idx,recordtype,fldtype,knownsize,unknownsize)
     next(flds+code
      , idx + 1
      , knownsize + size
     ,usize
         , constructflds + 
         if  fldtype=typeint /or isseq.fldtype then [Local.idx] else
          [Local.idx ,symbol(builtinmod.fldtype,"pushflds",fldtype,fldtype)])
  /for(let constructor2 =symdef(constructor, 
      constructflds+ 
     symbol(builtinmod.resulttype.constructor,"buildrecord",resulttype.constructor,typeptr)) 
    for acc=inprg ,r=flds+constructor2 do map(acc,sym.r,code.r) /for(acc))

use seq.symdef

function fldsym(modname:modref, name:word, objecttype:mytype, fldtype:mytype, knownsize:int, unknownsize:seq.symbol)symdef
let fldsym = symbol(modname, [name],    objecttype, fldtype )
symdef(fldsym, [ Local.1, Lit.knownsize] + unknownsize + Getfld.if isseq.fldtype then typeptr else fldtype)

function knownsize(fldtype:mytype)int
 if fldtype ∈ [ typeint, typeword, typereal, typeboolean, typeseqdec] ∨ isseq.fldtype ∨ isencoding.fldtype then 1 else 0

function gathersymbols(mods:set.passsymbols,typedict:set.mytype, passtypes:set.passtypes, inputseq:seq.seq.word)set.passsymbols
for text = empty:seq.symtextpair,module=moduleref."?", uses=empty:set.modref, defines=empty:set.symbol, exports=empty:set.symbol
, unresolvedexports=empty:set.symbol, unbound=empty:set.symbol, types=empty:seq.seq.mytype, prg=emptyprogram
,input = inputseq do
 if length.input = 0 then
    next(text, module, uses , defines , exports , unresolvedexports , unbound , types , prg )
 else {if input_1 ∈ "use"then
 let t= (types.parse.bindinfoX(typedict,"type type is" + input << 1,"use"))_2
    next(text, module, uses+t , defines , exports , unresolvedexports , unbound , types , prg )
 else }if input_1 ∈ "type"then
 let bb=parse.bindinfoX(typedict, input,"use")
  let name = input_2
  let t = addabstract(typeref([ name] + "fldname."), para.module) 
 let thetype = addabstract(typeref3(module, name ), para.module)
 let typesym   =  symbol4(module,"type"_1 ,thetype   ,   [ thetype ], thetype )
if input_4 = "sequence"_1 then
  let constructor = symbol(module, [ name],  [ typeint] + types.bb << 2  , t)
  let fldsyms = for acc=empty:seq.symbol,idx=2,t2=types.bb << 2 do
                    next( acc+ symbol(module, [(text.bb)_idx],[t], t2),idx+1)
                /for(acc)
  let seqtype = seqof.para.module
  let symtoseq = symbol(module,"toseq",  t, seqtype)
  let symfromseq = symbol4(module,"to"_1, t, [ seqtype], t)
  let indexfunc =  symbol(module,"_", [ addabstract(typeref([ name] + "fldname."), typeT), typeint], typeT)
  let prg1 = fldcode(constructor, [PreFref, indexfunc], fldsyms, 1, 2,"", prg ,true,bb,module)
  let prg2 = map(prg1, symtoseq, [ Local.1])
  let prg3 = map(prg2, symfromseq, ifthenelse([ Local.1, GetSeqType, PreFref,indexfunc, EqOp], [ Local.1]
  , [Sequence(typeint,0)], typeptr) )
  let syms = fldsyms + [ constructor, typesym, symtoseq, symfromseq]
    let newtypes =  addtype(types,   name, module, [typeint,typeint ] + types.bb << 2 )
  if name ≠ "seq"_1 then
       next(text, module, uses  , defines ∪ asset.syms, exports , unresolvedexports , unbound , newtypes , prg3 )
   else
    let symlen = symbol(module,"length",  t, typeint)
    let symgettype = symbol(builtinmod.typeint,"getseqtype",  t, typeint)
    let prg4 = map(prg3, symlen, [ Local.1, GetSeqLength])
      next(text, module, uses  , defines ∪ asset(syms + symlen + symgettype), exports , unresolvedexports , unbound , newtypes , prg4 )
else
   let constructor = symbol(module, [ name],types.bb << 1  , t)
   let fldsyms = for acc=empty:seq.symbol,idx=1,t2=types.bb << 1 do
                    next( acc+ symbol(module, [(text.bb)_idx],[t], t2),idx+1)
                /for(acc)
   let prg2 = fldcode(constructor, empty:seq.symbol, fldsyms, 1, 0,"", prg,false,bb,module)
   let syms = fldsyms + [ constructor, typesym]
   let newtypes=addtype(types, name, module,  types.bb << 1)
         next(text, module, uses  , defines ∪ asset.syms, exports , unresolvedexports , unbound , newtypes , prg2 )
 else if input_1 ∈ "Function function Builtin builtin Export unbound"then
 let t = parse.bindinfoX(typedict, getheader.input,"gather")
 let sym = tosymfromparse(t, module)
 let paratypes = paratypes.sym
  assert checkwellformed.sym report"Must use type T in function name or parameters in parameterized module and T cannot be used in non-parameterized module" + getheader.input
   if input_1 = "Export"_1 then
       next(text, module, uses  , defines , exports , unresolvedexports+ sym , unbound , types , prg )
   else if input_1 = "unbound"_1 then
          next(text, module, uses  , defines + setunbound.sym, exports , unresolvedexports  , unbound  , types , prg )
    else
    assert sym ∉ defines  report"Function" + wordname.sym + "is defined twice in module" + print.module
    let prg1 = if input_1 ∈ "Builtin builtin"then
    let code2 = 
     for acc = empty:seq.symbol, @e = arithseq(length.paratypes, 1, 1)do acc + Local.@e /for(acc)
     + if issimple.module.sym then [ sym, Words."BUILTIN", Optionsym]
     else
      [ if issimplename.sym then symbol(moduleref("builtin", typeT), [ wordname.sym], paratypes, resulttype.sym)
      else symbol4(moduleref("builtin", typeT), wordname.sym,(nametype.sym)_1, paratypes, resulttype.sym)]
    map(prg , sym, code2)
    else 
    prg 
    let a = if input_1 ∈ "Function Builtin"then exports  + sym else exports 
    let newtext=if input_1 ∈ "Builtin builtin"then text else 
              text+symtextpair(sym,input,0)
             next(newtext, module, uses  , defines+ sym , a , unresolvedexports  , unbound  , types , prg1 )
 else if input_1 ∈ "module Module"then
  let lib="."_1
 let x = findpasstypes( passtypes, lib,  input )
    assert not.isempty.x report"did not find" +input
     {let tmp= for acc=empty:seq.mytype,   m=toseq.uses.x_1 do  acc+addabstract(typeref3(m, name.m ), para.m) /for(acc)
       }  next(text, if length.input > 2 then moduleref([ input_2], typeT)else moduleref.[ input_2]
         ,  uses.x_1   , defines , exports , unresolvedexports  , unbound  , types , prg )
 else         next(text, module, uses  , defines , exports , unresolvedexports    , unbound ,types , prg )
/for( 
let f=firstpass(module, uses  , defines , exports , unresolvedexports     , types , prg,text )
if name.module.f /in "?" then mods else
assert f ∉ mods report"duplicate module name:" + print.module.f
  mods + f)
  
  use set.modref
  
  use seq.symtextpair
  
function cvttomytypes(in:set.modref) seq.mytype
for acc=empty:seq.mytype,   m=toseq.in do  acc+addabstract(typeref3(m, name.m ), para.m) /for(acc)

Function  cvttomodrefs(in:seq.mytype)    set.modref
  for acc=empty:set.modref,   m=in do acc+moduleref([abstracttype.m],parameter.m) /for(acc)

function roots(exported:seq.word, f:passsymbols)seq.symbol
 if name.module.f ∉ exported ∨ not.issimple.module.f then empty:seq.symbol else toseq.exports.f

use mytype

function getmod(s:seq.word, i:int)seq.word
 if s_i ∈ "."then getmod(s, i + 2) + s_(i + 1)
 else empty:seq.word 