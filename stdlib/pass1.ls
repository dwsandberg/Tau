Module pass1


use parse

use standard

use symbol

use firstpass

use textio

use words

use otherseq.firstpass

use seq.firstpass

use set.firstpass


use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use encoding.symboltext

use seq.symboltext



use set.word

use seq.seq.firstpass

use seq.seq.word

use seq.seq.seq.word

Export result(linkage)program

Export compiled(linkage)set.symbol

Export templates(linkage)program

Export cinfo(linkage)compileinfo

Export type:linkage

type linkage is result:program, compiled:set.symbol, templates:program,cinfo:compileinfo

function =(a:firstpass, b:firstpass)boolean module.a = module.b


Function print(b:firstpass)seq.word
" /br  /br" + print.module.b + " /br defines" + printdict.defines.b
 + " /br unboundexports"
 + printdict.asset.unboundexports.b

Function find(modset:set.firstpass, name:mytype)set.firstpass
 findelement(firstpass(tomodref.name), modset
 )

function issimple2(s:symbol)seq.symbol if isabstract.module.s then empty:seq.symbol else [ s]

use  groupparagraphs

/use program

use seq.program

use set.symdef


use set.passtypes

Function pass1(allsrc1:seq.seq.word, exports:seq.word, librarymods:seq.firstpass
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
let a = for acc = asset.librarymods, @e = allsrc do gathersymbols(acc,typedict, @e)/for(acc)
let d1 = resolveunboundexports.expanduse.a
 let split = split(toseq.d1)
 let simple = simple.split 
 let abstract = abstract.split
 let allsymbols1=defines.split
  let prg1 = for acc = libsimple, @e = simple do bind3(acc,   d1, @e)/for(acc)
 let templates = for acc = libtemplates, @e = abstract do 
 prescan2.bind3(acc,  d1, @e)/for(acc)
 let roots = for acc = empty:seq.symbol, @e = simple do acc + roots(exports, @e)/for(acc)
  { let z=for  acc=empty:set.symdef ,  sd=  toseq.data.templates do
     acc+symdef(sym.sd,code.postbind (sd,dict2,  compiled))
  /for (program.acc) }
     let dict2=if newdict then buildtypedict(allsymbols1,typeflds.split)
          else processtypedef.typeflds.split  
  {let dict4= buildtypedict(data.prg1, typeflds.split)  }   
  let prg2=postbind(dict2, allsymbols1, roots ,  prg1,  templates,compiled)
 let mods=tolibraryModules(dict2,emptyprogram,  simple + abstract,exports) 
{ assert false report  "X"+for acc="", m=mods do acc+name.modname.m /for (acc)
 }let cinfo=cvtL2( dict2 ,emptyprogram,  mods)
 linkage(processOptions(prg2,simple,"COMPILETIME NOINLINE INLINE PROFILE STATE"), compiled,   
 templates,cinfo)
  
 use typerep
 
 Function processOptions(prg:program,mods:seq.firstpass,option:seq.word) program
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
 
 
 Function tolibraryModules(alltypes: type2dict,prg:program,  t5:seq.firstpass,exports:seq.word) seq.libraryModule
 for acc = empty:seq.libraryModule, m2 =  t5 do
    if name.module.m2 /nin exports then acc else
     let exps=  for acc3 = empty:seq.symbolref, e = toseq.exports.m2 do acc3 + symbolref.e /for(acc3)
    let defines=if isabstract.module.m2 then
      for acc3 = empty:seq.symbolref, e = toseq(defines.m2 /cup unbound.m2) do acc3 + symbolref.e /for(acc3)
     else exps
      let d2=if isabstract.module.m2 then defines.m2 else exports.m2
     let types = for acc5 = empty:seq.seq.mytype, s =  toseq.d2 do 
        if istype.s then
         acc5+ ([ resulttype.s]+flatflds(alltypes, resulttype.s))
   else   acc5
  /for(acc5)
    acc
    + libraryModule(module.m2, 
 exps    ,if isabstract.module.m2 then uses.m2 else empty:seq.mytype
    ,defines,types)
   /for(acc)
   
 use postbind
 
 use program
 



function resolveunboundexports(modset:set.firstpass)set.firstpass
  for modset1 = modset,count=0 , orgcount=0,f = toseq.modset do 
      if length.unboundexports.f = 0 then next(modset1,count,orgcount)
 else
  let dict = builddict(modset1, f)
  let new = for exports=exports.f,unboundexports=empty:seq.symbol, s = unboundexports.f do 
        let x = findelement2(dict, s)
        if cardinality.x = 1 then
          assert resulttype.x_1 = resulttype.s report"export return type missmatch" + print.s + print.x_1
          next( exports  ∪ x,   unboundexports)
        else
            next( exports,    unboundexports + s)
    /for(firstpass(module.f, uses.f, defines.f, exports, unboundexports, unbound.f, types.f, prg.f))
  next(replace(modset1, new),count+length.unboundexports.new,orgcount+length.unboundexports.f)
  /for( if count=0 then modset1 
      else  assert count < orgcount /or  count = 0 report "unresolved exports"
    + for acc ="", x = for acc = empty:seq.symbol, @e = toseq.modset do 
      acc + unboundexports.@e /for(acc)do
     acc + print.x
    /for(acc)
     resolveunboundexports.modset1)

 
 
  

function formsymboldict(modset:set.firstpass, f:firstpass,mode:seq.word ) symboldict
 let dict=builddict(modset,f)
 let typedict= for typedict=empty:set.mytype, sym = toseq.dict do
  if istype.sym then  typedict+resulttype.sym else typedict
  /for(typedict)
symboldict(dict,[commoninfo("",module.f,"?"_1,typedict,mode_1)])

use seq.commoninfo

use symboldict

commoninfo("",moduleref."?","?"_1,typedict,mode_1)


function builddict(modset:set.firstpass, f:firstpass)set.symbol
 for acc = defines.f ∪ unbound.f, @e = uses.f do 
 let e = find(modset, @e)
 if isempty.e then acc else acc ∪ exports.e_1 /for(acc)


function expanduse(acc3:set.firstpass)set.firstpass
let modset1 = acc3
let newset = for acc2 = acc3, use = toseq.asset.for acc = empty:seq.mytype, @e = toseq.modset1 do acc + uses.@e /for(acc)do
let modset = acc2
let x = find(modset, use)
if iscomplex.use ∧ parameter.use ≠ typeT then
  if isempty.x then
  let template = find(modset, addabstract(abstracttypeof.use, typeT))
  assert not.isempty.template report"Cannot find module" + print.use
   let f = template_1
   let with = parameter.use
     modset
    + firstpass(replaceT(with, module.f)
    , for acc = empty:seq.mytype
    , @e = uses.f do acc + replaceT(with, @e)/for(acc)
    , asset.for acc = empty:seq.symbol, @e = toseq.defines.f do acc + replaceTsymbol(with, @e) /for(acc)
    , asset.for acc = empty:seq.symbol, @e = toseq.exports.f do acc + replaceTsymbol(with, @e) /for(acc)
    , for acc = empty:seq.symbol, @e = unboundexports.f do acc + replaceTsymbol(with, @e) /for(acc)
    , empty:set.symbol, replaceTmyinternaltype(with, types.f), prg.f)
  else acc2
 else assert not.isempty.x report"Cannot find module" + print.use
  acc2
/for(acc2)
if cardinality.newset > cardinality.modset1 then expanduse.newset else acc3



 type typesplit is abstract :seq.firstpass,simple :seq.firstpass,defines:set.symbol
 ,typeflds : seq.seq.mytype
   
function  newdict boolean false

function split(s:seq.firstpass) typesplit
  for  abstract=empty:seq.firstpass,simple=empty:seq.firstpass,defines=empty:set.symbol 
   ,fldtypes=empty:seq.seq.mytype
  ,f=s do
     if issimple.module.f  then
       next( abstract, simple + f,defines /cup defines.f,fldtypes+types.f)
    else if para.module.f = typeT then 
       next(abstract+f,simple,defines /cup defines.f,fldtypes+types.f)
    else next(abstract ,simple,defines /cup defines.f,if newdict then fldtypes else fldtypes+types.f )
  /for(typesplit( abstract, simple,defines,fldtypes))
 
 
function bind3(p:program,  modset:set.firstpass, f:firstpass)program
let dict= formsymboldict(modset,f,"body")
 for acc = p ∪ prg.f, s = toseq.defines.f do bind2(acc,  dict, s)/for(acc)

function bind2(p:program,   dict:symboldict, s:symbol)program
let txt = findencode.symboltext(s, moduleref."?","?")
if not.isempty.txt then
 let dict2= symboldict(asset.dict,[commoninfo(text.txt_1,modname.common.dict,"?"_1,types
 .common.dict,mode.common.dict)])
 let code = parsedcode.parse.dict2
 map(p, s, if length.code = 1 ∧ isconst.code_1 then code + [ Words."VERYSIMPLE", Optionsym]else code)
 else if para.module.s = typeT ∧ symdef(s,empty:seq.symbol) ∉ data.p then map(p, s, empty:seq.symbol)else p
 
 

type symboltext is ph:symbol, module:modref, text:seq.word

function hash(s:symboltext)int { should include module in hash }fsighash.ph.s

function =(a:symboltext, b:symboltext)boolean ph.a = ph.b

function assignencoding(p:seq.encodingpair.symboltext, a:symboltext)int assignrandom(p, a)

function fldname(a:mytype) word   abstracttype.a

function fldtype(a:mytype) mytype parameter.a 

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

function gathersymbols(mods:set.firstpass,typedict:set.mytype, inputseq:seq.seq.word)set.firstpass
for f = firstpass(moduleref."?"), input = inputseq do 
 if length.input = 0 then
 let k = defines.f ∩ asset.unboundexports.f
  if isempty.k then f
  else
   firstpass(module.f, uses.f, defines.f, exports.f ∪ k, toseq(asset.unboundexports.f - k), unbound.f, types.f, prg.f)
 else if input_1 ∈ "use"then
 let t= (types.parse.bindinfoX(typedict,"type type is" + input << 1,"use"))_2
  firstpass(module.f, uses.f + t, defines.f, exports.f, unboundexports.f, unbound.f, types.f, prg.f)
 else if input_1 ∈ "type"then
 let bb=parse.bindinfoX(typedict, input,"use")
  let name = input_2
 let t = addabstract(typeref([ name] + "fldname."), para.module.f)
 let thetype = addabstract(typeref3(module.f, name ), para.module.f)
 let typesym   =  symbol4(module.f,"type"_1 ,thetype   ,   [ thetype ], thetype )
if input_4 = "sequence"_1 then
  let constructor = symbol(module.f, [ name],  [ typeint] + types.bb << 2  , t)
  let fldsyms = for acc=empty:seq.symbol,idx=2,t2=types.bb << 2 do
                    next(acc+ symbol(module.f, [(text.bb)_idx],[t], t2),idx+1)
                /for(acc)
  let seqtype = seqof.para.module.f
  let symtoseq = symbol(module.f,"toseq",  t, seqtype)
  let symfromseq = symbol4(module.f,"to"_1, t, [ seqtype], t)
  let indexfunc =  symbol(module.f,"_", [ addabstract(typeref([ name] + "fldname."), typeT), typeint], typeT)
  let prg1 = fldcode(constructor, [PreFref, indexfunc], fldsyms, 1, 2,"", prg.f,true,bb,module.f)
  let prg2 = map(prg1, symtoseq, [ Local.1])
  let prg3 = map(prg2, symfromseq, ifthenelse([ Local.1, GetSeqType, PreFref,indexfunc, EqOp], [ Local.1]
  , [Sequence(typeint,0)], typeptr) )
  let syms = fldsyms + [ constructor, typesym, symtoseq, symfromseq]
    let newtypes =  addtype(types.f,   name, module.f, [typeint,typeint ] + types.bb << 2 )
  if name ≠ "seq"_1 then
    firstpass(module.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, newtypes, prg3)
   else
    let symlen = symbol(module.f,"length",  t, typeint)
    let symgettype = symbol(builtinmod.typeint,"getseqtype",  t, typeint)
    let prg4 = map(prg3, symlen, [ Local.1, GetSeqLength])
     firstpass(module.f, uses.f, defines.f ∪ asset(syms + symlen + symgettype), exports.f, unboundexports.f, unbound.f, newtypes, prg4) 
else
   let constructor = symbol(module.f, [ name],types.bb << 1  , t)
   let fldsyms = for acc=empty:seq.symbol,idx=1,t2=types.bb << 1 do
                    next(acc+ symbol(module.f, [(text.bb)_idx],[t], t2),idx+1)
                /for(acc)
   let prg2 = fldcode(constructor, empty:seq.symbol, fldsyms, 1, 0,"", prg.f,false,bb,module.f)
   let syms = fldsyms + [ constructor, typesym]
   let newtypes=addtype(types.f, name, module.f,  types.bb << 1)
   firstpass(module.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, newtypes, prg2)
 else if input_1 ∈ "Function function Builtin builtin Export unbound"then
 let t = parse.bindinfoX(typedict, getheader.input,"gather")
 let sym = tosymfromparse(t, module.f)
 let paratypes = paratypes.sym
  assert checkwellformed.sym report"Must use type T in function name or parameters in parameterized module and T cannot be used in non-parameterized module" + getheader.input
   if input_1 = "Export"_1 then
    firstpass(module.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f, types.f, prg.f)
   else if input_1 = "unbound"_1 then
    firstpass(module.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + setunbound.sym, types.f, prg.f)
   else
    assert sym ∉ defines.f report"Function" + wordname.sym + "is defined twice in module" + print.module.f
    let prg1 = if input_1 ∈ "Builtin builtin"then
    let code2 = 
     for acc = empty:seq.symbol, @e = arithseq(length.paratypes, 1, 1)do acc + Local.@e /for(acc)
     + if issimple.module.sym then [ sym, Words."BUILTIN", Optionsym]
     else
      [ if issimplename.sym then symbol(moduleref("builtin", typeT), [ wordname.sym], paratypes, resulttype.sym)
      else symbol4(moduleref("builtin", typeT), wordname.sym,(nametype.sym)_1, paratypes, resulttype.sym)]
    map(prg.f, sym, code2)
    else let discard = encode.symboltext(sym, module.f, input)
    prg.f
    let a = if input_1 ∈ "Function Builtin"then exports.f + sym else exports.f
     firstpass(module.f, uses.f, defines.f + sym, a, unboundexports.f, unbound.f, types.f, prg1)
 else if input_1 ∈ "module Module"then
  firstpass(if length.input > 2 then moduleref([ input_2], typeT)else moduleref.[ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f, types.f, prg.f)
 else f
/for( 
assert f ∉ mods report"duplicate module name:" + print.module.f
  mods + f)


function roots(exported:seq.word, f:firstpass)seq.symbol
 if name.module.f ∉ exported ∨ not.issimple.module.f then empty:seq.symbol else toseq.exports.f

use mytype

function getmod(s:seq.word, i:int)seq.word
 if s_i ∈ "."then getmod(s, i + 2) + s_(i + 1)
 else empty:seq.word 