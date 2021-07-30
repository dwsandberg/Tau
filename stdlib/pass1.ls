Module pass1

use parse

use standard

use symbol

use program

use textio

use words

use otherseq.firstpass

use seq.firstpass

use set.firstpass

use seq.mapele

use seq.myinternaltype

use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use encoding.symboltext

use seq.symboltext

use seq.unboundexport

use set.word

use seq.seq.firstpass

use seq.seq.word

use seq.seq.seq.word

Export result(linkage)pro2gram

Export compiled(linkage)set.symbol

Export templates(linkage)pro2gram

Export cinfo(linkage)compileinfo

Export type:linkage

type linkage is result:pro2gram, compiled:set.symbol, templates:pro2gram,cinfo:compileinfo

function =(a:firstpass, b:firstpass)boolean module.a = module.b

type mapele is key:symbol, target:symbol

function replaceTsymbol2(with:mytype, s:symbol)mapele mapele(replaceTsymbol(with, s), s)

Function print(b:firstpass)seq.word
" /br  /br" + print.module.b + " /br defines" + printdict.defines.b
 + " /br unboundexports"
 + printdict.asset.unboundexports.b

Function find(modset:set.firstpass, name:mytype)set.firstpass
 findelement(firstpass(tomodref.name, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, empty:seq.myinternaltype, emptyprogram)
 , modset
 )

function issimple2(s:symbol)seq.symbol if isabstract.module.s then empty:seq.symbol else [ s]

use  groupparagraphs

/use pro2gram

use seq.program


use set.passtypes

Function pass1(allsrc1:seq.seq.word, exports:seq.word, librarymods:seq.firstpass
, libsimple:program,libtemplates:program)linkage
let libpasstypes=for acc=empty:set.passtypes,m=librarymods do 
 let types= for acc2=empty:set.mytype,t=types.m  do 
 acc2+ if isabstract.module.t then addabstract(typeref3(module.t, name.t),typeT)
 else typeref3(module.t, name.t) /for(acc2)
acc+passtypes(module.m,empty:set.mytype,types)
 /for(acc)
let lib ="?"_1
let modsx = resolvetypes(libpasstypes,allsrc1, lib)
let typedict=for typedict=empty:set.mytype, m=toseq.modsx do typedict /cup defines.m /for(typedict)
let allsrc=groupparagraphs("module Module", allsrc1)
let a = for acc = asset.librarymods, @e = allsrc do gathersymbols(acc,typedict, @e)/for(acc)
let expand1 = expanduse.expanduseresult(a, empty:seq.mapele)
let u0 = firstpasses.expand1
let d1 = resolveunboundexports.u0
let allsymbols1 = for acc = empty:set.symbol, @e = toseq.d1 do acc ∪ defines.@e /for(acc)
let alltypes0 = for acc = empty:seq.myinternaltype, @e = toseq.d1 do acc + types.@e /for(acc)
{ assert false report"XX"+ @(seperator."
/br", towords,"", alltypes0)}
 let alltypes = processtypedef(typedict.basetypes, alltypes0, 1, empty:seq.myinternaltype)
 let abstractsimple1 = split(toseq.d1, 1, empty:seq.firstpass, empty:seq.firstpass)
 let simple = abstractsimple1_2
 let abstract = abstractsimple1_1
 let prg1 = for acc = libsimple, @e = simple do bind3(acc, alltypes, d1, @e)/for(acc)
 let templates0 = for acc = libtemplates, @e = abstract do bind3(acc, alltypes, d1, @e)/for(acc)
 let templates = maptemp(map.expand1, templates0)
 let roots = for acc = empty:seq.symbol, @e = simple do acc + roots(exports, @e)/for(acc)
  let dict2=type2dict(alltypes)
  let compiled=asset.toseq.libsimple
let prg2=postbind(dict2, allsymbols1, roots , prg1, templates,compiled)
 let options=for acc = empty:seq.seq.word, @e = allsrc1 do acc + @e /for(acc)
 let mods=tolibraryModules(dict2,emptypro2gram,  simple + abstract,exports) 
{ assert false report  "X"+for acc="", m=mods do acc+name.modname.m /for (acc)
 }let cinfo=cvtL2( dict2 ,emptypro2gram,  mods)
 linkage(processOptions(prg2,simple,"COMPILETIME NOINLINE INLINE PROFILE STATE"), compiled,   prescan2.pro2gram.templates,cinfo)
 
 Function processOptions(prg:pro2gram,mods:seq.firstpass,option:seq.word) pro2gram
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
 
 
 Function tolibraryModules(alltypes: type2dict,prg:pro2gram,  t5:seq.firstpass,exports:seq.word) seq.libraryModule
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
 
 use pro2gram
 

function basetypes seq.myinternaltype [ myinternaltype("defined"_1,"int"_1, moduleref."standard", [ typeint]), myinternaltype("defined"_1,"boolean"_1, moduleref."standard", [ typeint])]

function maptemp(map:seq.mapele, templates:program)program
 for st = templates, e = map do
 let s2 = lookupcode(templates, target.e)
 if isdefined.s2 then map(st, key.e, target.e, code.s2)
  else map(st, key.e, target.e, empty:seq.symbol)
 /for(st)
 
 Function print3(it:myinternaltype)seq.word
 if not.isdefined.it then
  "module:" + print.module.it + "type" + name.it + "is"
  + typekind.it
  + for acc ="", e = subflds.it do list(acc,",", printfld.e)/for(acc)
 else
  [ typekind.it, name.it] + print.module.it
  + for acc ="", e = subflds.it do acc + print.e /for(acc)

function printfld(f:mytype)seq.word [ fldname.f,":"_1] + print.parameter.f

function processtypedef(defined:typedict, undefined:seq.myinternaltype, i:int, newundefined:seq.myinternaltype)typedict
 if i > length.undefined then
  if length.newundefined = 0 then defined
  else
   assert length.undefined > length.newundefined report"unresolved types:"
   + for acc ="", @e = newundefined do list(acc," /br", print3.@e)/for(acc)
   processtypedef(defined, newundefined, 1, empty:seq.myinternaltype)
 else
  let td = undefined_i
  let fldtypes = if typekind.td ∈ "record"then
   for acc = empty:seq.mytype, @e = subflds.td do acc + parameter.@e /for(acc)
  else if typekind.td ∈ "sequence"then
   for acc = [ typeint], @e = subflds.td do acc + parameter.@e /for(acc)
  else subflds.td
  let flds = for acc = empty:seq.mytype, idx = 1, fld = fldtypes do
   next(let tmp = subflddefined(defined, replaceT(modpara.td, fld))
   if idx = 1 ∨ isempty.tmp then tmp else if isempty.acc then acc else acc + tmp, idx + 1)
  /for(acc)
  if length.flds = 0 then
    { some fld is not defined }processtypedef(defined, undefined, i + 1, newundefined + undefined_i)
   else processtypedef(defined + [ changesubflds(td, flds)], undefined, i + 1, newundefined)

function subflddefined(defined:typedict, typ:mytype)seq.mytype
 if isseq.typ ∨ typ ∈ [ typeint, typereal, typeboolean, typeT]then [ typ]
 else if isencoding.typ then [ typeint]
 else
  let typdesc = findtype(defined, typ)
  if isempty.typdesc then { not defined }empty:seq.mytype else subflds.typdesc_1

type unboundexport is modname:mytype, unbound:symbol

/function getunboundexport(f:firstpass)seq.unboundexport @(+, unboundexport(modname.f), empty:seq.unboundexport, unboundexports.f)

/function resolveexport(modset:set.firstpass, lastdict:set.symbol, lastmodname:mytype, toprocess:seq.unboundexport, i:int, unresolved:seq.unboundexport)set.firstpass if i > length.toprocess then if length.unresolved = 0 then modset else assert length.toprocess ≠ length.unresolved report"unresolved exports"+ @(+, print,"", unresolved)resolveexport(modset, empty:set.symbol, typedef("internal","1"), unresolved, 1, empty:seq.unboundexport)else let u = toprocess_i let dict = if lastmodname = modname.u then lastdict else let e = find(modset, modname.u)@(∪, builddict.modset, defines.e_1 ∪ unbound.e_1, uses.e_1)let x = findelement2(dict, unbound.u)// assert not(mangledname.unbound.u ="typeQ3AwordZwords"_1)report print.u + toword.cardinality.x // if cardinality.x = 1 then assert resulttype.x_1 = resulttype.unbound.u report"export return type missmatch"+ print.unbound.u + print.x_1 let f = find(modset, modname.u)_1 let newf = firstpass(modname.f, uses.f, defines.f, replace(exports.f, x), unboundexports.f, unbound.f, types.f, prg.f)// let t = replace(modset, newf)let f2 = find(modset, modname.u)_1 // resolveexport(replace(modset, newf), dict, modname.u, toprocess, i + 1, unresolved)else resolveexport(modset, dict, modname.u, toprocess, i + 1, unresolved)

function print(x:unboundexport)seq.word" /br" + print.modname.x + print.unbound.x

function resolveunboundexports(modset:set.firstpass)set.firstpass
let u = for acc = empty:seq.firstpass, @e = toseq.modset do acc + hasunbound.@e /for(acc)
let orgcount = for acc = 0, @e = u do acc + totalunbound.@e /for(acc)
if orgcount = 0 then modset
 else
  let newset = for acc = modset, @e = u do bindunboundexports(acc, @e)/for(acc)
  let newcount = for acc = 0, @e = toseq.newset do acc + totalunbound.@e /for(acc)
  if newcount = orgcount then
    assert orgcount = 0 report"unresolved exports"
    + for acc ="", @e = for acc = empty:seq.symbol, @e = u do acc + unboundexports.@e /for(acc)do
     acc + print.@e
    /for(acc)
    modset
   else resolveunboundexports.newset
   

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

function bindunboundexports(modset:set.firstpass, f:firstpass)set.firstpass
 if length.unboundexports.f = 0 then modset
 else
  let dict = builddict(modset, f)
  let acc0 = firstpass(module.f, uses.f, defines.f, exports.f, empty:seq.symbol, unbound.f, types.f, prg.f)
  let new = for acc = acc0, @e = unboundexports.f do resolveexport(acc, dict, @e)/for(acc)
  replace(modset, new)

function resolveexport(f:firstpass, dict:set.symbol, s:symbol)firstpass
let x = findelement2(dict, s)
if cardinality.x = 1 then
  assert resulttype.x_1 = resulttype.s report"export return type missmatch" + print.s + print.x_1
   firstpass(module.f, uses.f, defines.f, exports.f ∪ x, unboundexports.f, unbound.f, types.f, prg.f)
 else
  firstpass(module.f, uses.f, defines.f, exports.f, unboundexports.f + s, unbound.f, types.f, prg.f)

function expanduse(acc3:expanduseresult)expanduseresult
let modset1 = firstpasses.acc3
let newset = for acc2 = acc3, use = toseq.asset.for acc = empty:seq.mytype, @e = toseq.modset1 do acc + uses.@e /for(acc)do
let modset = firstpasses.acc2
let x = find(modset, use)
if iscomplex.use ∧ parameter.use ≠ typeT then
  if isempty.x then
  let template = find(modset, addabstract(abstracttypeof.use, typeT))
  assert not.isempty.template report"Cannot find module" + print.use
   let f = template_1
   let with = parameter.use
   let defs = for acc = empty:seq.mapele, @e = toseq.defines.f do acc + replaceTsymbol2(with, @e)/for(acc)
   let exps = for acc = empty:seq.mapele, @e = toseq.exports.f do acc + replaceTsymbol2(with, @e)/for(acc)
   let unb = for acc = empty:seq.mapele, @e = unboundexports.f do acc + replaceTsymbol2(with, @e)/for(acc)
   expanduseresult(modset
    + firstpass(replaceT(with, module.f), for acc = empty:seq.mytype, @e = uses.f do acc + replaceT(with, @e)/for(acc), asset.for acc = empty:seq.symbol, @e = defs do acc + key.@e /for(acc), asset.for acc = empty:seq.symbol, @e = exps do acc + key.@e /for(acc), for acc = empty:seq.symbol, @e = unb do acc + key.@e /for(acc), empty:set.symbol, for acc = empty:seq.myinternaltype, @e = types.f do acc + replaceTmyinternaltype(with, @e)/for(acc), prg.f)
    , map.acc2 + defs + exps + unb
    )
  else acc2
 else assert not.isempty.x report"Cannot find module" + print.use
  acc2
/for(acc2)
if cardinality.firstpasses.newset > cardinality.modset1 then expanduse.newset else acc3

type expanduseresult is firstpasses:set.firstpass, map:seq.mapele

function hasunbound(f:firstpass)seq.firstpass if length.unboundexports.f = 0 then empty:seq.firstpass else [ f]

function totalunbound(f:firstpass)int length.unboundexports.f

function split(s:seq.firstpass, i:int, abstract:seq.firstpass, simple:seq.firstpass)seq.seq.firstpass
 if i > length.s then [ abstract, simple]
 else
  let f = s_i
   if issimple.module.f ∧ { this condition needs attention }length.uses.f > 0 then
    split(s, i + 1, abstract, simple + f)
   else if para.module.f = typeT then split(s, i + 1, abstract + f, simple)
   else split(s, i + 1, abstract, simple)

function print(p2:program)seq.word
 for acc ="", @e = toseq.p2 do list(acc," /br  /br", print(p2, @e))/for(acc)

function bind3(p:program, alltypes:typedict, modset:set.firstpass, f:firstpass)program
let dict= formsymboldict(modset,f,"body")
 for acc = p ∪ prg.f, @e = toseq.defines.f do bind2(acc, alltypes, dict, @e)/for(acc)

function bind2(p:program, alltypes:typedict, dict:symboldict, s:symbol)program
let txt = findencode.symboltext(s, moduleref."?","?")
if not.isempty.txt then
 let dict2= symboldict(asset.dict,[commoninfo(text.txt_1,modname.common.dict,"?"_1,types
 .common.dict,mode.common.dict)])
 let code = parsedcode.parse.dict2
 map(p, s, if length.code = 1 ∧ isconst.code_1 then code + [ Words."VERYSIMPLE", Optionsym]else code)
 else if para.module.s = typeT ∧ s ∉ p then map(p, s, empty:seq.symbol)else p


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

     for flds = empty:seq.symdef, idx = 1
     , knownsize = if isseq then 1 else 0
     , unknownsize = empty:seq.symbol
     , constructflds = if isseq then [ PreFref, indexfunc , Local.1 ] else  empty:seq.symbol
     , fldtype = if isseq then [ typeint] + types.b << 2 else types.b << 1 
     do
       let size = knownsize.fldtype
       let usize = if size = 1 then unknownsize else unknownsize + symbol(builtinmod.fldtype,"typesize", typeint) + PlusOp
       if(text.b)_idx ∈ ":"then next(flds, idx + 1, knownsize + size, usize, constructflds)
       else
         next(flds + fldsym(modname.common
         ,(text.b)_idx, first.types.b, fldtype, knownsize, unknownsize)
         , idx + 1
         , knownsize + size
         , usize
         , constructflds + 
         if  fldtype=typeint /or isseq.fldtype then [Local.idx] else
          [Local.idx ,symbol(builtinmod.fldtype,"pushflds",fldtype,fldtype)])
   /for(let constructor = symbol(modname.common, [name],   
   if isseq then [ typeint] + typs << 2 else typs << 1
   , first.typs)


function fldsym(modname:modref, name:word, objecttype:mytype, fldtype:mytype, knownsize:int, unknownsize:seq.symbol)symdef
let fldsym = symbol(modname, [name],    objecttype, fldtype )
symdef(fldsym, [ Local.1, Lit.knownsize] + unknownsize + Getfld.if isseq.fldtype then typeptr else fldtype)

function knownsize(fldtype:mytype)int
 if fldtype ∈ [ typeint, typeword, typereal, typeboolean, typeseqdec] ∨ isseq.fldtype ∨ isencoding.fldtype then 1 else 0



function gathersymbols(mods:set.firstpass,typedict:set.mytype, input:seq.seq.word)set.firstpass
let acc0 = firstpass(moduleref."?", empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, empty:seq.myinternaltype, emptyprogram)
let r = for acc = acc0, @e = input do gathersymbols(acc, typedict,  @e)/for(acc)
assert r ∉ mods report"duplicate module name:" + print.module.r
  mods + r

function gathersymbols(f:firstpass,typedict:set.mytype , input:seq.word)firstpass
 if length.input = 0 then
 let k = defines.f ∩ asset.unboundexports.f
  if isempty.k then f
  else
   firstpass(module.f, uses.f, defines.f, exports.f ∪ k, toseq(asset.unboundexports.f - k), unbound.f, types.f, prg.f)
 else if input_1 ∈ "use"then
 let t = typeflds.parse.bindinfoX(typedict,"type type is" + input << 1,"use")
 firstpass(module.f, uses.f + parameter.t_1, defines.f, exports.f, unboundexports.f, unbound.f, types.f, prg.f)
 else if input_1 ∈ "type"then
 let bb=parse.bindinfoX(typedict, input,"use")
 let b = typeflds.bb
 let name = input_2
 let t = addabstract(typeref([ name] + "fldname."), para.module.f)
 let it = if input_4 = "sequence"_1 ∨ fldname.(b)_1 = "sequence"_1 then
  myinternaltype("sequence"_1, name, module.f, [ addabstract(typeref.":fldname.", typeint)] + b << 1)
 else myinternaltype("record"_1, name, module.f, b)
 let typesym = typesym.it
  if typekind.it = "sequence"_1 then
  let constructor = symbol(module.f, [ name], for acc = [ typeint], @e = subflds.it << 1 do acc + parameter.@e /for(acc), t)
  let fldsyms = for acc = empty:seq.symbol, m = subflds.it << 1 do
   acc + symbol(module.f, [ fldname.m], [ t], parameter.m)
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
  if name ≠ "seq"_1 then
    firstpass(module.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, types.f + it, prg3)
   else
   { let symlen = symbol(builtinmod.typeint,"length" ,  t, typeint ) 
   } let symlen = symbol(module.f,"length",  t, typeint)
    let symgettype = symbol(builtinmod.typeint,"getseqtype",  t, typeint)
    let prg4 = map(prg3, symlen, [ Local.1, GetSeqLength])
     firstpass(module.f, uses.f, defines.f ∪ asset(syms + symlen + symgettype), exports.f, unboundexports.f, unbound.f, types.f + it, prg4) else
   let constructor = symbol(module.f, [ name], for acc = empty:seq.mytype, @e = subflds.it do acc + parameter.@e /for(acc), t)
   let fldsyms = for acc = empty:seq.symbol, m = b do
    acc + symbol(module.f, [ fldname.m], [ t], parameter.m)
   /for(acc)
   let prg2 = fldcode(constructor, empty:seq.symbol, fldsyms, 1, 0,"", prg.f,false,bb,module.f)
   let syms = fldsyms + [ constructor, typesym]
   firstpass(module.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, types.f + it, prg2)
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

function XX(f:firstpass, prg1:program, sym:symbol, input:seq.word)firstpass
let a = if input_1 ∈ "Function Builtin"then exports.f + sym else exports.f
 firstpass(module.f, uses.f, defines.f + sym, a, unboundexports.f, unbound.f, types.f, prg1)

function roots(exported:seq.word, f:firstpass)seq.symbol
 if name.module.f ∉ exported ∨ not.issimple.module.f then empty:seq.symbol else toseq.exports.f





use mytype

function getmod(s:seq.word, i:int)seq.word
 if s_i ∈ "."then getmod(s, i + 2) + s_(i + 1)
 else empty:seq.word 