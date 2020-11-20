
Module pass1

use otherseq.firstpass


use seq.seq.firstpass

use seq.firstpass

use set.firstpass

use seq.mapele

use seq.myinternaltype

use seq.mytype

use set.mytype

use parse

use stacktrace

use stdlib

use seq.symbol

use set.symbol

use symbol

use encoding.symboltext

use seq.symboltext

use textio

use seq.unboundexport

use seq.seq.seq.word

use seq.seq.word

use set.word

use words

Export result(linkage)program

Export dict(linkage) set.symbol

Export compiled(linkage)set.symbol

Export roots(linkage)seq.symbol

Export mods(linkage)seq.firstpass

Export templates(linkage)program

Export alltypes(linkage)typedict

Export type:linkage internaltype

type linkage is record result:program, compiled:set.symbol, 
roots:seq.symbol, mods:seq.firstpass, templates:program, alltypes:typedict,dict:set.symbol

function =(a:firstpass, b:firstpass)boolean modname.a = modname.b

Function ?(a:firstpass, b:firstpass)ordering toalphaseq.typerep.modname.a ? toalphaseq.typerep.modname.b

Function print(b:firstpass)seq.word
 " &br  &br" + print.modname.b + " &br defines" + printdict.defines.b
 + " &br unboundexports"
 + printdict.asset.unboundexports.b

Function find(modset:set.firstpass, name:mytype)set.firstpass
 findelement(firstpass(name, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, empty:seq.myinternaltype, emptyprogram)
 , modset)

function  issimple2(s:symbol) seq.symbol if isabstract.modname.s then empty:seq.symbol else [s]

Function pass1(allsrc:seq.seq.seq.word, exports:seq.word, librarymods:seq.firstpass)linkage
  let alllibsym = 
  @(∪, defines, empty:set.symbol, librarymods)
  &cup  @(∪, exports, empty:set.symbol, librarymods)
  let simplesym=asset.@(+,issimple2,empty:seq.symbol,toseq.alllibsym)
 let libprg= program.simplesym
 let libtemplates=program(alllibsym-simplesym) 
  // let discard = getinstance:encodingstate.symboltext //
  let a = @(gathersymbols, identity, asset.librarymods, allsrc)
  let expand1 = expanduse.expanduseresult(a, empty:seq.mapele)
  let u0 = firstpasses.expand1
   // let u1 = @(+, getunboundexport, empty:seq.unboundexport, toseq.u0)let d1 = resolveexport(u0, empty:set.symbol, mytype."1", u1, 1, empty:seq.unboundexport)//
   let d1 = resolveunboundexports.u0
   let allsymbols1 = @(∪, defines, empty:set.symbol, toseq.d1)
   let alltypes0 = @(+, types, empty:seq.myinternaltype, toseq.d1)
    // assert false report"XX"+ @(seperator."&br", towords,"", alltypes0)//
     let alltypes = processtypedef(typedict.basetypes, alltypes0, 1, empty:seq.myinternaltype)
    let abstractsimple1 = split(toseq.d1, 1, empty:seq.firstpass, empty:seq.firstpass)
    let simple = abstractsimple1_2
    let abstract = abstractsimple1_1
    let prg1 = @(bind3(alltypes, d1), identity, libprg, simple)
     let templates0 = @(bind3(alltypes, d1), identity, libtemplates , abstract)
    let templates = @(maptemp.templates0 , identity, templates0,   map.expand1)
     // assert false report @(seperator." &br", print,"", roots)//
    let roots = @(+, roots.exports, empty:seq.symbol, simple)
     linkage(prg1, toset.libprg , roots, simple + abstract, templates, alltypes,allsymbols1)

  function   basetypes seq.myinternaltype 
  [myinternaltype("defined"_1,"int"_1, mytype("stdlib"), [typeint]) ]


function maptemp(templates:program, st:program, s:mapele)program
 let s2 = lookupcode(templates, target.s)
  if isdefined.s2 then map(st, key.s, target.s, code.s2)
  else map(st, key.s, target.s, empty:seq.symbol)

function processtypedef(defined:typedict, undefined:seq.myinternaltype, i:int, newundefined:seq.myinternaltype)typedict
 if i > length.undefined then
 if length.newundefined = 0 then defined
  else
   assert length.undefined > length.newundefined report"unresolved types:" + @(seperator." &br", print3,"", newundefined)
    processtypedef(defined, newundefined, 1, empty:seq.myinternaltype)
 else
  let td = undefined_i
   let fldtypes= if kind.td in  "record " then @(+,parameter,empty:seq.mytype,subflds.td) 
    else if kind.td in  "sequence" then @(+,parameter,[typeint],subflds.td) 
   else subflds.td
  let flds = subflddefined( fldtypes , modpara.td, 1, defined, empty:seq.mytype)
   if length.flds = 0 then 
    // some fld is not defined //
    processtypedef(defined, undefined, i + 1, newundefined + undefined_i)
   else 
    processtypedef(defined + [changesubflds(td,  flds)], undefined, i + 1, newundefined)

function subflddefined(subflds:seq.mytype,modpara:mytype, i:int, defined:typedict, flatflds:seq.mytype)seq.mytype
 // check to see all flds of type are defined. //
 if i > length.subflds then  flatflds 
 else
  let typ = replaceT(modpara, subflds_i)
    if abstracttype.typ in "int seq real T"then subflddefined(subflds,modpara, i + 1, defined, flatflds + typ)
   else if abstracttype.typ in "encoding"then subflddefined(subflds,modpara, i + 1, defined, flatflds + typeint)
   else
    let typdesc = findelement(defined, typ)
    if isempty.typdesc then // not defined // empty:seq.mytype else subflddefined(subflds,modpara, i + 1, defined, flatflds + subflds.typdesc_1)


type unboundexport is record modname:mytype, unbound:symbol

/function getunboundexport(f:firstpass)seq.unboundexport @(+, unboundexport(modname.f), empty:seq.unboundexport, unboundexports.f)

/function resolveexport(modset:set.firstpass, lastdict:set.symbol, lastmodname:mytype, toprocess:seq.unboundexport, i:int, unresolved:seq.unboundexport)set.firstpass if i > length.toprocess then if length.unresolved = 0 then modset else assert length.toprocess &ne length.unresolved report"unresolved exports"+ @(+, print,"", unresolved)resolveexport(modset, empty:set.symbol, mytype."1", unresolved, 1, empty:seq.unboundexport)else let u = toprocess_i let dict = if lastmodname = modname.u then lastdict else let e = find(modset, modname.u)@(∪, builddict.modset, defines.e_1 ∪ unbound.e_1, uses.e_1)let x = findelement2(dict, unbound.u)// assert not(mangledname.unbound.u ="typeQ3AwordZwords"_1)report print.u + toword.cardinality.x // if cardinality.x = 1 then assert resulttype.x_1 = resulttype.unbound.u report"export return type missmatch"+ print.unbound.u + print.x_1 let f = find(modset, modname.u)_1 let newf = firstpass(modname.f, uses.f, defines.f, replace(exports.f, x), unboundexports.f, unbound.f, types.f, prg.f)// let t = replace(modset, newf)let f2 = find(modset, modname.u)_1 // resolveexport(replace(modset, newf), dict, modname.u, toprocess, i + 1, unresolved)else resolveexport(modset, dict, modname.u, toprocess, i + 1, unresolved)

function print(x:unboundexport)seq.word" &br" + print.modname.x + print.unbound.x

function resolveunboundexports(modset:set.firstpass)set.firstpass
 let u = @(+, hasunbound, empty:seq.firstpass, toseq.modset)
 let orgcount = @(+, totalunbound, 0, u)
  if orgcount = 0 then modset
  else
   let newset = @(bindunboundexports, identity, modset, u)
   let newcount = @(+, totalunbound, 0, toseq.newset)
    if newcount = orgcount then
    assert orgcount = 0 report"unresolved exports" + @(+, print,"", @(+, unboundexports, empty:seq.symbol, u))
      modset
    else resolveunboundexports.newset

function builddict(modset:set.firstpass, use:mytype)set.symbol
 let e = find(modset, use)
  if isempty.e then empty:set.symbol else exports.e_1

function builddict(modset:set.firstpass, f:firstpass)set.symbol @(∪, builddict.modset, defines.f ∪ unbound.f, uses.f)

function bindunboundexports(modset:set.firstpass, f:firstpass)set.firstpass
 if length.unboundexports.f = 0 then modset
 else
  let dict = builddict(modset, f)
  let new = @(resolveexport.dict, identity, firstpass(modname.f, uses.f, defines.f, exports.f, empty:seq.symbol, unbound.f, types.f, prg.f), unboundexports.f)
   replace(modset, new)

function resolveexport(dict:set.symbol, f:firstpass, s:symbol)firstpass
 let x = findelement2(dict, s)
  if cardinality.x = 1 then
  assert resulttype.x_1 = resulttype.s report"export return type missmatch" + print.s + print.x_1
    firstpass(modname.f, uses.f, defines.f, exports.f ∪ x, unboundexports.f, unbound.f, types.f, prg.f)
  else
   firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + s, unbound.f, types.f, prg.f)

function expanduse(acc:expanduseresult)expanduseresult
 let modset = firstpasses.acc
 let newset = @(expanduse2, identity, acc, toseq.asset.@(+, uses, empty:seq.mytype, toseq.modset))
  if cardinality.firstpasses.newset > cardinality.modset then expanduse.newset else acc

type expanduseresult is record firstpasses:set.firstpass, map:seq.mapele

function expanduse2(acc:expanduseresult, use:mytype)expanduseresult
 let modset = firstpasses.acc
 let x = find(modset, use)
 if iscomplex.use ∧ not(parameter.use = mytype."T")then
  if isempty.x then
   let template = find(modset, mytype("T" + abstracttype.use))
     assert not.isempty.template report"Cannot find module" + print.use
    //  + @(+, print,"", @(+, modname, empty:seq.mytype, toseq.modset))//
     let f = template_1
     let with = parameter.use
     let defs = @(+, replaceTsymbol2.with, empty:seq.mapele, toseq.defines.f)
     let exps = @(+, replaceTsymbol2.with, empty:seq.mapele, toseq.exports.f)
     let unb = @(+, replaceTsymbol2.with, empty:seq.mapele, unboundexports.f)
      expanduseresult(modset
      + firstpass(replaceT(with, modname.f), @(+, replaceT.with, empty:seq.mytype, uses.f), asset.@(+, s, empty:seq.symbol, defs), asset.@(+, s, empty:seq.symbol, exps), @(+, s, empty:seq.symbol, unb), empty:set.symbol, @(+, replaceTmyinternaltype.with, empty:seq.myinternaltype, types.f), prg.f)
      , map.acc + defs + exps + unb)
   else acc
  else
   assert not.isempty.x report"Cannot find module" + print.use
 //  + @(+, print,"", @(+, modname, empty:seq.mytype, toseq.modset)) //
    acc

function hasunbound(f:firstpass)seq.firstpass if length.unboundexports.f = 0 then empty:seq.firstpass else [ f]

function totalunbound(f:firstpass)int length.unboundexports.f

function split(s:seq.firstpass, i:int, abstract:seq.firstpass, simple:seq.firstpass)seq.seq.firstpass
 if i > length.s then [ abstract, simple]
 else
  let f = s_i
   if  not.iscomplex.modname.f  ∧ length.uses.f > 0 then
   split(s, i + 1, abstract, simple + f)
   else if parameter.modname.f = mytype."T"then split(s, i + 1, abstract + f, simple)
   else split(s, i + 1, abstract, simple)

function print(p2:program)seq.word @(seperator." &br  &br", print.p2,"", toseq.toset.p2)

function bind3(alltypes:typedict, modset:set.firstpass, p:program, f:firstpass)program
 let dict = builddict(modset, f) ∪ headdict
  @(bind2(alltypes, dict), identity, p ∪ prg.f, toseq.defines.f)

function bind2(alltypes:typedict, dict:set.symbol, p:program, s:symbol)program
 let txt = findencode.symboltext(s, mytype."?","?")
  if not.isempty.txt then map(p, s, parsedcode.parse(dict, text.txt_1))
  else
    if parameter.modname.s = mytype."T" ∧ not(s in toset.p)then
   map(p, s, empty:seq.symbol)
   else p

Function headdict set.symbol asset.[ symbol("export","headdict","internal1"), symbol("stub","headdict","internal1")]

function gathersymbols(mods:set.firstpass, input:seq.seq.word)set.firstpass
 let r = @(gathersymbols(headdict)
 , identity
 , firstpass(mytype."?", empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, empty:seq.myinternaltype, emptyprogram)
 , input)
  assert not(r in mods)report"duplicate module name:" + print.modname.r
   mods + r

function definefld(modname:mytype, t:seq.mytype, m:mytype)symbol newsymbol([ abstracttype.m], modname, t, parameter.m)

type symboltext is record ph:symbol, modname:mytype, text:seq.word

function hash(s:symboltext)int hash(fsig.ph.s + module.ph.s)

function =(a:symboltext, b:symboltext)boolean ph.a = ph.b

function assignencoding(l:int, s:symboltext)int assignrandom(l, s)

function tokind(type:mytype)word
 if type = mytype."real"then"real"_1
 else if abstracttype.type in "seq"then"ptr"_1
 else assert type=typeint &or type=mytype."word" report "tokind" + print.type
    "int"_1 

function fldcode(constructor: symbol,indexfunc:seq.symbol, syms:seq.symbol, i:int, knownoffset:int, offset:seq.word, prg:program)program
 if i > length.syms then
 if offset = ""then
  let args = @(+, Local, indexfunc, arithseq(length.syms, 1, 1))
   let x = Record.@(+, tokind, if not.isempty.indexfunc then "int" else "", paratypes.constructor)
    map(prg, constructor , args + x)
  else
   map(prg, constructor, indexfunc + symbol("build." + fsig.constructor,"x builtin","ptr"))
 else
  let this = syms_i
   if i = 1 ∧ length.syms = 1 then
   map(map(prg, this, [ Local.1]), constructor, [ Local.1])
   else
    let fldtype = resulttype.this
    let offsetinc = if abstracttype.fldtype in "real int seq word encoding boolean"then 1 else 0
     if offset = "" ∧ offsetinc = 1 then
     fldcode(constructor,indexfunc
      , syms
      , i + 1
      , knownoffset + 1
      , offset
      , map(prg
      , this
      , [ Local.1, Lit.knownoffset, Idx
      .if fldtype = mytype."real"then"real"_1
      else if abstracttype.fldtype in "seq"then"ptr"_1 else"int"_1]))
     else
      let newoffset = if offsetinc = 0 then
      if offset = ""then typerep.fldtype else offset + "," + typerep.fldtype
      else offset
       fldcode(constructor,indexfunc
       , syms
       , i + 1
       , knownoffset + offsetinc
       , newoffset
       , map(prg, this, [ Local.1, symbol("offsets("+typerep.fldtype+","+offset+")", [ toword.knownoffset]  + "builtin", typerep.fldtype)]))


function gathersymbols(stubdict:set.symbol, f:firstpass, input:seq.word)firstpass
 if length.input = 0 then
 let k = defines.f ∩ asset.unboundexports.f
   if isempty.k then f
   else
    firstpass(modname.f, uses.f, defines.f, exports.f ∪ k, toseq(asset.unboundexports.f - k), unbound.f, types.f, prg.f)
 else if input_1 in "use"then
 let t = parse(empty:set.symbol, subseq(input, 2, length.input))
   firstpass(modname.f, uses.f + (types.t)_1, defines.f, exports.f, unboundexports.f, unbound.f, types.f, prg.f)
 else if input_1 in "type"then
 let b = parse(empty:set.symbol, input)
  let kind = input_4
  let name = input_2
  let t = abstracttype(name, parameter.modname.f)
   assert parameter.modname.f in [ mytype."", mytype."T"]report"KLJKL"
   let it = myinternaltype(kind, name, modname.f, types.b)
   let typesym =  // newsymbol("type:" + print.t, modname.f,[t], t) // typesym.it
    let constructor = newsymbol([ name], modname.f, @(+, parameter, empty:seq.mytype, types.b), t)
   let fldsyms = @(+, definefld(modname.f, [ t]), empty:seq.symbol, types.b)
     let prg1 =prg.f  
    if kind = "sequence"_1 then
    let seqtype = typeseq+parameter.modname.f 
     let symtoseq = newsymbol("toseq", modname.f, [ t], seqtype)
     let symfromseq = newsymbol("to:" + print.t, modname.f, [ seqtype], t)
     let indexfunc = Fref
     .newsymbol("_", modname.f, [ mytype("T" + name), typeint], mytype."T")
     let prg0 = fldcode(  constructor ,[indexfunc], fldsyms, 1, 1,"", prg1)
     let syms = fldsyms + [ constructor, typesym, symtoseq, symfromseq]
     let prg = map(prg0, symtoseq, [ Local.1])
     let prg2 = map(prg, symfromseq, [ Local.1, Lit.0, Idx."int"_1, indexfunc, EqOp, Lit.2, Lit.3, Br, Local.1, Exit] + Emptyseq
     + [ Exit, Block(typeptr, 3)])
      firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, types.f + it, prg2)
    else
     let prg2 = fldcode( constructor,empty:seq.symbol, fldsyms, 1, 0,"", prg1)
     let syms = fldsyms + [ constructor, typesym]
      firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, types.f + it, prg2)
 else if input_1 in "Function function Builtin builtin Export unbound"then
 let t = parse(stubdict, getheader.input)
  let name = funcname.t
  let paratypes = funcparametertypes.t
  let sym = newsymbol(name, modname.f, paratypes, funcreturntype.t)
   assert iscomplex.modname.f = "T"_1 in fsig.sym report"Must use type T in function name or parameters in parameterized module and T cannot be used in non-parameterized module" + getheader.input
    if input_1 = "Export"_1 then
    firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f, types.f, prg.f)
    else if input_1 = "unbound"_1 then
    firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + sym, types.f, prg.f)
    else
     assert not(sym in defines.f)report"Function" + name.sym + "is defined twice in module" + print.modname.f
     let prg1 = if input_1 in "Builtin builtin"then
     let code2 =    if fsig.sym= "empty:seq.T"then Emptyseq + [ Words."VERYSIMPLE", Optionsym]
  else if fsig.sym = "getseqtype(T seq)"then
  [ Local.1, Lit.0, Idx."int"_1, Words."VERYSIMPLE", Optionsym]
  else if fsig.sym = "aborted(T process)"then
  [ Local.1, symbol("aborted(T process)","builtin","boolean")]
else  
     @(+, Local, empty:seq.symbol, arithseq(length.paratypes, 1, 1))
      + symbol(fsig.sym, if length.module.sym = 1 then"builtin"else"T builtin", returntype.sym)
       map(prg.f, sym, code2)
     else
      let discard = encode.symboltext(sym, modname.f, input)
       prg.f
      firstpass(modname.f, uses.f, defines.f + sym, if input_1 in "Function Builtin"then exports.f + sym else exports.f, unboundexports.f, unbound.f, types.f, prg1)
 else if input_1 in "module Module"then
 firstpass(mytype.if length.input > 2 then"T" + input_2 else [ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f, types.f, prg.f)
 else f

function roots(exported:seq.word, f:firstpass)seq.symbol
 if not(abstracttype.modname.f in exported) ∨ iscomplex.modname.f  then
 empty:seq.symbol
 else toseq.exports.f