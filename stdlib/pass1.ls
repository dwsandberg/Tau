Module pass1

use parse

use standard

use symbol

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

Export result(linkage)program

Export dict(linkage)set.symbol

Export compiled(linkage)set.symbol

Export roots(linkage)seq.symbol

Export mods(linkage)seq.firstpass

Export templates(linkage)program

Export alltypes(linkage)typedict

Export type:linkage internaltype

type linkage is result:program, compiled:set.symbol, roots:seq.symbol, mods:seq.firstpass, templates:program, alltypes:typedict, dict:set.symbol

function =(a:firstpass, b:firstpass)boolean modname.a = modname.b

Function ?(a:firstpass, b:firstpass)ordering toalphaseq.typerep.modname.a ? toalphaseq.typerep.modname.b

Function print(b:firstpass)seq.word
 " &br  &br" + print.modname.b + " &br defines" + printdict.defines.b
 + " &br unboundexports"
 + printdict.asset.unboundexports.b

Function find(modset:set.firstpass, name:mytype)set.firstpass
 findelement(firstpass(name, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, empty:seq.myinternaltype, emptyprogram)
 , modset
 )

function issimple2(s:symbol)seq.symbol if isabstract.modname.s then empty:seq.symbol else [ s]

Function pass1(allsrc:seq.seq.seq.word, exports:seq.word, librarymods:seq.firstpass)linkage
let alllibsym = for acc = empty:set.symbol, @e = librarymods do acc ∪ defines.@e end(acc)
∪ for acc = empty:set.symbol, @e = librarymods do acc ∪ exports.@e end(acc)
 let simplesym = asset.for acc = empty:seq.symbol, @e = toseq.alllibsym do acc + issimple2.@e end(acc)
 let libprg = program2.simplesym
 let libtemplates = program2(alllibsym - simplesym)
  \\ let discard = getinstance:encodingstate.symboltext \\
 let a = for acc = asset.librarymods, @e = allsrc do gathersymbols(acc, @e)end(acc)
  let expand1 = expanduse.expanduseresult(a, empty:seq.mapele)
  let u0 = firstpasses.expand1
   \\ let u1 = @(+, getunboundexport, empty:seq.unboundexport, toseq.u0)let d1 = resolveexport(u0, empty:set.symbol, mytype."1", u1, 1, empty:seq.unboundexport)\\
   let d1 = resolveunboundexports.u0
  let allsymbols1 = for acc = empty:set.symbol, @e = toseq.d1 do acc ∪ defines.@e end(acc)
  let alltypes0 = for acc = empty:seq.myinternaltype, @e = toseq.d1 do acc + types.@e end(acc)
    \\ assert false report"XX"+ @(seperator."
&br", towords,"", alltypes0)\\
    let alltypes = processtypedef(typedict.basetypes, alltypes0, 1, empty:seq.myinternaltype)
    let abstractsimple1 = split(toseq.d1, 1, empty:seq.firstpass, empty:seq.firstpass)
    let simple = abstractsimple1_2
    let abstract = abstractsimple1_1
   let prg1 = for acc = libprg, @e = simple do bind3(acc, alltypes, d1, @e)end(acc)
   let templates0 = for acc = libtemplates, @e = abstract do bind3(acc, alltypes, d1, @e)end(acc)
    let templates = maptemp(map.expand1, templates0)
   let roots = for acc = empty:seq.symbol, @e = simple do acc + roots(exports, @e)end(acc)
     linkage(prg1, asset.toseq.libprg, roots, simple + abstract, templates, alltypes, allsymbols1)

function basetypes seq.myinternaltype [ myinternaltype("defined"_1,"int"_1, mytype."standard", [ typeint]), myinternaltype("defined"_1,"boolean"_1, mytype."standard", [ typeint])]

function maptemp(map:seq.mapele, templates:program)program
 for st = templates, e = map do let s2 = lookupcode(templates, target.e)
  if isdefined.s2 then map(st, key.e, target.e, code.s2)
  else map(st, key.e, target.e, empty:seq.symbol) end(st)

function processtypedef(defined:typedict, undefined:seq.myinternaltype, i:int, newundefined:seq.myinternaltype)typedict
 if i > length.undefined then
 if length.newundefined = 0 then defined
  else
   assert length.undefined > length.newundefined report"unresolved types:" + for acc ="", @e = newundefined do list(acc," &br", print3.@e)end(acc)
    processtypedef(defined, newundefined, 1, empty:seq.myinternaltype)
 else
  let td = undefined_i
  let fldtypes = if kind.td ∈ "record"then
  for acc = empty:seq.mytype, @e = subflds.td do acc + parameter.@e end(acc)
  else if kind.td ∈ "sequence"then
  for acc = [ typeint], @e = subflds.td do acc + parameter.@e end(acc)
  else subflds.td
  let flds = for acc = empty:seq.mytype, idx = 1, fld = fldtypes do
   next(let tmp = subflddefined(defined, replaceT(modpara.td, fld))
    if idx = 1 ∨ isempty.tmp then tmp else if isempty.acc then acc else acc + tmp, idx + 1)
  end(acc)
   if length.flds = 0 then
   \\ some fld is not defined \\ processtypedef(defined, undefined, i + 1, newundefined + undefined_i)
   else processtypedef(defined + [ changesubflds(td, flds)], undefined, i + 1, newundefined)

function subflddefined(defined:typedict, typ:mytype)seq.mytype
 if abstracttype.typ ∈ "int seq real boolean T"then [ typ]
 else if abstracttype.typ ∈ "encoding"then [ typeint]
 else
  let typdesc = findelement(defined, typ)
   if isempty.typdesc then \\ not defined \\ empty:seq.mytype else subflds.typdesc_1

type unboundexport is modname:mytype, unbound:symbol

/function getunboundexport(f:firstpass)seq.unboundexport @(+, unboundexport(modname.f), empty:seq.unboundexport, unboundexports.f)

/function resolveexport(modset:set.firstpass, lastdict:set.symbol, lastmodname:mytype, toprocess:seq.unboundexport, i:int, unresolved:seq.unboundexport)set.firstpass if i > length.toprocess then if length.unresolved = 0 then modset else assert length.toprocess &ne length.unresolved report"unresolved exports"+ @(+, print,"", unresolved)resolveexport(modset, empty:set.symbol, mytype."1", unresolved, 1, empty:seq.unboundexport)else let u = toprocess_i let dict = if lastmodname = modname.u then lastdict else let e = find(modset, modname.u)@(∪, builddict.modset, defines.e_1 ∪ unbound.e_1, uses.e_1)let x = findelement2(dict, unbound.u)// assert not(mangledname.unbound.u ="typeQ3AwordZwords"_1)report print.u + toword.cardinality.x // if cardinality.x = 1 then assert resulttype.x_1 = resulttype.unbound.u report"export return type missmatch"+ print.unbound.u + print.x_1 let f = find(modset, modname.u)_1 let newf = firstpass(modname.f, uses.f, defines.f, replace(exports.f, x), unboundexports.f, unbound.f, types.f, prg.f)// let t = replace(modset, newf)let f2 = find(modset, modname.u)_1 // resolveexport(replace(modset, newf), dict, modname.u, toprocess, i + 1, unresolved)else resolveexport(modset, dict, modname.u, toprocess, i + 1, unresolved)

function print(x:unboundexport)seq.word" &br" + print.modname.x + print.unbound.x

function resolveunboundexports(modset:set.firstpass)set.firstpass
let u = for acc = empty:seq.firstpass, @e = toseq.modset do acc + hasunbound.@e end(acc)
let orgcount = for acc = 0, @e = u do acc + totalunbound.@e end(acc)
  if orgcount = 0 then modset
  else
  let newset = for acc = modset, @e = u do bindunboundexports(acc, @e)end(acc)
  let newcount = for acc = 0, @e = toseq.newset do acc + totalunbound.@e end(acc)
    if newcount = orgcount then
    assert orgcount = 0 report"unresolved exports"
    + for acc ="", @e = for acc = empty:seq.symbol, @e = u do acc + unboundexports.@e end(acc)do
     acc + print.@e end(acc)
      modset
    else resolveunboundexports.newset

function builddict(modset:set.firstpass, use:mytype)set.symbol
 let e = find(modset, use)
  if isempty.e then empty:set.symbol else exports.e_1

function builddict(modset:set.firstpass, f:firstpass)set.symbol
 for acc = defines.f ∪ unbound.f, @e = uses.f do acc ∪ builddict(modset, @e)end(acc)

function bindunboundexports(modset:set.firstpass, f:firstpass)set.firstpass
 if length.unboundexports.f = 0 then modset
 else
  let dict = builddict(modset, f)
  let acc0 = firstpass(modname.f, uses.f, defines.f, exports.f, empty:seq.symbol, unbound.f, types.f, prg.f)
  let new = for acc = acc0, @e = unboundexports.f do resolveexport(acc, dict, @e)end(acc)
   replace(modset, new)

function resolveexport(f:firstpass, dict:set.symbol, s:symbol)firstpass
 let x = findelement2(dict, s)
  if cardinality.x = 1 then
  assert resulttype.x_1 = resulttype.s report"export return type missmatch" + print.s + print.x_1
    firstpass(modname.f, uses.f, defines.f, exports.f ∪ x, unboundexports.f, unbound.f, types.f, prg.f)
  else
   firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + s, unbound.f, types.f, prg.f)

function expanduse(acc2:expanduseresult)expanduseresult
 let modset = firstpasses.acc2
let newset = for acc = acc2, @e = toseq.asset.for acc = empty:seq.mytype, @e = toseq.modset do acc + uses.@e end(acc)do
 expanduse2(acc, @e)end(acc)
  if cardinality.firstpasses.newset > cardinality.modset then expanduse.newset else acc2

type expanduseresult is firstpasses:set.firstpass, map:seq.mapele

function expanduse2(acc2:expanduseresult, use:mytype)expanduseresult
 let modset = firstpasses.acc2
 let x = find(modset, use)
  if iscomplex.use ∧ not(parameter.use = mytype."T")then
  if isempty.x then
   let template = find(modset, mytype("T" + abstracttype.use))
     assert not.isempty.template report"Cannot find module" + print.use
     let f = template_1
     let with = parameter.use
   let defs = for acc = empty:seq.mapele, @e = toseq.defines.f do acc + replaceTsymbol2(with, @e)end(acc)
   let exps = for acc = empty:seq.mapele, @e = toseq.exports.f do acc + replaceTsymbol2(with, @e)end(acc)
   let unb = for acc = empty:seq.mapele, @e = unboundexports.f do acc + replaceTsymbol2(with, @e)end(acc)
      expanduseresult(modset
    + firstpass(replaceT(with, modname.f), for acc = empty:seq.mytype, @e = uses.f do acc + replaceT(with, @e)end(acc), asset.for acc = empty:seq.symbol, @e = defs do acc + s.@e end(acc), asset.for acc = empty:seq.symbol, @e = exps do acc + s.@e end(acc), for acc = empty:seq.symbol, @e = unb do acc + s.@e end(acc), empty:set.symbol, for acc = empty:seq.myinternaltype, @e = types.f do acc + replaceTmyinternaltype(with, @e)end(acc), prg.f)
    , map.acc2 + defs + exps + unb
    )
   else acc2
 else assert not.isempty.x report"Cannot find module" + print.use
    acc2

function hasunbound(f:firstpass)seq.firstpass if length.unboundexports.f = 0 then empty:seq.firstpass else [ f]

function totalunbound(f:firstpass)int length.unboundexports.f

function split(s:seq.firstpass, i:int, abstract:seq.firstpass, simple:seq.firstpass)seq.seq.firstpass
 if i > length.s then [ abstract, simple]
 else
  let f = s_i
   if not.iscomplex.modname.f ∧ length.uses.f > 0 then
   split(s, i + 1, abstract, simple + f)
   else if parameter.modname.f = mytype."T"then split(s, i + 1, abstract + f, simple)
   else split(s, i + 1, abstract, simple)

function print(p2:program)seq.word
 for acc ="", @e = toseq.p2 do list(acc," &br  &br", print(p2, @e))end(acc)

function bind3(p:program, alltypes:typedict, modset:set.firstpass, f:firstpass)program
 let dict = builddict(modset, f) ∪ headdict
 for acc = p ∪ prg.f, @e = toseq.defines.f do bind2(acc, alltypes, dict, @e)end(acc)


function bind2(p:program, alltypes:typedict, dict:set.symbol, s:symbol)program
 let txt = findencode.symboltext(s, mytype."?","?")
  if not.isempty.txt then
  let code = parsedcode.parse(dict, text.txt_1)
    map(p, s, if length.code = 1 ∧ isconst.code_1 then code + [ Words."VERYSIMPLE", Optionsym]else code)
  else if parameter.modname.s = mytype."T" ∧ not(s ∈ p)then
  map(p, s, empty:seq.symbol)
  else p

Function headdict set.symbol asset.[ symbol("export","headdict","internal1"), symbol("stub","headdict","internal1")]

function gathersymbols(mods:set.firstpass, input:seq.seq.word)set.firstpass
 let acc0 = firstpass(mytype."?", empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, empty:seq.myinternaltype, emptyprogram)
let r = for acc = acc0, @e = input do gathersymbols(acc, headdict, @e)end(acc)
  assert not(r ∈ mods)report"duplicate module name:" + print.modname.r
   mods + r

type symboltext is ph:symbol, modname:mytype, text:seq.word

function hash(s:symboltext)int hash(fsig.ph.s + module.ph.s)

function =(a:symboltext, b:symboltext)boolean ph.a = ph.b

function assignencoding(l:int, s:symboltext)int assignrandom(l, s)

function fldcode(constructor:symbol, indexfunc:seq.symbol, syms:seq.symbol, i:int, knownoffset:int, offset:seq.word, prg:program)program
 if i > length.syms then
 \\ if offset =""then could build access function for type here but does not seem to impact overall performance to delay \\
  map(prg, constructor, indexfunc + symbol("build." + fsig.constructor,"x builtin","ptr"))
 else
  let this = syms_i
   if i = 1 ∧ length.syms = 1 ∧ knownoffset = 0 then
   map(map(prg, this, [ Local.1]), constructor, [ Local.1])
   else
    let fldtype = resulttype.this
    let offsetinc = if abstracttype.fldtype ∈ "real int seq word encoding boolean"then 1 else 0
    let knowntype = if fldtype = mytype."real" ∨ fldtype = mytype."boolean" ∨ fldtype = typeint then
    fldtype
    else if fldtype = mytype."word" ∨ abstracttype.fldtype = "encoding"_1 then typeint
    else if abstracttype.fldtype ∈ "seq" ∧ abstracttype.parameter.fldtype ∈ "real int word encoding boolean byte bit"then
    fldtype
    else typeptr
     if offset = "" ∧ knowntype ≠ typeptr then
     fldcode(constructor, indexfunc, syms, i + 1, knownoffset + 1, offset, map(prg, this, [ Local.1, Lit.knownoffset, Idx.knowntype]))
     else
      let newoffset = if offsetinc = 0 then
      if isempty.offset then typerep.fldtype else offset + "," + typerep.fldtype
      else offset
       \\ assert not.isempty.offset report"problem X"+ typerep.fldtype +"idxfunc"+"constr"+ print.constructor + stacktrace \\
       let code = [ Local.1
       , symbol("offsets(" + typerep.fldtype
       + if isempty.offset then")"else"," + offset + ")", [ toword.knownoffset] + "builtin", typerep.fldtype)
       ]
        fldcode(constructor, indexfunc, syms, i + 1, knownoffset + offsetinc, newoffset, map(prg, this, code))

function gathersymbols(f:firstpass, stubdict:set.symbol, input:seq.word)firstpass
 if length.input = 0 then
 let k = defines.f ∩ asset.unboundexports.f
   if isempty.k then f
   else
    firstpass(modname.f, uses.f, defines.f, exports.f ∪ k, toseq(asset.unboundexports.f - k), unbound.f, types.f, prg.f)
 else if input_1 ∈ "use"then
  let t = parse(empty:set.symbol, "type type is"+input << 1)
   firstpass(modname.f, uses.f +  parameter.(types.t)_1, defines.f, exports.f, unboundexports.f, unbound.f, types.f, prg.f)
 else if input_1 ∈ "type"then
 let b = parse(empty:set.symbol, input)
  let name = input_2
  let t = addabstract(name, parameter.modname.f)
   assert parameter.modname.f ∈ [ mytype."", mytype."T"]report"KLJKL"
   let it = if input_4 = "sequence"_1 ∨ abstracttype.parameter.(types.b)_1 = "sequence"_1 then
   myinternaltype("sequence"_1, name, modname.f, [ addabstract(":"_1, typeint)] + types.b << 1)
   else myinternaltype("record"_1, name, modname.f, types.b)
   let typesym = typesym.it
    if kind.it = "sequence"_1 then
   let constructor = newsymbol([ name], modname.f, for acc = [ typeint], @e = subflds.it << 1 do acc + parameter.@e end(acc), t)
   let fldsyms = for acc = empty:seq.symbol, m = subflds.it << 1 do acc + newsymbol([ abstracttype.m], modname.f, [ t], parameter.m)end(acc)
     let seqtype = addabstract("seq"_1, parameter.modname.f)
     let symtoseq = newsymbol("toseq", modname.f, [ t], seqtype)
     let symfromseq = newsymbol("to:" + print.t, modname.f, [ seqtype], t)
     let t1 = \\ if name ="pseq"_1 then"int"else \\"T"
     let indexfunc = Fref.newsymbol("_", modname.f, [ mytype(t1 + name), typeint], mytype.t1)
     let prg1 = fldcode(constructor, [ indexfunc], fldsyms, 1, 2,"", prg.f)
     let prg2 = map(prg1, symtoseq, [ Local.1 ,newsymbol("toseqX:T",mytype." T builtin",[typeptr],mytype."T seq")])
   let prg3 = map(prg2
   , symfromseq
   , 
   ifthenelse( [ Local.1, GetSeqType, indexfunc, EqOp]
   ,[Local.1], [Lit0, Lit0, Record.[ typeint, typeint]]
   , typeptr)+ symbol("bitcast(ptr)","builtin","ptr") 
   )
     let syms = fldsyms + [ constructor, typesym, symtoseq, symfromseq]
      if name ≠ "seq"_1 then
      firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, types.f + it, prg3)
      else
       let symlen = newsymbol("length", modname.f, [ t], typeint)
       let symgettype = newsymbol("getseqtype", modname.f, [ t], typeint)
       let prg4 = map(prg3, symlen, [ Local.1, GetSeqLength, Words."VERYSIMPLE", Optionsym])
       let prg5 = map(prg4, symgettype, [ Local.1, GetSeqType, Words."VERYSIMPLE", Optionsym])
        firstpass(modname.f, uses.f, defines.f ∪ asset(syms + symlen + symgettype), exports.f, unboundexports.f, unbound.f, types.f + it, prg5)
    else
    let constructor = newsymbol([ name], modname.f, for acc = empty:seq.mytype, @e = subflds.it do acc + parameter.@e end(acc), t)
    let fldsyms = for acc = empty:seq.symbol, m = types.b do acc + newsymbol([ abstracttype.m], modname.f, [ t], parameter.m)end(acc)
     let prg2 = fldcode(constructor, empty:seq.symbol, fldsyms, 1, 0,"", prg.f)
     let syms = fldsyms + [ constructor, typesym]
      firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, types.f + it, prg2)
 else if input_1 ∈ "Function function Builtin builtin Export unbound"then
 let t = parse(stubdict, getheader.input)
  let name = funcname.t
  let paratypes = funcparametertypes.t
  let sym = newsymbol(name, modname.f, paratypes, funcreturntype.t)
   assert iscomplex.modname.f = "T"_1 ∈ fsig.sym report"Must use type T in function name or parameters in parameterized module and T cannot be used in non-parameterized module" + getheader.input
    if input_1 = "Export"_1 then
    firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f, types.f, prg.f)
    else if input_1 = "unbound"_1 then
    firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + sym, types.f, prg.f)
    else
     assert not(sym ∈ defines.f)report"Function" + name.sym + "is defined twice in module" + print.modname.f
     let prg1 = if input_1 ∈ "Builtin builtin"then
     let code2 = if fsig.sym = "empty:seq.T"then  Emptyseq.mytype."T" 
      else if fsig.sym = "aborted(T process)"then
      [ Local.1, symbol("aborted(T process)","builtin","boolean")]
      else if fsig.sym = "true"then [ Littrue, Words."VERYSIMPLE", Optionsym]
      else if fsig.sym = "false"then [ Litfalse, Words."VERYSIMPLE", Optionsym]
      else
     for acc = empty:seq.symbol, @e = arithseq(length.paratypes, 1, 1)do acc + Local.@e end(acc)
       + if length.module.sym = 1 then [ sym, Words."BUILTIN", Optionsym]
       else [ symbol(fsig.sym,"T builtin", returntype.sym)]
       map(prg.f, sym, code2)
    else let discard = encode.symboltext(sym, modname.f, input)
       prg.f
      firstpass(modname.f, uses.f, defines.f + sym, if input_1 ∈ "Function Builtin"then exports.f + sym else exports.f, unboundexports.f, unbound.f, types.f, prg1)
 else if input_1 ∈ "module Module"then
 firstpass(mytype.if length.input > 2 then"T" + input_2 else [ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f, types.f, prg.f)
 else f

function roots(exported:seq.word, f:firstpass)seq.symbol
 if not(abstracttype.modname.f ∈ exported) ∨ iscomplex.modname.f then empty:seq.symbol else toseq.exports.f

Function processOption(p:program, txt:seq.word)program
 if length.txt < 3 ∨ first.txt ∉ "option"then p
 else
  let modname = getmod(txt, 2)
  let dict = asset.[ symbol("STATE","headdict","internal1"), symbol("PROFILE","headdict","internal1"), symbol("COMPILETIME","headdict","internal1"), symbol("INLINE","headdict","internal1"), symbol("NOINLINE","headdict","internal1")]
  let t = parse(dict, txt << (2 * length.modname))
  let name = funcname.t
  let paratypes = funcparametertypes.t
  let sym = newsymbol(name, mytype.modname, paratypes, funcreturntype.t)
  let r = lookupcode(p, sym)
  let option = fsig.(parsedcode.t)_1
   assert isdefined.r report"Option problem" + modname + print.sym + EOL
   + for acc ="", @e = toseq.p do acc
   + if(fsig.@e)_1 ∈ "findelement"then EOL + module.@e + fsig.@e else"" end(acc)
    addoption(p, sym, option)

function getmod(s:seq.word, i:int)seq.word
 if s_i ∈ "."then getmod(s, i + 2) + s_(i + 1)
 else empty:seq.word