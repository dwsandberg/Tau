Module pass1

run main test1

use blockseq.int

use deepcopy.linkage

use deepcopy.symbolset

use libscope

use parse

use process.bindinfo

use process.firstpass

use seq.firstpass

use seq.ipair.tree.seq.word

use seq.mytype

use seq.seq.seq.word

use seq.seq.word

use seq.stepresult

use seq.stkele

use seq.symbol

use set.firstpass

use set.mytype

use set.symbol

use set.word

use stack.stkele

use stacktrace

use stdlib

use symbol

use textio

type firstpass is record modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unbound:set.symbol, exportmodule:boolean, rawsrc:seq.seq.word

Function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, exportmodule:boolean)firstpass 
 firstpass(modname, uses, defines, exports, unboundexports, unboundx, exportmodule, empty:seq.seq.word)

Function exportmodule(firstpass)boolean export

Function modname(firstpass)mytype export

Function defines(firstpass)set.symbol export

Function exports(firstpass)set.symbol export

Function uses(firstpass)seq.mytype export

Function rawsrc(firstpass)seq.seq.word export

Function replaceT(with:mytype, f:firstpass)firstpass 
 firstpass(replaceT(with, modname.f), @(+, replaceT.with, empty:seq.mytype, uses.f), asset.@(+, replaceT.with, empty:seq.symbol, toseq.defines.f), asset.@(+, replaceT.with, empty:seq.symbol, toseq.exports.f), @(+, replaceT.with, empty:seq.symbol, unboundexports.f), asset.@(+, replaceT.with, empty:seq.symbol, toseq.unbound.f), false, rawsrc.f)

function =(a:firstpass, b:firstpass)boolean modname.a = modname.b

Function ?(a:firstpass, b:firstpass)ordering modname.a ? modname.b

Function print(b:firstpass)seq.word 
 {"&br &br"+ print.modname.b +"&br defines"+ printdict.defines.b +"&br unboundexports"+ printdict.asset.unboundexports.b }

function find(modset:set.firstpass, name:mytype)set.firstpass 
 findelement(firstpass(name, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, false, empty:seq.seq.word), modset)

type linkage is record symset:symbolset, mods:seq.firstpass, roots:set.word

Function symset(linkage)symbolset export

Function mods(linkage)seq.firstpass export

Function roots(linkage)set.word export

Function pass1(allsrc:seq.seq.seq.word, exports:seq.word, librarysyms:symbolset, librarymods:set.firstpass)linkage 
 PROFILE.// assert false report print.librarysyms // 
  let a = @(+, gathersymbols.exports, librarymods, allsrc)
  let d2 = resolveunboundexports.expanduse.a 
  let simple = @(+, findsimple, empty:seq.firstpass, toseq.d2)
  let roots = toseq.asset.@(+, roots,"", simple)
  let abstractmods = @(+, templates.d2, empty:seq.firstpass, toseq.d2)
  let templates = @(+, clean, emptysymbolset, toseq.@(∪, defines, empty:set.symbol, abstractmods))
  let knownsymbols = @(+, identity, librarysyms, toseq.@(∪, defines, empty:set.symbol, simple))
  let known2 = @(addinternal, identity, knownsymbols, toseq.d2)
  let X = @(bind(templates, d2), identity, known2, simple)
  linkage(X, simple + abstractmods, asset.roots)

function clean(s:symbol)symbol 
 if length.src.s > 0 ∧ src(s)_1 ="parsedfunc"_1 
  then changesrc(s, subseq(src.s, toint(src(s)_2)+ 3, length.src.s))
  else s

function addinternal(known:symbolset, sym:symbol)symbolset 
 if modname.sym = mytype."internal"
  then let x = lookupsymbol(known, mangledname.sym)
   if isdefined.x then known else replace(known, sym)
  else known

function addinternal(known:symbolset, f:firstpass)symbolset 
 @(addinternal, identity, known, toseq.defines.f)

function recordsize(src:seq.word, i:int)int 
 // bug if made tail recursive ? // 
  if i > length.src 
  then 0 
  else if i = 1 ∧ src_i ="FREF"_1 
  then recordsize(src, i + 2)+ 1 
  else if src_i ="PARAM"_1 
  then recordsize(src, i + 2)+ 1 
  else if src_i ="LIT"_1 then recordsize(src, i + 3)else 10000

function removeflat(p:word, i:int)seq.word 
 if i = 0 
  then""
  else removeflat(p, i - 1)+"PARAM"+ p +"LIT"+ toword.i +"IDXUC"

function resolveunboundexports(modset:set.firstpass)set.firstpass 
 let u = @(+, hasunbound, empty:seq.firstpass, toseq.modset)
  let orgcount = @(+, totalunbound, 0, u)
  if orgcount = 0 
  then modset 
  else let newset = @(bindunboundexports, identity, modset, u)
  let newcount = @(+, totalunbound, 0, toseq.newset)
  if newcount = orgcount then modset else resolveunboundexports.newset

function builddict(modset:set.firstpass, use:mytype)set.symbol 
 let e = find(modset, use)
  if isempty.e then empty:set.symbol else exports(find(modset, use)_1)

function builddict(modset:set.firstpass, f:firstpass)set.symbol 
 @(∪, builddict.modset, defines.f ∪ unbound.f, uses.f)

function bindunboundexports(modset:set.firstpass, f:firstpass)set.firstpass 
 if length.unboundexports.f = 0 
  then modset 
  else let dict = builddict(modset, f)
  let new = @(resolveexport.dict, identity, firstpass(modname.f, uses.f, defines.f, exports.f, empty:seq.symbol, unbound.f, exportmodule.f, rawsrc.f), unboundexports.f)
  replace(modset, new)

function resolveexport(dict:set.symbol, f:firstpass, s:symbol)firstpass 
 let x = findelement2(dict, s)
  if cardinality.x = 1 
  then firstpass(modname.f, uses.f, defines.f, exports.f ∪ x, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
  else firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + s, unbound.f, exportmodule.f, rawsrc.f)

function expanduse(modset:set.firstpass)set.firstpass 
 let newset = @(expanduse, identity, modset, toseq.asset.@(+, uses, empty:seq.mytype, toseq.modset))
  if cardinality.newset > cardinality.modset then expanduse.newset else modset

function expanduse(modset:set.firstpass, use:mytype)set.firstpass 
 let x = find(modset, use)
  if iscomplex.use ∧ not(parameter.use = mytype."T")
  then if isempty.x 
   then let template = find(modset, mytype("T"+ abstracttype.use))
    assert not.isempty.template report"Cannot find module"+ print.use 
    modset + replaceT(parameter.use, template_1)
   else modset 
  else assert not.isempty.x report"Cannot find module"+ print.use + @(+, print,"", @(+, modname, empty:seq.mytype, toseq.modset))
  modset

function hasunbound(f:firstpass)seq.firstpass 
 if length.unboundexports.f = 0 then empty:seq.firstpass else [ f]

function totalunbound(f:firstpass)int length.unboundexports.f

function findsimple(f:firstpass)seq.firstpass 
 if length.towords.modname.f = 1 ∧ length.uses.f > 0 then [ f]else empty:seq.firstpass

function templates(modset:set.firstpass, f:firstpass)seq.firstpass 
 if parameter.modname.f = mytype."T"
  then if length.uses.f > 0 
   then let newdefines = @(+, template(builddict(modset, f)∪ headdict), empty:seq.symbol, toseq.defines.f)
    [ firstpass(modname.f, uses.f, asset.newdefines, exports.f, empty:seq.symbol, empty:set.symbol, exportmodule.f, rawsrc.f)]
   else [ f]
  else empty:seq.firstpass

function template(dict:set.symbol, s:symbol)symbol 
 if src(s)_1 in"sequence record encoding Encoding"
  then s 
  else let b = parse(bindinfo(dict,"", empty:seq.mytype), src.s)
  changesrc(s, parsedresult.b)

function bind(templates:symbolset, modset:set.firstpass, a:symbolset, f:firstpass)symbolset 
 PROFILE.let x = subseq(towords.modname.f, 1, length.towords.modname.f - 1)
  if x =""
  then let dict = builddict(modset, f)∪ headdict 
   let b = @(x2(templates, dict), identity, a, toseq.exports.f)
   @(bind(templates, dict), identity, b, toseq.defines.f)
  else if x ="T"
  then @(bind(templates, builddict(modset, f)∪ headdict), identity, a, toseq.defines.f)
  else a

function iscomplex(s:symbol)seq.symbol 
 if iscomplex.modname.s then [ s]else empty:seq.symbol

function x2(templates:symbolset, dict:set.symbol, knownsymbols:symbolset, s:symbol)symbolset 
 if iscomplex.modname.s 
  then known.X(mangledname.s, s, dict, parameter.modname.s, templates, knownsymbols)
  else knownsymbols

function bind(templates:symbolset, dict:set.symbol, knownsymbols:symbolset, s:symbol)symbolset 
 PROFILE.let symsrc = src.s 
  if length.symsrc = 2 ∧ symsrc_1 ="LIT"_1 
  then knownsymbols 
  else if symsrc_1 in"type sequence record encoding Encoding"
  then postbindtypes(dict, mytype."", templates, knownsymbols, src.s, s, s)
  else assert length.src.s > 2 report"PROBLEM TT"
  let b = parse(bindinfo(dict,"", empty:seq.mytype), symsrc)
  let code = code.b 
  let s2 = // changesrc(s, src.s, src.s, code)// s 
  if code_1 in"type sequence record encoding Encoding"
  then postbindtypes(dict, mytype."", templates, knownsymbols, code, s2, s2)
  else postbind(dict, mytype."", templates, knownsymbols, parsedresult.b, s2, s2)

resultpair type is needed because calculation often involve adding new known symbols.

type resultpair is record known:symbolset, size:seq.word

Function lookuptypedesc2(knownsymbols:symbolset, typ:seq.word)symbol 
 let name = mangle(merge("typedesc:"+ typ), mytype."internal", empty:seq.mytype)
  lookupsymbol(knownsymbols, name)

Function extracttypedesc(a:symbol)seq.word 
 if isdefined.a 
  then subseq(src.a, if src(a)_1 ="WORDS"_1 then 3 else 1, length.src.a)
  else"undefined"

function definetypedesc(knownsymbols:symbolset, t:mytype, code:seq.word)symbol 
 let s1 = lookuptypedesc2(knownsymbols, print.t)
  let s = if isdefined.s1 
   then s1 
   else symbol(merge("typedesc:"+ print.t), mytype."internal", empty:seq.mytype, mytype."word seq","")
  changesrc(s, if code_1 in"record sequence pending"
   then code 
   else"WORDS"+ toword.length.code + code)

function buildtypedesc(knownsymbols:symbolset, k:seq.word, t:mytype)seq.word 
 k + if abstracttype.t in"word int seq"
  then print.t 
  else if abstracttype.t ="encoding"_1 
  then"int"
  else let s = lookuptypedesc2(knownsymbols, print.t)
  assert isdefined.s report"type?"+ print.t 
  let a = extracttypedesc.s 
  subseq(a, 2, length.a)

function checkdefined(org:symbol, dict:set.symbol, templates:symbolset, knownsymbols:symbolset, t:mytype)symbolset 
 assert not("T"_1 in towords.t)report"ERR104"+ print.t 
  if abstracttype.t in"word int seq encoding T"
  then knownsymbols 
  else let s = lookuptypedesc2(knownsymbols, print.t)
  let a = extracttypedesc.s 
  if not(a_1 in"record")
  then knownsymbols 
  else assert not(a ="pending")report"ERROR101"+ a 
  // assert false report"ERROR101"+ name // 
  definestructure(org, dict, templates, a, parameter.t, replace(knownsymbols, definetypedesc(knownsymbols, t,"pending")), 3 + toint(a_3)+ 1,"", empty:seq.mytype,"")

function definestructure(org:symbol, dict:set.symbol, templates:symbolset, src:seq.word, modname:mytype, knownsymbols:symbolset, i:int, offset:seq.word, paras:seq.mytype, constructor:seq.word)symbolset 
 if i > length.src 
  then let consrc = if length.paras = 1 
    then"PARAM 1"
    else constructor +"RECORD"+ toword.recordsize(constructor, 1)
   let con = symbol(src_2, modname, paras, mytype(towords.parameter.modname + src_2), consrc)
   if src_1 ="sequence"_1 
   then let t = mytype(towords.parameter.modname + src_2)
    let symtoseq = symbol("toseq"_1, modname, [ mytype("T"+ src_2)], mytype(towords.parameter.t +"seq"_1),"PARAM 1")
    // assert not(src_2 ="pseq"_1 ∧ print.modname ="seq.word")report print.modname + src +"&br"+ print2.symtoseq // 
    let descsym = definetypedesc(knownsymbols, mytype(towords.parameter.modname + src_2),"1 seq."+ print.parameter.modname)
    assert not("T"_1 in src.descsym)report"ERR1011"+ src.descsym +">>"+ print.org 
    replace(replace(replace(knownsymbols, con), symtoseq), descsym)
   else // assert not(mytype."bit bitpackedseq"in paras)report src // 
   let newk = @(checkdefined(org, dict, templates), replaceT.parameter.modname, knownsymbols, paras)
   let dsrc = @(buildtypedesc.newk, replaceT.parameter.modname,"", paras)
   assert not("T"_1 in dsrc)report"ERR1010"+ dsrc +">>"+ print.org 
   let descsym = definetypedesc(knownsymbols, resulttype.con, [ offset_2]+ dsrc)
   replace(replace(knownsymbols, con), descsym)
  else let len = toint(src_i)
  let fldtype = mytype.subseq(src, i + 1, i + len - 1)
  let thetype = replaceT(parameter.modname, fldtype)
  assert length.towords.thetype > 0 report"ERR16"+ toword.i + src +"/"+ towords.fldtype +"/"+ towords.thetype +"/"+ print.modname 
  let z1 = if abstracttype.thetype in // set should not need to be included //"int real seq word encoding set"
   then resultpair(knownsymbols,"LIT 1")
   else let code = extracttypedesc.lookuptypedesc2(knownsymbols, print.thetype)
   assert not(code ="undefined")report"can not find type"+ print.thetype +"for"+ print.org + src 
   if not(code_1 in"record sequence")
   then resultpair(knownsymbols,"LIT"+ code_1)
   else let len2 = toint(code_3)
   let modname2 = replaceT(parameter.thetype, mytype.subseq(code, 3 + 1, 3 + len2))
   let newknown = definestructure(org, dict, templates, code, modname2, knownsymbols, 3 + len2 + 1,"", empty:seq.mytype,"")
   let z = extracttypedesc.lookuptypedesc2(newknown, print.thetype)
   assert not(code ="undefined")report"ERR30"+ print.thetype 
   resultpair(newknown,"LIT"+ z_1)
  let newoffset = if offset =""
   then size.z1 
   else"LIT"+ toword(toint(offset_2)+ toint(size(z1)_2))
  let fldsrc = if offset =""
   then if i + len + 1 > length.src then"PARAM 1"else"PARAM 1 LIT 0 IDXUC"
   else"PARAM 1"+ offset +"IDXUC"
  let ptype = if parameter.modname = mytype.""then [ src_2]else"T"+ src_2 
  let fldsym = symbol(src_(i + len), modname, [ mytype.ptype], fldtype, fldsrc)
  let confld = if size.z1 ="LIT 1"
   then"PARAM"+ toword(length.paras + 1)
   else"PARAM"+ toword(length.paras + 1)+ if size.z1 ="LIT 1"
    then""
    else removeflat(toword(length.paras + 1), toint(size(z1)_2) - 1)
  definestructure(org, dict, templates, src, modname, replace(known.z1, fldsym), i + len + 1, newoffset, paras + fldtype, constructor + confld)

struct cinfo{ BT(* copy)(processinfo, BT); BT(* look)(processinfo, BT, BT); BT(*add)(processinfo, BT, BT, BT); BT no; BT nameasword; BT persitant; BT typeaswords;};

function postbindtypes(dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset, code:seq.word, thissymbol:symbol, org:symbol)symbolset 
 if code_1 in"record"
  then let len = toint(code_3)
   let modname = replaceT(modpara, mytype.subseq(code, 3 + 1, 3 + len))
   definestructure(org, dict, templates, code, modname, replace(knownsymbols, changesrc(thissymbol,"pending")), 3 + len + 1,"", empty:seq.mytype,"")
  else if code_1 in"sequence"
  then let mn = mangle("_"_1, modname.thissymbol, [ mytype("T"+ code_2), mytype."int"])
   let newknown = known.X(mn, org, dict, modpara, templates, knownsymbols)
   let len = toint(code_3)
   let modname = replaceT(modpara, mytype.subseq(code, 3 + 1, 3 + len))
   assert modname = modname.thissymbol report towords.modname +"///2"+ towords.modname.thissymbol 
   definestructure(org, dict, templates, code, modname.thissymbol, newknown, 3 + len + 1,"LIT 1", empty:seq.mytype,"FREF"+ mn)
  else if code_1 in"encoding Encoding"
  then let encodingtype = mytype.subseq(code, 4, length.code - 1)
   let lkup = lookup(dict,"lookup"_1, [ encodingtype, mytype(towords.encodingtype + switch)])
   assert not.isempty.lkup report"no lookup for"+ code_2 + print.encodingtype 
   let iadd = lookup(dict,"add"_1, [ mytype(towords.encodingtype + switch), mytype."int", encodingtype])
   assert not.isempty.iadd report"no add for"+ code_2 + print.encodingtype 
   let copy = deepcopymangle.encodingtype 
   let newsrc ="FREF"+ copy +"FREF"+ mangledname(lkup_1)+"FREF"+ mangledname(iadd_1)+(if name.thissymbol ="wordencoding"_1 
    then"LIT 1"
    else"LIT 0")+"WORD"+ mangledname.thissymbol +(if code_1 ="encoding"_1 then"LIT 0"else"LIT 1")+"RECORD 6 NOINLINE"
   let new1 = known.X(mangledname(lkup_1), org, dict, modpara, templates, knownsymbols)
   let new2 = known.X(mangledname(iadd_1), org, dict, modpara, templates, new1)
   let newknown = known.X(copy, org, dict, modpara, templates, new2)
   let syme = changesrc(thissymbol, newsrc)
   postbind(dict, mytype."", templates, replace(newknown, syme), src.syme, syme, org)
  else assert false report"not a type"+ code 
  emptysymbolset

function postbind(dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset, code:seq.word, thissymbol:symbol, org:symbol)symbolset 
 assert not(code_1 in"record sequence encoding Encoding")report"not expecting type"+ code + stacktrace 
  postbind2(org, dict, modpara, templates, knownsymbols, code, 1,"", thissymbol)

function topara(i:int)seq.word {"PARAM"+ toword.i }

function postbind2(org:symbol, dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset, code:seq.word, i:int, result:seq.word, thissymbol:symbol)symbolset 
 if i > length.code 
  then let src = result 
   replace(knownsymbols, changesrc(thissymbol, result))
  else if code_i in"IDXUC FREF if assertZbuiltinZwordzseq NOINLINE builtinZtestZinternal1 STATEZtestZinternal1 builtinZtestZwordzseq"
  then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 1, result + code_i, thissymbol)
  else if code_i in"WORDS"
  then if toint(code_(i + 1))+ 3 ≤ length.code ∧ code_(toint(code_(i + 1))+ 3)="builtinZtestZwordzseq"_1 
   then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 3 + toint(code_(i + 1)), result + subseq(code, i + 2, length.code), thissymbol)
   else postbind2(org, dict, modpara, templates, knownsymbols, code, i + 2 + toint(code_(i + 1)), result + subseq(code, i, i + 1 + toint(code_(i + 1))), thissymbol)
  else if code_i in"COMMENT parsedfunc"
  then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 2 + toint(code_(i + 1)), result + subseq(code, i, i + 1 + toint(code_(i + 1))), thissymbol)
  else if code_i in"LIT APPLY RECORD SET PARAM PRECORD WORD"
  then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 2, result + subseq(code, i, i + 1), thissymbol)
  else if code_i ="usemangleZtest"_1 
  then let builtinname = mangle(name.thissymbol, mytype."builtin", paratypes.thissymbol)
   let src = @(+, topara,"", arithseq(length.paratypes.thissymbol, 1, 1))+ builtinname 
   postbind2(org, dict, modpara, templates, knownsymbols, code, i + 1, result + src, thissymbol)
  else if code_i ="NOOPZtest"_1 
  then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 1, result +"PARAM 1", thissymbol)
  else if code_i ="IDXUCZtest"_1 
  then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 1, result +"PARAM 1 PARAM 2 IDXUC", thissymbol)
  else if code_i ="FROMSEQ51Ztest"_1 
  then let mn = mangle("_"_1, modname.thissymbol, [ mytype("T"+ abstracttype.resulttype.thissymbol), mytype."int"])
   let newknown = known.X(mn, org, dict, modpara, templates, knownsymbols)
   let f1 ="PARAM 1 LIT 0 IDXUC FREF"+ mn +"Q3DZbuiltinZintZint PARAM 1 LIT 0 LIT 0 RECORD 2 if"
   postbind2(org, dict, modpara, templates, newknown, code, i + 1, result + f1, thissymbol)
  else let z = X(code_i, org, dict, modpara, templates, knownsymbols)
  postbind2(org, dict, modpara, templates, known.z, code, i + 1, result + size.z, thissymbol)

function X(mangledname:word, org:symbol, dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset)resultpair 
 let t1 = lookupsymbol(knownsymbols, mangledname)
  if isdefined.t1 
  then let src = src.t1 
   if src_1 in"record encoding Encoding"
   then let down = codedown.mangledname 
    assert length(down_2)= 1 report"inX"+ print2.t1 
    resultpair(postbindtypes(dict, mytype(down_2), templates, knownsymbols, src, t1, org), [ mangledname])
   else resultpair(knownsymbols,  [ mangledname])
  else let down = codedown.mangledname 
  assert length.down > 1 report"LLLx"+ mangledname 
  let newmodname = replaceT(modpara, mytype(down_2))
  let newmodpara = parameter.newmodname 
  let templatename = abstracttype.newmodname 
  if templatename ="local"_1 ∧ down_1 = [ merge."sizeoftype:T"]
  then if towords.modpara in ["int"]∨ abstracttype.modpara ="seq"_1 
   then resultpair(knownsymbols,"LIT 1")
   else let xx = extracttypedesc.lookuptypedesc2(knownsymbols, print.modpara)
   if xx_1 in"1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16"
   then resultpair(knownsymbols,"LIT"+ xx_1)
   else assert false report"did it get here?"+ xx 
   X(merge("sizeoftype:"+ print.modpara), org, dict, modpara, templates, knownsymbols)
  else if templatename in"para local"
  then resultpair(knownsymbols, //"PARAM"+ down_2_1 // [ mangledname])
  else if templatename ="deepcopy"_1 
  then if down_1 ="deepcopy"
   then // assert false report"XX"+ mangledname // 
    // assert code_i &ne"deepcopyZTzseqzdeepcopyZT"_1 report"ERR677"+ newmodpara // 
    assert down_3 in ["T"]report"OOO"+ down_3 + print.newmodpara 
    definedeepcopy(dict, templates, knownsymbols, if down_3 ="T"then newmodpara else mytype(down_3), org)
   else // Compile options // resultpair(knownsymbols, down_1)
  else let params = @(+, mytype, empty:seq.mytype, subseq(down, 3, length.down))
  let fullname = mangle(down_1_1, newmodname, params)
 //  assert not(mangledname="frombits2Q3ATZTzbitpackedseqZbits"_1) 
   report   [fullname]+print.newmodpara+@(seperator("&br"),print2,"",toseq.knownsymbols) //
  let t2 = lookupsymbol(knownsymbols, fullname)
  if fullname ≠ mangledname ∧ isdefined.t2 
  then // assert mangledname ="inZwordzseqzseqZTZTzseq"_1 report"ERR13"+ fullname + mangledname // 
   let src = src.t2 
   if src_1 in"sequence record"
   then resultpair(postbindtypes(dict, newmodpara, templates, knownsymbols, src, t2, org), [ fullname])
   else resultpair(knownsymbols, [ fullname])
  else let f = lookupsymbol(templates, mangle(down_1_1, mytype("T"+ templatename), params))
  if isdefined.f 
  then let newsymbol = symbol(down_1_1, newmodname, params, replaceT(newmodpara, resulttype.f), src.f)
   assert length.src.f > 0 report"MMM4"+ mangledname.f 
   let a = if src(f)_1 in"record sequence encoding Encoding"
    then postbindtypes(dict, newmodpara, templates, knownsymbols + newsymbol, src.f, newsymbol, org)
    else postbind(dict, newmodpara, templates, knownsymbols + newsymbol, src.f, newsymbol, org)
   resultpair(a, [ fullname])
  else 
  let params2 = @(+, replaceT.modpara, empty:seq.mytype, params)
  let k2 = lookup(dict, down_1_1, params2)
  let k=if cardinality.k2=0 then
        // case for examples like "frombits:T(bits) T" which needs to find "frombits:bit(bits) bit //
        // assert down_1_1 in [merge("frombits:T")] report [down_1_1] //
       lookup(dict, replaceTinname(newmodpara,down_1_1), params2)
      else
        // often there is no T in the function name so a lookup assuming that is done first. //
       k2
  assert cardinality.k = 1 report"cannot find template  for"+
  down_1_1 +"("+ @(seperator.",", print,"", params2)+")while process"+ print.org 
  assert mangledname ≠ mangledname(k_1)report"ERR12"+ mangledname + print2(k_1)
  if not.isdefined.lookupsymbol(knownsymbols, mangledname(k_1))
  then X(mangledname(k_1), org, dict, mytype."T", templates, knownsymbols)
  else resultpair(knownsymbols, [ mangledname(k_1)])
  
 


function roots(f:firstpass)seq.word 
 if exportmodule.f then @(+, mangledname,"", toseq.exports.f)else""

Function headerdict set.symbol 
 let modulename = mytype."test"
  asset.[ symbol("export"_1, modulename, empty:seq.mytype, mytype."internal",""), 
  symbol("unbound"_1, modulename, empty:seq.mytype, mytype."internal",""), 
  symbol("stub"_1, modulename, empty:seq.mytype, mytype."internal",""), 
  symbol("usemangle"_1, modulename, empty:seq.mytype, mytype."internal","")]

function gathersymbols(exported:seq.word, src:seq.seq.word)firstpass 
 @(wrapgathersymbols(exported, headerdict), identity, firstpass(mytype."?", empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, false, src), src)

function wrapgathersymbols(exported:seq.word, stubdict:set.symbol, f:firstpass, input:seq.word)firstpass 
 gathersymbols(exported, stubdict, f, input)

function definefld(src:seq.word, modname:mytype, t:seq.mytype, m:mytype)symbol 
 symbol(abstracttype.m, modname, t, parameter.m, src)

function switch seq.word {"encodingstate"}

use seq.char

function hasT (s:seq.word,i:int) boolean
  // used to determine it type T is specified somewhere in function sig //
  if s_(i+1) in ":." then // s_i is name // hasT(s,i+2)
  else // at end of type // if s_i="T"_1 then  true
  else  if s_(i+1)  in ",(" then 
     hasT(s,i+2)
  else // at end of parameter list or beginning of function type // 
      false


function gathersymbols(exported:seq.word, stubdict:set.symbol, f:firstpass, input:seq.word)firstpass 
 // assert print.modname.f in ["?","stdlib","UTF8","altgen"]∨(print.modname.f ="bitpackedseq.T"∧ cardinality.defines.f + cardinality.unbound.f < 8)report print.modname.f + printdict.unbound.f // 
  if length.input = 0 
  then f 
  else if input_1 in"use"
  then let t = parse(empty:set.symbol, input)
   firstpass(modname.f, uses.f + mytype.code.t, defines.f, exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
  else if input_1 in"type"
  then let b = parse(empty:set.symbol, input)
   let kind = code(b)_1 
   let t = mytype(towords.parameter.modname.f + [ code(b)_2])
   if kind in"encoding Encoding"
   then assert parameter.modname.f = mytype.""report"encoding in template?"
    let typ = parameter(types(b)_1)
    let sym = symbol(code(b)_2, modname.f, empty:seq.mytype, mytype(towords.typ +"erecord"), code.b)
    firstpass(modname.f, uses.f + mytype(towords.typ +"encoding"), defines.f + changesrc(sym, code.b), exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
   else assert parameter.modname.f in [ mytype."", mytype."T"]report"KLJKL"
   // assert false report code.b // 
   let modnm = towords.modname.f 
   let code = subseq(code.b, 1, 2)+ toword.length.modnm + modnm + subseq(code.b, 3, length.code.b)
   let sizeofsym = definetypedesc(emptysymbolset, t, code)
   let constructor = symbol(code_2, modname.f, @(+, parameter, empty:seq.mytype, types.b), t, code)
   let syms = @(+, definefld(code, modname.f, [ t]), [ constructor, sizeofsym], types.b)+ if kind ="sequence"_1 
    then [ symbol("toseq"_1, modname.f, [ t], mytype(towords.parameter.t +"seq"_1), code)]
    else empty:seq.symbol 
   firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
  else if input_1 in"Function function"
  then let t = parse(stubdict, getheader.input)
   let name = funcname.t 
   let paratypes = funcparametertypes.t 
   assert  iscomplex.modname.f=hasT(input,2) report
      "Must use type T in function name or parameters in  parameterized module and T cannot be used in non-parameterized module"
       +getheader.input
   let firstinstruction = code(t)_1 
   if firstinstruction ="usemangleZtest"_1 
   then let sym = symbol(name, mytype.if iscomplex.modname.f then"T builtin"else"builtin", paratypes, funcreturntype.t, input)
    firstpass(modname.f, uses.f, defines.f + sym, if input_1 ="Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
   else let sym = symbol(name, modname.f, paratypes, funcreturntype.t, input)
   if"exportZtest"_1 = firstinstruction 
   then firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f, exportmodule.f, rawsrc.f)
   else if"unboundZtest"_1 = firstinstruction 
   then firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + sym, exportmodule.f, rawsrc.f)
   else assert not(sym in defines.f)report"Function"+ name.sym +"is defined twice in module"+ print.modname.f 
   firstpass(modname.f, uses.f, defines.f + sym, if input_1 ="Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
  else if input_1 in"module Module"
  then firstpass(mytype.if length.input > 2 then"T"+ input_2 else [ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f, input_2 in exported, rawsrc.f)
  else f

function definedeepcopy(dict:set.symbol, templates:symbolset, knownsymbols:symbolset, type:mytype, org:symbol)resultpair 
 // assert towords.type in ["int seq","int","word3","stat5","word seq","llvmtypeele","word","llvmconst","const3","inst","flddesc seq","match5","flddesc","templatepart seq","templatepart","internalbc","persistant"]report"definedeepcopy"+ towords.type // 
  let body = if abstracttype.type in"encoding int word"
   then resultpair(knownsymbols,"PARAM 1")
   else // assert length.print.type = 1 &or print.type in ["match5","seq.int","llvmconst","match5","inst","libsym","llvmtypeele","word3","const3","seq.word","stat5","seq.flddesc","flddesc","seq.templatepart","templatepart","set.mod2desc"]report"DDD"+ print.type // 
   if abstracttype.type ="seq"_1 
   then let typepara = parameter.type 
    let dc = deepcopymangle.typepara 
    let pseqidx = mangle("_"_1, type, [ mytype."T pseq", mytype."int"])
    let cat = mangle("+"_1, type, [ mytype."T seq", mytype."T"])
    let blockit = mangle("blockit"_1, mytype."int blockseq", [ mytype."T seq"])
    resultpair(knownsymbols,"LIT 0 LIT 0 RECORD 2 PARAM 1 FREF"+ dc +"FREF"+ cat +"FREF"+ pseqidx +"APPLY 5"+ blockit)
   else let name = mangle(merge("typedesc:"+ print.type), mytype."internal", empty:seq.mytype)
   // assert false report"ERR100"+ name +"NO test example for deepcopy"// 
   let a = lookupsymbol(knownsymbols, name)
   assert isdefined.a report"not defined"+ name 
   let z = if src(a)_1 ="record"_1 
    then let newknown = postbindtypes(dict, mytype."", templates, knownsymbols, src.a, a, org)
     let b = lookupsymbol(newknown, name)
     resultpair(newknown, src.b)
    else resultpair(knownsymbols, src.a)
   let src = size.z 
   assert src_1 ="WORDS"_1 report"deepcopy:type desc format is wrong"+ src 
   let y = subfld(src, 4, 0, 4)
   resultpair(known.z, if last.y ="1"_1 
    then // only one element in record so type is not represent by actual record // 
     "PARAM 1"+ subseq(y, 6, length.y - 2)
    else y)
  let sym = symbol("deepcopy"_1, mytype(towords.type +"deepcopy"), [ mytype."T"], type, size.body)
  resultpair(postbind(dict, mytype."", templates, known.body + sym, src.sym, sym, org), [ mangledname.sym])

function subfld(desc:seq.word, i:int, fldno:int, starttype:int)seq.word 
 if i > length.desc 
  then"RECORD"+ toword.fldno 
  else if i < length.desc ∧ desc_(i + 1)="."_1 
  then subfld(desc, i + 2, fldno, starttype)
  else let fldtype = mytype.@(+,_.desc,"", arithseq((i - starttype + 2)/ 2,-2, i))
  {"PARAM 1 LIT"+ toword.fldno +"IDXUC"+ deepcopymangle.fldtype + subfld(desc, i + 1, fldno + 1, i + 1)}

