#!/usr/local/bin/tau

Module other

run main test1

use newsymbol

use blockseq.int

use libscope

use newparse

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

use textio

type firstpass is record modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unbound:set.symbol, exportmodule:boolean

function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unbound:set.symbol, exportmodule:boolean)firstpass 
 export

function exportmodule(firstpass)boolean export

function modname(firstpass)mytype export

function defines(firstpass)set.symbol export

function exports(firstpass)set.symbol export

Function replaceT(with:mytype, f:firstpass)firstpass 
 firstpass(replaceT(with, modname.f), @(+, replaceT.with, empty:seq.mytype, uses.f), asset.@(+, replaceT.with, empty:seq.symbol, toseq.defines.f), asset.@(+, replaceT.with, empty:seq.symbol, toseq.exports.f), @(+, replaceT.with, empty:seq.symbol, unboundexports.f), asset.@(+, replaceT.with, empty:seq.symbol, toseq.unbound.f), false)

function =(a:firstpass, b:firstpass)boolean modname.a = modname.b

Function ?(a:firstpass, b:firstpass)ordering modname.a ? modname.b

function print(b:firstpass)seq.word 
 {"&br &br"+ print.modname.b +"&br defines"+ printdict.defines.b +"&br unboundexports"+ printdict.asset.unboundexports.b }

function find(modset:set.firstpass, name:mytype)set.firstpass 
 findelement(firstpass(name, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, false), modset)

type linkage is record symset:symbolset, mods:seq.firstpass, roots:set.word

function symset(linkage)symbolset export

function mods(linkage)seq.firstpass export

function roots(linkage)set.word export

Function pass1(allsrc:seq.seq.seq.word, exports:seq.word, librarysyms:symbolset, librarymods:set.firstpass)linkage 
 let a = @(+, gathersymbols.exports, librarymods, allsrc)
  let d2 = resolveunboundexports.expanduse.a 
  let simple = @(+, findsimple, empty:seq.firstpass, toseq.d2)
  let roots = toseq.asset.@(+, roots,"", simple)
  let abstractmods = @(+, templates.d2, empty:seq.firstpass, toseq.d2)
  let templates = @(+, identity, emptysymbolset, toseq.@(∪, defines, empty:set.symbol, abstractmods))
  let knownsymbols = @(+, identity, librarysyms, toseq.@(∪, defines, empty:set.symbol, simple))
  let known2 = @(addinternal, identity, knownsymbols, toseq.d2)
  let X = @(bind(templates, d2), identity, known2, simple)
  // assert false report"KKLL"+ print2.X_("wordencodingZstdlib"_1)// 
  linkage(X, simple + abstractmods, asset.roots)

function addinternal(known:symbolset, sym:symbol)symbolset 
 if modname.sym = mytype."internal"
  then let x = known_mangledname.sym 
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
  let new = @(resolveexport.dict, identity, firstpass(modname.f, uses.f, defines.f, exports.f, empty:seq.symbol, unbound.f, exportmodule.f), unboundexports.f)
  replace(modset, new)

function resolveexport(dict:set.symbol, f:firstpass, s:symbol)firstpass 
 let x = findelement2(dict, s)
  if cardinality.x = 1 
  then firstpass(modname.f, uses.f, defines.f, exports.f ∪ x, unboundexports.f, unbound.f, exportmodule.f)
  else firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + s, unbound.f, exportmodule.f)

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
  else assert not.isempty.x report"Cannot find module"+ print.use +
  @(+,print,"",@(+,modname,empty:seq.mytype,toseq.modset))
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
    [ firstpass(modname.f, empty:seq.mytype, asset.newdefines, exports.f, empty:seq.symbol, empty:set.symbol, exportmodule.f)]
   else [ f]
  else empty:seq.firstpass

function template(dict:set.symbol, s:symbol)symbol 
 if src(s)_1 in"type sequence record encoding LIT"
  then s 
  else let b = parse(bindinfo(dict,"", empty:seq.mytype), src.s)
  changesrc(s, code.b)

function bind(templates:symbolset, modset:set.firstpass, a:symbolset, f:firstpass)symbolset 
 let x = subseq(towords.modname.f, 1, length.towords.modname.f - 1)
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
 let symsrc = src.s 
  if length.symsrc = 2 ∧ symsrc_1 ="LIT"_1 
  then knownsymbols 
  else let code = if symsrc_1 in"type sequence record encoding"
   then symsrc 
   else assert length.src.s > 2 report"PROBLEM TT"
   code.parse(bindinfo(dict,"", empty:seq.mytype), symsrc)
  postbind(dict, mytype."", templates, knownsymbols, code, s, s)

type zzz is record known:symbolset, size:seq.word

function buildtypedesc(knownsymbols:symbolset, k:seq.word, t:mytype)seq.word 
 k + if abstracttype.t in"word int seq"
  then print.t 
  else if abstracttype.t ="encoding"_1 
  then"int"
  else let name = mangle(merge("typedesc:"+ print.t), mytype."internal", empty:seq.mytype)
  let a = knownsymbols_name 
  assert not(mangledname.a ="undefinedsym"_1)report"type?"+ name + print.t 
  // assert not(src(a)_1 in "type sequence record encoding") report "ERROR101"+print2.a //
  subseq(src.a,2,length.src.a)

  
function checkdefined(org:symbol, dict:set.symbol, templates:symbolset,   knownsymbols:symbolset,t:mytype)symbolset
  assert not("T"_1 in towords.t )report "ERR104"+print.t
  if abstracttype.t in"word int seq encoding T" then knownsymbols
  else 
  let name = mangle(merge("typedesc:"+ print.t), mytype."internal", empty:seq.mytype)
   let a = knownsymbols_name 
  assert not(mangledname.a ="undefinedsym"_1)report"type?2"+ name + print.t 
  if  not(src(a)_1 in "record")  then
   knownsymbols 
   else
    assert src.a &ne "pending" report "ERROR101"+print2.a
    // assert false report "ERROR101"+name //
      definestructure(org, dict, templates, src.a, parameter.t, 
  replace(knownsymbols, changesrc(a,"pending")), 3 +  toint((src.a)_3)+ 1,"", empty:seq.mytype,"")

  



function definestructure(org:symbol, dict:set.symbol, templates:symbolset, src:seq.word, modname:mytype, knownsymbols:symbolset, i:int, offset:seq.word, paras:seq.mytype, constructor:seq.word)symbolset 
 // assert src in ["sequence cseq 3 seq.T 2 int len 2 T element","sequence seq 3 seq.T 2 int length 2 T x","sequence pseq 3 seq.T 2 int length 3 T seq a 3 T seq b","record UTF8 1 UTF8 3 int seq toseqint","record bit 1 bits 2 int toint","record bits 1 bits 2 int toint","sequence bitpackedseq 3 bitpackedseq.T 2 int length 3 T seq data 2 bits part","sequence arithmeticseq 3 seq.T 2 int length 2 T step 2 T start","record word 1 stdlib 4 int seq encoding bb","record boolean 1 stdlib 2 int toint","record ordering 1 stdlib 2 int toint","record alphaword 1 stdlib 2 word toword","record invertedseq 3 invertedseq.T 5 T ipair seq seq hashtable 2 int elecount","record ipair 3 ipair.T 2 int index 2 T value","sequence dseq 3 seq.T 2 int length 2 T default 3 T seq data","sequence packedseq 3 packedseq.T 2 int length 3 T seq x","sequence blockseq 3 blockseq.T 2 int length 2 int blocksize 4 T seq seq data","record libsym 1 libscope 2 word fsig 3 word seq returntype 3 word seq instruction","record mytype 1 libscope 3 word seq towords","record libtype 1 libscope 2 word name 2 boolean abstract 2 word kind 3 mytype seq subtypes 2 offset size 3 word seq fldnames","record offset 1 libscope 2 int TSIZE 2 int LIT"]report"JKLLL"+ src // 
  if i > length.src 
  then let consrc = if length.paras = 1 
    then"PARAM 1 VERYSIMPLE"
    else constructor +"RECORD"+ toword.recordsize(constructor, 1)
   let con = symbol(src_2, modname, paras, mytype(towords.parameter.modname + src_2), consrc)
   if src_1 ="sequence"_1 
   then let t = mytype(towords.parameter.modname + src_2)
    let symtoseq = symbol("toseq"_1, modname, [ mytype("T"+ src_2)], mytype(towords.parameter.t +"seq"_1),"PARAM 1 VERYSIMPLE")
    // assert not(src_2 ="pseq"_1 ∧ print.modname ="seq.word")report print.modname + src +"&br"+ print2.symtoseq // 
    let descsym = symbol(merge("typedesc:"+ print.mytype(towords.parameter.modname + src_2)), mytype."internal", empty:seq.mytype, mytype."word seq","1 seq."+ print.parameter.modname)
      assert not("T"_1 in src.descsym) report "ERR1011"+src.descsym+">>"+print.org
    replace(replace(replace(knownsymbols, con), symtoseq), descsym)
   else // assert not(mytype."bit bitpackedseq"in paras)report src // 
   let newk=@(checkdefined(org , dict , templates ),replaceT.parameter.modname,knownsymbols,paras)
   let dsrc = @(buildtypedesc.newk, replaceT.parameter.modname,"", paras)
   assert not("T"_1 in dsrc) report "ERR1010"+dsrc+">>"+print.org
   let descsym = symbol(merge("typedesc:"+ print.resulttype.con), mytype."internal", empty:seq.mytype, mytype."word seq", [ offset_2]+ dsrc)
   replace(replace(knownsymbols, con), descsym)
  else let len = toint(src_i)
  let fldtype = mytype.subseq(src, i + 1, i + len - 1)
  let thetype = replaceT(parameter.modname, fldtype)
  assert length.towords.thetype > 0 report"ERR16"+ toword.i + src +"/"+ towords.fldtype +"/"+ towords.thetype +"/"+ print.modname 
  let z1 = if abstracttype.thetype in // set should not need to be included //"int real seq word encoding set"
   then zzz(knownsymbols,"LIT 1")
   else let sym2 = knownsymbols_mangle(merge("typedesc:"+ print.thetype), mytype."internal", empty:seq.mytype)
   assert isdefined.sym2 report"can not find type"+ print.thetype +"for"+ print.org +src
   if not(src(sym2)_1 in"record sequence")
   then zzz(knownsymbols,"LIT"+ src(sym2)_1)
   else let code = src.sym2 
   let len2 = toint(code_3)
   let modname2 = replaceT(parameter.thetype, mytype.subseq(code, 3 + 1, 3 + len2))
   let newknown = definestructure(org, dict, templates, src.sym2, modname2, knownsymbols, 3 + len2 + 1,"", empty:seq.mytype,"")
   let z = newknown_mangledname.sym2 
   assert isdefined.z report"ERR30"+ mangledname.sym2 
   zzz(newknown,"LIT"+ src(z)_1)
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

struct cinfo{ BT (* copy) (processinfo,BT) ;
             BT (* look)(processinfo,BT,BT);
             BT (*add)(processinfo,BT,BT,BT);
             BT no; 
             BT nameasword; BT persitant;
             BT typeaswords;};


function postbind(dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset, code:seq.word, thissymbol:symbol, org:symbol)symbolset 
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
  else if code_1 in"encoding"
  then let encodingtype = mytype.subseq(code, 4, length.code - 1)
   let lkup = lookup(dict,"lookup"_1, [ encodingtype, mytype(towords.encodingtype +"invertedseq")])
   assert not.isempty.lkup report"no lookup for"+ code_2 + print.encodingtype 
   let iadd = lookup(dict,"add"_1, [ mytype(towords.encodingtype +"invertedseq"), mytype."int", encodingtype])
   assert not.isempty.iadd report"no add for"+ code_2 + print.encodingtype 
   let copy = deepcopymangle.encodingtype 
   let newsrc ="FREF"+ copy +"FREF"+ mangledname(lkup_1)+"FREF"+ mangledname(iadd_1)+(if name.thissymbol ="wordencoding"_1 
    then"LIT 1"
    else"LIT 0")+"WORD"+ mangledname.thissymbol +(if code_1 ="encoding"_1 then"LIT 0"else"LIT 1")+"WORDS"+ toword.length.towords.encodingtype + towords.encodingtype +"RECORD 7 NOINLINE"
   let new1 = known.X(mangledname(lkup_1), org, dict, modpara, templates, knownsymbols)
   let new2 = known.X(mangledname(iadd_1), org, dict, modpara, templates, new1)
   let newknown = known.X(copy, org, dict, modpara, templates, new2)
   replace(newknown, changesrc(thissymbol, newsrc))
  else if last.code ="builtinZtestZinternal1"_1 
  then if code ="NOOPZtest builtinZtestZinternal1"
   then replace(knownsymbols, changesrc(thissymbol,"PARAM 1 VERYSIMPLE"))
   else if code ="EMPTYSEQ51Ztest builtinZtestZinternal1"
   then replace(knownsymbols, changesrc(thissymbol,"LIT 0 LIT 0 RECORD 2 VERYSIMPLE"))
   else if code ="CALLIDXZtest builtinZtestZinternal1"
   then replace(knownsymbols, changesrc(thissymbol,"PARAM 1 PARAM 2 PARAM 3 CALLIDX VERYSIMPLE"))
   else if code ="IDXUCZtest builtinZtestZinternal1"
   then replace(knownsymbols, changesrc(thissymbol,"PARAM 1 PARAM 2 IDXUC VERYSIMPLE"))
   else if code ="FROMSEQ51Ztest builtinZtestZinternal1"
   then let mn = mangle("_"_1, modname.thissymbol, [ mytype("T"+ abstracttype.resulttype.thissymbol), mytype."int"])
    let newknown = known.X(mn, org, dict, modpara, templates, knownsymbols)
    let f1 ="PARAM 1 LIT 0 IDXUC FREF"+ mn +"Q3DZbuiltinZintZint PARAM 1 LIT 0 LIT 0 RECORD 2 if"
    replace(newknown, changesrc(thissymbol, f1))
   else if code ="usemangleZtest builtinZtestZinternal1"∨ code ="usemangleZtest STATEZtestZinternal1 builtinZtestZinternal1"
   then let builtinname = mangle(name.thissymbol, mytype."builtin", paratypes.thissymbol)
    let src = if mangledname.thissymbol = builtinname 
     then if length.code = 3 then"STATE EXTERNAL"else"EXTERNAL"
     else @(+, topara,"", arithseq(length.paratypes.thissymbol, 1, 1))+ mangle(name.thissymbol, mytype."builtin", paratypes.thissymbol)+ if length.code = 3 then"STATE"else""
    replace(knownsymbols, changesrc(thissymbol, src))
   else assert false report"QQ5 builtin"
   knownsymbols 
  else if last.code ="builtinZtestZwordzseq"_1 ∧ code_1 ="WORDS"_1 
  then replace(knownsymbols, changesrc(thissymbol, subseq(code, 3, length.code - 1)))
  else postbind2(org, dict, modpara, templates, knownsymbols, code, 1,"", thissymbol)

function topara(i:int)seq.word {"PARAM"+ toword.i }

function postbind2(org:symbol, dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset, code:seq.word, i:int, result:seq.word, thissymbol:symbol)symbolset 
 if i > length.code 
  then let src = result 
   let nopara = nopara.thissymbol 
   let newflag = if length.src < 8 * nopara ∧ subseq(src, 1, 2 * nopara)= @(+, topara,"", arithseq(nopara, 1, 1))∧ not("PARAM"_1 in subseq(src, nopara * 2 + 1, length.src))∧ not(mangledname.thissymbol in src)∧ not("SET"_1 in src)
    then"VERYSIMPLE"
    else""
   replace(knownsymbols, changesrc(thissymbol, result + newflag))
  else if code_i in"IDXUC FREF if assertZbuiltinZwordzseq"
  then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 1, result + code_i, thissymbol)
  else if code_i ="WORDS"_1 
  then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 2 + toint(code_(i + 1)), result + subseq(code, i, i + 1 + toint(code_(i + 1))), thissymbol)
  else if code_i in"LIT APPLY RECORD SET PARAM PRECORD"
  then postbind2(org, dict, modpara, templates, knownsymbols, code, i + 2, result + subseq(code, i, i + 1), thissymbol)
  else let z = X(code_i, org, dict, modpara, templates, knownsymbols)
  // assert not("Q3F2ZlibtypezgraphZTzarcZTzarc"_1 in size.z)report [ toword.i]+"LP6"+ code_i + size.z // 
  postbind2(org, dict, modpara, templates, known.z, code, i + 1, result + size.z, thissymbol)

function X(mangledname:word, org:symbol, dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset)zzz 
 let t1 = knownsymbols_mangledname 
  if isdefined.t1 
  then let src = src.t1 
   if src_1 in"record encoding"
   then let down = codedown.mangledname 
    assert length(down_2)= 1 report"inX"+ print2.t1 
    zzz(postbind(dict, mytype(down_2), templates, knownsymbols, src, t1, org), [ mangledname])
   else zzz(knownsymbols, if length.src = 2 ∧ src_1 ="LIT"_1 then src else [ mangledname])
  else let down = codedown.mangledname 
  assert length.down > 1 report"LLLx"+ mangledname 
  let newmodname = replaceT(modpara, mytype(down_2))
  let newmodpara = parameter.newmodname 
  let templatename = abstracttype.newmodname 
  if templatename ="para"_1 
  then zzz(knownsymbols,"PARAM"+ down_2_1)
  else if templatename ="deepcopy"_1 
  then if down_1 ="deepcopy"
   then assert down_3 in ["T"]report"OOO"+ down_3 + print.newmodpara 
    let sym = definedeepcopy(knownsymbols, if down_3 ="T"then newmodpara else mytype(down_3))
    assert mangledname.sym = mangledname report "ERR21"+[ mangledname.sym, mangledname]
    zzz(postbind(dict, mytype."", templates, knownsymbols + sym, src.sym, sym, org), [ mangledname])
   else // Compile options // zzz(knownsymbols, down_1)
  else if templatename ="local"_1 
  then if towords.newmodpara =""
   then zzz(knownsymbols,"LOCAL"+ down_1)
   else if down_1 = [ merge."sizeoftype:T"]
   then if towords.modpara in ["int"]∨ abstracttype.modpara ="seq"_1 
    then zzz(knownsymbols,"LIT 1")
    else let xx = knownsymbols_mangle(merge("typedesc:"+ print.modpara), mytype."internal", empty:seq.mytype)
    if src(xx)_1 in"1 2 3 4 5 6"
    then zzz(knownsymbols,"LIT"+ src(xx)_1)
    else assert false report"did it get here?"+ print2.xx 
    X(merge("sizeoftype:"+ print.modpara), org, dict, modpara, templates, knownsymbols)
   else // Compile options // zzz(knownsymbols, towords.newmodpara)
  else let params = @(+, mytype, empty:seq.mytype, subseq(down, 3, length.down))
  let fullname = mangle(down_1_1, newmodname, params)
  let t2 = knownsymbols_fullname 
  if fullname ≠ mangledname ∧ isdefined.t2 
  then // assert mangledname ="inZwordzseqzseqZTZTzseq"_1 report"ERR13"+ fullname + mangledname // 
   let src = src.t2 
   if src_1 in"sequence record"
   then zzz(postbind(dict, newmodpara, templates, knownsymbols, src, t2, org), [ fullname])
   else zzz(knownsymbols, [ fullname])
  else let f = templates_mangle(down_1_1, mytype("T"+ templatename), params)
  if isdefined.f 
  then let newsymbol = symbol(down_1_1, newmodname, params, replaceT(newmodpara, resulttype.f), src.f)
   let a = postbind(dict, newmodpara, templates, knownsymbols + newsymbol, src.f, newsymbol, org)
   zzz(a, [ fullname])
  else let params2 = @(+, replaceT.modpara, empty:seq.mytype, params)
  let k = lookup(dict, down_1_1, params2)
  assert cardinality.k = 1 report "cannot find template for"+ down_1_1 +"("+ @(seperator.",", print,"", params2)+")while process"+ print.org 
  assert mangledname ≠ mangledname(k_1)report"ERR12"+ mangledname + print2(k_1)
  if not.isdefined(knownsymbols_mangledname(k_1))
  then X(mangledname(k_1), org, dict, mytype."T", templates, knownsymbols)
  else zzz(knownsymbols, [ mangledname(k_1)])

function roots(f:firstpass)seq.word 
 if exportmodule.f then @(+, mangledname,"", toseq.exports.f)else""


function gathersymbols(exported:seq.word, src:seq.seq.word)firstpass 
 let modulename = mytype."test"
  let stubdict = asset.[ symbol("export"_1, modulename, empty:seq.mytype, mytype."internal",""), 
  symbol("unbound"_1, modulename, empty:seq.mytype, mytype."internal",""), 
  symbol("stub"_1, modulename, empty:seq.mytype, mytype."internal",""), 
  symbol("usemangle"_1, modulename, empty:seq.mytype, mytype."internal","")]
  @(wrapgathersymbols(exported, stubdict), identity, firstpass(mytype."?", empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, false), src)

function wrapgathersymbols(exported:seq.word, stubdict:set.symbol, f:firstpass, input:seq.word)firstpass 
 let p = process.gathersymbols(exported, stubdict, f, input)
  assert not.aborted.p report message.p +"FAIL"+ input 
  result.p

function definefld(src:seq.word, modname:mytype, t:seq.mytype, m:mytype)symbol 
 symbol(abstracttype.m, modname, t, parameter.m, src)

function gathersymbols(exported:seq.word, stubdict:set.symbol, f:firstpass, input:seq.word)firstpass 
 // assert print.modname.f in ["?","stdlib","UTF8","altgen"]∨(print.modname.f ="bitpackedseq.T"∧ cardinality.defines.f + cardinality.unbound.f < 8)report print.modname.f + printdict.unbound.f // 
  if input in ["Function sizeoftype T builtin.TYPESIZE", 
  "type encoding", 
  "Function NOINLINE(T)T builtin.NOINLINE", 
  "Function FORCEINLINE(T)T builtin.FORCEINLINE", 
  "Function PROFILE(T)T builtin.PROFILE", 
  "Function TESTOPT(T)T builtin.TESTOPT", 
  "Function deepcopy(T)T builtin.DEEPCOPY"]
  then f 
  else if length.input = 0 
  then f 
  else if input_1 in"use"
  then let t = parse(empty:set.symbol, input)
   firstpass(modname.f, uses.f + mytype.code.t, defines.f, exports.f, unboundexports.f, unbound.f, exportmodule.f)
  else if input_1 in"type"
  then if input in ["type int","type real"]
   then f 
   else let b = parse(empty:set.symbol, input)
   let kind = code(b)_1 
   let t = mytype(towords.parameter.modname.f + [ code(b)_2])
   if kind ="encoding"_1 
   then assert parameter.modname.f = mytype.""report"encoding in template?"
    let typ = parameter(types(b)_1)
    let syms = [ symbol(code(b)_2, modname.f, empty:seq.mytype, mytype(towords.typ +"erecord"), code.b)]
    firstpass(modname.f, uses.f + mytype(towords.typ +"invertedseq")+ mytype(towords.typ +"ipair"), defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, exportmodule.f)
   else assert parameter.modname.f in [ mytype."", mytype."T"]report"KLJKL"
   // assert false report code.b // 
   let modnm = towords.modname.f 
   let code = subseq(code.b, 1, 2)+ toword.length.modnm + modnm + subseq(code.b, 3, length.code.b)
   let sizeofsym = symbol(merge("typedesc:"+ print.t), mytype."internal", empty:seq.mytype, mytype."word seq", code)
   let constructor = symbol(code_2, modname.f, @(+, parameter, empty:seq.mytype, types.b), t, code)
   let syms = @(+, definefld(code, modname.f, [ t]), [ constructor, sizeofsym], types.b)+ if kind ="sequence"_1 
    then [ symbol("toseq"_1, modname.f, [ t], mytype(towords.parameter.t +"seq"_1), code)]
    else empty:seq.symbol 
   firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, exportmodule.f)
  else if input_1 in"Function function"
  then let t = parse(stubdict, getheader.input)
   let name = towords(types(t)_1)_1 
   let n = if iscomplex.modname.f ∧ length.subseq(types.t, 3, length.types.t)= 0 
    then merge([ name]+":"+ print(types(t)_2))
    else name 
    if code.t ="usemangleZtest"
   then let sym = symbol(n, mytype.if iscomplex.modname.f then"T builtin"else"builtin", subseq(types.t, 3, length.types.t), types(t)_2, input)
    firstpass(modname.f, uses.f, defines.f + sym, if input_1 ="Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f, exportmodule.f)
   else let sym = symbol(n, modname.f, subseq(types.t, 3, length.types.t), types(t)_2, input)
   if"exportZtest"= code.t 
   then firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f, exportmodule.f)
   else if"unboundZtest"= code.t 
   then firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + sym, exportmodule.f)
   else firstpass(modname.f, uses.f, defines.f + sym, if input_1 ="Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f, exportmodule.f)
  else if input_1 in"module Module"
  then firstpass(mytype.if length.input > 2 then"T"+ input_2 else [ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f, input_2 in exported)
  else f

function definedeepcopy(knownsymbols:symbolset, type:mytype)symbol 
 let body = if true ∨ abstracttype.type in"encoding int word"
   then"PARAM 1"
   else if abstracttype.type ="seq"_1 
   then let typepara = parameter.type 
    let dc = deepcopymangle.typepara 
    let pseqidx = mangle("_"_1, mytype(towords.typepara +"seq"), [ mytype."T pseq", mytype."int"])
    let cat = mangle("+"_1, type, [ mytype."T seq", mytype."T seq"])
    let blockit = mangle("blockit"_1, mytype(towords.typepara +"blockseq"), [ mytype."T seq"])
    {"LIT 0 LIT 0 RECORD 2 PARAM 1 FREF"+ dc +"FREF"+ cat +"FREF"+ pseqidx +"APPLY 5"+ blockit } 
   else let name = mangle(merge("typedesc:"+ print.type), mytype."internal", empty:seq.mytype)
   assert false report "ERR100"+name+"NO test example for deepcopy"
   let a = knownsymbols_name 
   subfld(src.a, 2, 0, 0)
  symbol("deepcopy"_1, mytype(towords.type +"deepcopy"), [ mytype."T"], type, body)

function subfld(desc:seq.word, i:int, fldno:int, starttype:int)seq.word 
 if i > length.desc 
  then"RECORD"+ toword.fldno 
  else if desc_i ="."_1 
  then subfld(desc, i + 2, fldno, starttype)
  else if desc_i ="seq"_1 
  then subfld(desc, i + 1, fldno, i)
  else if starttype > 0 
  then assert false report"in build deep copy"
   {"PARAM 1 LIT"+ toword.fldno +"IDXUC"+ mangle(merge("deepcopy:"+ subseq(desc, starttype, i - 1)), mytype."deepcopy", empty:seq.mytype)+ subfld(desc, i + 1, fldno + 1, 0)} 
  else"PARAM 1 LIT"+ toword.fldno +"IDXUC"+ subfld(desc, i + 1, fldno + 1, 0)

