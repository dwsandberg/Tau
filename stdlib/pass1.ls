
run mylib test

Module pass1

run main test1

use process.bindinfo

use otherseq.firstpass

use process.firstpass

use seq.firstpass

use set.firstpass

use seq.flddesc

use blockseq.int

use libscope

/use deepcopy.linkage

use seq.mytype

use set.mytype

use parse

use stacktrace

use stdlib

use seq.symbol

use set.symbol

use symbol

/use deepcopy.symbolset

use textio

use seq.typedesc

use seq.seq.seq.word

use seq.seq.word

use set.word

use words

use format

Function replaceTfirstpass(with:mytype, f:firstpass)firstpass
 firstpass(replaceT(with, modname.f), @(+, replaceT.with, empty:seq.mytype, uses.f), 
 asset.@(+, replaceTsymbol.with, empty:seq.symbol, toseq.defines.f), asset.@(+, replaceTsymbol.with, empty:seq.symbol, 
 toseq.exports.f), @(+, replaceTsymbol.with, empty:seq.symbol, unboundexports.f), 
 asset.@(+, replaceTsymbol.with, empty:seq.symbol, toseq.unbound.f), false, rawsrc.f)

function =(a:firstpass, b:firstpass)boolean modname.a = modname.b

Function ?(a:firstpass, b:firstpass)ordering toalphaseq.towords.modname.a ? toalphaseq.towords.modname.b

Function print(b:firstpass)seq.word
 " &br  &br" + print.modname.b + " &br defines" + printdict.defines.b
 + " &br unboundexports"
 + printdict.asset.unboundexports.b

Function find(modset:set.firstpass, name:mytype)set.firstpass
 findelement(firstpass(name, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, false, empty:seq.seq.word)
 , modset)

type linkage is record symset:symbolset, mods:seq.firstpass

Function symset(linkage)symbolset export

Function mods(linkage)seq.firstpass export


Function type:linkage internaltype export

Function pass1(allsrc:seq.seq.seq.word, exports:seq.word, librarysyms:symbolset, librarymods:set.firstpass)linkage
// assert false report print.librarysyms //
 let a = @(+, gathersymbols.exports, librarymods, allsrc)
 let d1 = resolveunboundexports.expanduse.a
 let alltypes = @(+, findtypes.d1, empty:seq.typedesc, toseq.d1)
 let zx = processtypedef(empty:set.symbol, alltypes, 1, empty:seq.typedesc, empty:seq.symbol)
  let d2 = asset.@(+, fixfirstpass.asset.zx, empty:seq.firstpass, toseq.d1)
  let simple = @(+, findsimple, empty:seq.firstpass, toseq.d2)
  let abstractmods = @(+, templates.d2, empty:seq.firstpass, toseq.d2)
  let templates = @(clean, identity, emptysymbolset, toseq.@(∪, defines, empty:set.symbol, abstractmods))
  let knownsymbols1 = @(+, identity, librarysyms, toseq.@(∪, defines, empty:set.symbol, simple))
  let knownsymbols = @(filtersym, identity, knownsymbols1, zx)
  let X = @(bind(templates, d2), identity, knownsymbols, simple)
    assert cardinality(asset.toseq.X &cap asset.toseq.templates)=0 report "CHECK"+toword.cardinality(asset.toseq.X &cap asset.toseq.templates)
    linkage(@(+,identity,X,toseq.templates), sort(simple + abstractmods))


function   filtersym(st:symbolset,s:symbol) symbolset 
      let newpara=@(+, replaceT.parameter.modname.s, empty:seq.mytype, paratypes.s)
    let newsymbol=symbol( name.s
        ,modname.s,newpara,replaceT(parameter.modname.s,resulttype.s),src.s)
       let a= mapsymbol(st, mangledname.s ,newsymbol )
              mapsymbol(a,mangledname.newsymbol,newsymbol)

function processtypedef(defined:set.symbol, undefined:seq.typedesc, i:int, newundefined:seq.typedesc, other:seq.symbol)seq.symbol
 if i > length.undefined then
 if length.newundefined = 0 then other
  else
    assert length.undefined > length.newundefined 
    report"ProBLEM" + @(seperator." &br", print2,"", @(+, s, empty:seq.symbol, newundefined))
    processtypedef(defined, newundefined, 1, empty:seq.typedesc, other)
 else if kind.undefined_i = "defined"_1 then
 processtypedef(defined + s.undefined_i, undefined, i + 1, newundefined, other)
 else
  let td = undefined_i
  let x = nametotype.name.s.td
  let k2 = subflddefined(flds.td, parameter.x, 1, defined, empty:seq.flddesc)
   if length.k2 = 0 then processtypedef(defined, undefined, i + 1, newundefined + undefined_i, other)
   else
    let modname = modname.s.td
    let ptype = [ mytype.if parameter.modname = mytype.""then [ name.td]else"T" + name.td]
    let syms = definestructure(kind.td, k2, 1, ptype, modname, if kind.td in "sequence"then 1 else 0, empty:seq.mytype,"","", empty:seq.symbol)
     processtypedef(defined + last.syms, undefined, i + 1, newundefined, other + syms)

type flddesc is record desc:seq.word, combined:mytype

function fldname(t:flddesc)word abstracttype.combined.t

function fldtype(t:flddesc)mytype parameter.combined.t

function subflddefined(s:seq.flddesc, T:mytype, i:int, defined:set.symbol, result:seq.flddesc)seq.flddesc
 // check to see all flds of type are defined. //
 if i > length.s then result
 else
  let next = s_i
  let t = towords.fldtype.next
  let typ = if t_1 = "T"_1 then mytype(towords.T + subseq(t, 2, length.t))
  else fldtype.next
   if abstracttype.typ in "word int seq"then
   subflddefined(s, T, i + 1, defined, result + flddesc("1" + print.typ, combined.next))
   else
    let sym = lookup(defined, merge("type:" + print.typ), empty:seq.mytype)
     if cardinality.sym = 0 ∨ (src.sym_1)_1 ≠ "WORDS"_1 then
     empty:seq.flddesc
     else
      let src = src.sym_1
       subflddefined(s, T, i + 1, defined, result + flddesc(subseq(src, 3, 2 + toint.src_2), combined.next))

function nametotype(w:word)mytype
 let t = towords.decodeword.w
  mytype.@(+,_(t),"", arithseq(length.t / 2, -2, length.t))

function fixfirstpass(new:set.symbol, f:firstpass)firstpass
 let newdefines = replace(defines.f, new)
  assert cardinality.newdefines = cardinality.defines.f report"oops 2" + toword.cardinality.newdefines + toword.cardinality.defines.f
   // + @(+, print,"", toseq.newdefines)+ @(+, print,"/", toseq.defines.f)//
   let newexports = replace(exports.f, new)
    assert cardinality.newexports = cardinality.exports.f report"oops 3"
     // assert modname.f &ne mytype."stdlib"report let ttt = lookup(commonexports,"char"_1, [ mytype."int"])if length.toseq.ttt = 1 then print2.ttt_1 else"notfound"//
     firstpass(modname.f, uses.f, newdefines, newexports, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)

type typedesc is record s:symbol, kind:word, name:word, flds:seq.flddesc

function cvty(t:flddesc)seq.word
 [ toword.length.towords.combined.t] + towords.combined.t
 + if desc.t = ""then""else desc.t + "/"

function findtypes(dict:set.symbol, s:symbol)seq.typedesc
 if resulttype.s = mytype."internaltype"then
 if(src.s)_1 in "WORDS"then
  [ typedesc(s,"defined"_1,"defined"_1, empty:seq.flddesc)]
  else
   assert(src.s)_1 in "type"report"NNN" + print2.s
   let b = parse(dict, src.s)
   let kind =(code.b)_1
   let name =(code.b)_2
    [ typedesc(s, kind, name, @(+, flddesc."", empty:seq.flddesc, types.b))]
 else empty:seq.typedesc

function findtypes(modset:set.firstpass, f:firstpass)seq.typedesc
 if"T"_1 in towords.modname.f then empty:seq.typedesc
 else
  let dict = builddict(modset, f)
   @(+, findtypes(dict), empty:seq.typedesc, toseq.defines.f)

function clean(b:symbolset, s:symbol)symbolset
 if length.src.s > 0 ∧ (src.s)_1 = "parsedfunc"_1 then
 b + changesrc(s, subseq(src.s, toint.(src.s)_2 + 3, length.src.s))
 else if(src.s)_1 = "STUB"_1 then b else b + s

function recordsize(src:seq.word, i:int)int
 // bug if made tail recursive ? //
 if i > length.src then 0
 else if i = 1 ∧ src_i = "FREF"_1 then
 recordsize(src, i + 2) + 1
  else if src_i = "LOCAL"_1 then recordsize(src, i + 2) + 1
 else if src_i = "LIT"_1 then recordsize(src, i + 3)else 10000

function removeflat(p:word, i:int)seq.word
 if i = -1 then""
 else
  removeflat(p, i - 1) + "LOCAL" + p + "LIT" + toword.i
  + "IDXUC"

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
  if isempty.e then empty:set.symbol else exports.find(modset, use)_1

function builddict(modset:set.firstpass, f:firstpass)set.symbol @(∪, builddict.modset, defines.f ∪ unbound.f, uses.f)

function bindunboundexports(modset:set.firstpass, f:firstpass)set.firstpass
 if length.unboundexports.f = 0 then modset
 else
  let dict = builddict(modset, f)
  let new = @(resolveexport.dict, identity, firstpass(modname.f, uses.f, defines.f, exports.f, empty:seq.symbol, unbound.f, exportmodule.f, rawsrc.f), unboundexports.f)
   replace(modset, new)

function resolveexport(dict:set.symbol, f:firstpass, s:symbol)firstpass
 let x = findelement2(dict, s)
  if cardinality.x = 1 then
  assert resulttype.x_1 = resulttype.s report"export return type missmatch" + print.s + print.x_1
    firstpass(modname.f, uses.f, defines.f, exports.f ∪ x, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
  else
   firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + s, unbound.f, exportmodule.f, rawsrc.f)

function expanduse(modset:set.firstpass)set.firstpass
 let newset = @(expanduse2, identity, modset, toseq.asset.@(+, uses, empty:seq.mytype, toseq.modset))
  if cardinality.newset > cardinality.modset then expanduse.newset else modset

function expanduse2(modset:set.firstpass, use:mytype)set.firstpass
 let x = find(modset, use)
  if iscomplex.use ∧ not(parameter.use = mytype."T")then
  if isempty.x then
   let template = find(modset, mytype("T" + abstracttype.use))
     assert not.isempty.template report"Cannot find module" + print.use
     + @(+, print,"", @(+, modname, empty:seq.mytype, toseq.modset))
      modset + replaceTfirstpass(parameter.use, template_1)
   else modset
  else
   assert not.isempty.x report"Cannot find module" + print.use
   + @(+, print,"", @(+, modname, empty:seq.mytype, toseq.modset))
    modset

function hasunbound(f:firstpass)seq.firstpass if length.unboundexports.f = 0 then empty:seq.firstpass else [ f]

function totalunbound(f:firstpass)int length.unboundexports.f

function findsimple(f:firstpass)seq.firstpass
 if length.towords.modname.f = 1 ∧ length.uses.f > 0 then [ f]
 else empty:seq.firstpass

function templates(modset:set.firstpass, f:firstpass)seq.firstpass
 if parameter.modname.f = mytype."T"then
 if length.uses.f > 0 then
  let newdefines = @(+, template(builddict(modset, f) ∪ headdict), empty:seq.symbol, toseq.defines.f)
    [ firstpass(modname.f, uses.f, asset.newdefines, exports.f, empty:seq.symbol, empty:set.symbol, exportmodule.f, rawsrc.f)]
  else [ f]
 else empty:seq.firstpass

function template(dict:set.symbol, s:symbol)seq.symbol
 if(src.s)_1 in "STUB"then empty:seq.symbol
 else if(src.s)_1 in "Function function"then
 let b = parse(bindinfo(dict,"", empty:seq.mytype), src.s)
   [ changesrc(s, code.b)]
 else [ s]

function bind(templates:symbolset, modset:set.firstpass, a:symbolset, f:firstpass)symbolset
 let x = subseq(towords.modname.f, 1, length.towords.modname.f - 1)
 let dict = builddict(modset, f) ∪ headdict
  if x = ""then
  let b = @(x2(templates, dict), identity, a, toseq.exports.f)
    @(bind2(templates, dict), identity, b, toseq.defines.f)
  else
   assert x = "T"report"internal error bind"
    @(bind2(templates, dict), identity, a, toseq.defines.f)

function x2(templates:symbolset, dict:set.symbol, knownsymbols:symbolset, s:symbol)symbolset
 if iscomplex.modname.s then known.X(mangledname.s, s, dict, parameter.modname.s, templates, knownsymbols)else knownsymbols

function bind2(templates:symbolset, dict:set.symbol, knownsymbols:symbolset, s:symbol)symbolset
  //          assert not(mangledname.s in "emptyQ513AseqQ512ETQ5AwordQ7AseqZwordzseq") report "JKL" // 
 let symsrc = src.s
  if symsrc_1 = "FREF"_1 then postbind(dict, mytype."", templates, knownsymbols, symsrc, s, s)
  else if // length.symsrc = 2 &and //   symsrc_1 = "WORDS"_1 &or symsrc_1 = "LOCAL"_1 then
  knownsymbols
  else
   assert symsrc_1 in "Function function"report"internal error bind" + symsrc
   let b = parse(bindinfo(dict,"", empty:seq.mytype), symsrc)
   let code = bodyonly.code.b
    postbind(dict, mytype."", templates, knownsymbols, code.b, s, s)

resultpair type is needed because calculation often involve adding new known symbols.

type resultpair is record known:symbolset, size:seq.word

function definestructure(kind:word, flds:seq.flddesc, i:int, ptype:seq.mytype, modname:mytype, offset:int, paras:seq.mytype, constructor:seq.word, desc:seq.word, symbols:seq.symbol)seq.symbol
 if i > length.flds then
 if kind = "sequence"_1 then
  let mn = mangle("_"_1, modname, ptype + mytype."int")
   let consrc ="FREF" + mn + constructor + "RECORD"
   + toword.recordsize("FREF" + mn + constructor, 1)
   let con = symbol(abstracttype.ptype_1, modname, paras, mytype(towords.parameter.modname + abstracttype.ptype_1), consrc)
   let seqtype=mytype(towords.parameter.modname + "seq"_1)
   let symtoseq = symbol("toseq"_1, modname, ptype, seqtype,"LOCAL 1")
   let symfromseq=symbol(merge("to:"+print.ptype_1),modname,[seqtype],ptype_1,
    "LOCAL 1 LIT 0 IDXUC FREF" + mn + "Q3DZbuiltinZintZint LIT 2 LIT 3 BR 3 LOCAL 1 EXITBLOCK 1 LIT 0 LIT 0 RECORD 2 EXITBLOCK 1 
   BLOCK 3")
   let t ="1 seq." + print.parameter.modname
   let descsym = symbol(merge("type:" + print.resulttype.con), modname, empty:seq.mytype, mytype."internaltype","WORDS" + toword.length.t + t)
    symbols + symtoseq + symfromseq+ con + descsym
  else
   let consrc = if length.paras = 1 then"LOCAL 1"else constructor + "RECORD" + toword.recordsize(constructor, 1)
   let con = symbol(abstracttype.ptype_1, modname, paras, mytype(towords.parameter.modname + abstracttype.ptype_1), consrc)
   let descsym = symbol(merge("type:" + print.resulttype.con), modname, empty:seq.mytype, mytype."internaltype","WORDS" + toword(length.desc + 1) + toword.offset + desc)
    symbols + con + descsym
 else
  let fldtype = fldtype.flds_i
  let fldname = fldname.flds_i
  let tsize = toint.(desc.flds_i)_1
  let newoffset = if offset = 0 then tsize else offset + tsize
  let fldsrc = if offset = 0 ∧ i + 1 > length.flds then"LOCAL 1"
  else if tsize = 1 then"LOCAL 1 LIT" + toword.offset + "IDXUC"
  else
   // should use a GEP instruction //
   //"LOCAL 1 LIT"+ toword.offset +"LIT"+ toword.tsize +"castZbuiltinZTzseqZintZint"//"LOCAL 1 LIT"
   + toword(8 * offset)
   + "Q2BZbuiltinZintZint"
  let fldsym = symbol(fldname, modname, ptype, fldtype, fldsrc)
  let confld = if tsize = 1 then"LOCAL" + toword(length.paras + 1)
  else removeflat(toword(length.paras + 1), tsize - 1)
   definestructure(kind, flds, i + 1, ptype, modname, newoffset, paras + fldtype, constructor + confld, desc + subseq(desc.flds_i, 2, length.desc.flds_i), symbols + fldsym)

function topara(i:int)seq.word"LOCAL" + toword.i

function postbind(dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset, code:seq.word, thissymbol:symbol, org:symbol)symbolset
 let i = if code_1 = "parsedfunc"_1 then 3 + toint.code_2 else 1
 let result = if i = 1 then""else subseq(code, 1, i - 1)
  if code_i = "WORDS"_1 then
  let l = toint.code_(i + 1) + 2 + i
    if l ≤ length.code ∧ code_l = "builtinZinternal1Zwordzseq"_1 then
    replace(knownsymbols, changesrc(thissymbol, result + subseq(code, i + 2, length.code)))
    else postbind2(org, dict, modpara, templates, knownsymbols, code, l, result + subseq(code, i, l - 1), thissymbol)
  else if code_i in "usemangleZinternal1"then
  let builtinname = mangle(name.thissymbol, mytype."builtin", paratypes.thissymbol)
   let src = @(+, topara,"", arithseq(length.paratypes.thissymbol, 1, 1)) + builtinname
      changesrc(knownsymbols,thissymbol, result + src + subseq(code, i + 1, length.code)) 
  else if code_i in "FROMSEQ51Zinternal1"then
  let mn = mangle("_"_1, modname.thissymbol, [ mytype("T" + abstracttype.resulttype.thissymbol), mytype."int"])
   let newknown = known.X(mn, org, dict, modpara, templates, knownsymbols)
   let f1 ="LOCAL 1 LIT 0 IDXUC FREF" + mn + "Q3DZbuiltinZintZint LIT 2 LIT 3 BR 3 LOCAL 1 EXITBLOCK 1 LIT 0 LIT 0 RECORD 2 EXITBLOCK 1 
   BLOCK 3"
    replace(newknown, changesrc(thissymbol, result + f1 + subseq(code, i + 1, length.code)))
  else postbind2(org, dict, modpara, templates, knownsymbols, code, i, result, thissymbol)

function changesrc(knownsymbols:symbolset, s:symbol,code:seq.word) symbolset
  // assert not(    towords.modname.s="int seq encoding" &and  name.s in  "add") 
    &or mangledname.s in "addZintzseqzencodingZTzencodingstateZTzencodingrep  
                       addZintzseqzencodingZTzencodingstateZTzencodingrepzseq" report "X"+ mangledname.s  //
  if   isinstance.modname.s then 
         let newpara=@(+, replaceT.parameter.modname.s, empty:seq.mytype, paratypes.s)
      let new=symbol(name.s,modname.s,newpara,replaceT(parameter.modname.s,resulttype.s),code) 
       let t=mapsymbol(knownsymbols,mangledname.s, new)
          mapsymbol(t,mangledname.new, new)  
    else  mapsymbol(knownsymbols,mangledname.s, changesrc(s, code))
     

function postbind2(org:symbol, dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset, code:seq.word, i:int, result:seq.word, thissymbol:symbol)symbolset
  if i > length.code then  
   let t=changesrc( knownsymbols,thissymbol,result)
  //  assert not(mangledname.thissymbol  in "test2Ztest2 " )report "HJK"+
        src.thissymbol  +"&br"+code //
   t
 else if code_i in "IDXUC FREF if assertZbuiltinZwordzseq NOINLINE TESTOPT optionZbuiltinZTZwordzseq "then
 postbind2(org, dict, modpara, templates, knownsymbols, code, i + 1, result + code_i, thissymbol)
 else if code_i = "WORDS"_1 then
 let l = toint.code_(i + 1) + 2
   postbind2(org, dict, modpara, templates, knownsymbols, code, i + l, result + subseq(code, i, i + l - 1), thissymbol)
 else if code_i = "COMMENT"_1 then
 postbind2(org, dict, modpara, templates, knownsymbols, code, i + 2 + toint.code_(i + 1), result + subseq(code, i, i + 1 + toint.code_(i + 1)), thissymbol)
 else if code_i in "LIT APPLY RECORD SET WORD DEFINE EXITBLOCK BLOCK BR LOCAL"then
 postbind2(org, dict, modpara, templates, knownsymbols, code, i + 2, result + subseq(code, i, i + 1), thissymbol)
 else
  let z = X(code_i, org, dict, modpara, templates, knownsymbols)
   postbind2(org, dict, modpara, templates, known.z, code, i + 1, result + size.z, thissymbol)

function checkforindex(t1:symbol, org:symbol, dict:set.symbol, templates:symbolset, knownsymbols:symbolset)symbolset
 let src = src.t1
  if length.src=0 &or not(src_1 = "FREF"_1) ∨ abstracttype.resulttype.t1 = "erecord"_1 then
  knownsymbols
  else known.X(src_2, org, dict, parameter.modname.t1, templates, knownsymbols)
  
function X(mangledname:word, org:symbol, dict:set.symbol, modpara:mytype, templates:symbolset, knownsymbols:symbolset)resultpair
 let t1 = lookupsymbol(knownsymbols, mangledname)
  if isdefined.t1 then resultpair(checkforindex(t1, org, dict, templates, knownsymbols), [ mangledname.t1])
  else
   let down = codedown.mangledname
    assert length.down > 1 report"LLLx" + mangledname + print.org
    let newmodname = replaceT(modpara, mytype.down_2)
    let newmodpara = parameter.newmodname
    let templatename = abstracttype.newmodname
     if templatename in "para local"then resultpair(knownsymbols, [ mangledname])
     else if templatename = "deepcopy"_1 then
     if down_1 = "deepcopy"then
      definedeepcopy(dict, templates, knownsymbols, if down_3 = "T"then newmodpara else mytype.down_3, org)
      else if down_1 = [ merge."sizeoftype:T"]then
      let z = if print.newmodpara = "int"then"1"
       else
        let xx = lookup(dict, merge("type:" + print.newmodpara), empty:seq.mytype)
         assert cardinality.xx = 1 ∧ (src.xx_1)_1 = "WORDS"_1 report"can not find type sizeof" + print.newmodpara + print.org
          subseq(src.xx_1, 3, length.src.xx_1)
       let newsym = symbol(down_1_1, newmodname, empty:seq.mytype, mytype."int","LIT" + z_1)
        resultpair(replace(knownsymbols, newsym), [ mangledname.newsym])
      else // Compile options // resultpair(knownsymbols, down_1)
     else
      let params = @(+, mytype, empty:seq.mytype, subseq(down, 3, length.down))
       let fullname = mangle(down_1_1, newmodname, params)
      let t2 = lookupsymbol(knownsymbols, fullname)
       if fullname ≠ mangledname ∧ isdefined.t2 then 
           resultpair(checkforindex(t2, org, dict, templates, knownsymbols), [ mangledname.t2])
       else
        let f = lookupsymbol(templates, mangle(down_1_1, mytype("T" + templatename), params))
         if isdefined.f then
         let newsymbol = symbol(down_1_1, newmodname, params, replaceT(newmodpara, resulttype.f), src.f)
          let newknown = 
            checkforindex(newsymbol, org, dict, templates, knownsymbols) + newsymbol
           let t44= postbind(dict, newmodpara, templates, newknown, src.f, newsymbol, org)
              resultpair(t44, [ mangledname.lookupsymbol(t44,fullname)])
         else
           let params2= @(+, replaceT.modpara, empty:seq.mytype, params) 
           let k = lookup(dict, replaceTinname(newmodpara, down_1_1), params2)
         // case for examples like frombits:T(bits)T which needs to find frombits:bit(bits)bit //
          assert cardinality.k = 1 report"cannot find template for" + down_1_1 + "("
           + @(seperator.",", print,"", params2)
           + ")while process"
           + print.org
           + "templatename"
           + templatename
           + mangledname
           + fullname
           + "newmodpara:"
           + print.newmodpara
           + toword.cardinality.k
              + @(+, print,"", toseq.templates) 
            assert mangledname ≠ mangledname.k_1 report"ERR12" + mangledname + print2.k_1
             if not.isdefined.lookupsymbol(knownsymbols, mangledname.k_1)then
             X(mangledname.k_1, org, dict, mytype."T", templates, knownsymbols)
             else resultpair(knownsymbols, [ mangledname.k_1])


Function headdict set.symbol
let modulename = mytype."internal1"
 asset
 .[ symbol("builtin"_1, modulename, [ mytype."internal1"], mytype."internal",""), symbol("builtin"_1, modulename, [ mytype."word seq"], mytype."internal",""), symbol("STATE"_1, modulename, [ mytype."internal1"], mytype."internal1",""), symbol("FROMSEQ"_1, modulename, empty:seq.mytype, mytype."internal1",""), symbol("export"_1, modulename, empty:seq.mytype, mytype."internal1",""), symbol("unbound"_1, modulename, empty:seq.mytype, mytype."internal1",""), symbol("stub"_1, modulename, empty:seq.mytype, mytype."internal1",""), symbol("usemangle"_1, modulename, empty:seq.mytype, mytype."internal1","")]

function gathersymbols(exported:seq.word, src:seq.seq.word)firstpass
 @(wrapgathersymbols(exported, headdict)
 , identity
 , firstpass(mytype."?", empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol, false, src)
 , src)

function wrapgathersymbols(exported:seq.word, stubdict:set.symbol, f:firstpass, input:seq.word)firstpass gathersymbols(exported, stubdict, f, input)

function definefld(src:seq.word, modname:mytype, t:seq.mytype, m:mytype)symbol 
symbol(abstracttype.m, modname, t, parameter.m, src)

function hasT(s:seq.word, i:int)boolean
 // used to determine it type T is specified somewhere in function sig //
 if s_(i + 1) in ":."then
 // s_i is name // hasT(s, i + 2)
 else
  // at end of type //
  if s_i = "T"_1 then true
  else if s_(i + 1) in ",("then hasT(s, i + 2)
  else // at end of parameter list or beginning of function type // false

Function bodyonly(code:seq.word)seq.word
 if code_1 = "parsedfunc"_1 then subseq(code, 3 + toint.code_2, length.code)else code

function gathersymbols(exported:seq.word, stubdict:set.symbol, f:firstpass, input:seq.word)firstpass
 // assert print.modname.f in ["?","stdlib","UTF8","altgen"]∨(print.modname.f ="bitpackedseq.T"∧ cardinality.defines.f + cardinality.unbound.f < 8)report print.modname.f + printdict.unbound.f //
 if length.input = 0 then f
 else if input_1 in "use"then
 let t = parse(empty:set.symbol, subseq(input, 2, length.input))
   firstpass(modname.f, uses.f + mytype.code.t, defines.f, exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
 else if input_1 in "type"then
 let b = parse(empty:set.symbol, input)
  let kind =(code.b)_1
  let name =(code.b)_2
  let t = mytype(towords.parameter.modname.f + name)
   if kind in "encoding"then
   assert parameter.modname.f = mytype.""report"encoding in template?"
    let typ = parameter.(types.b)_1
    let adde = mangle("add"_1, mytype(towords.typ + "encoding"), [ mytype."T encodingstate", mytype."T encodingrep"])
    let code =("FREF" + adde + if name = "wordencoding"_1 then"LIT 1"else"LIT 0")
    + "WORD"
    + merge([ name] + print.modname.f)
     + // "RECORD 3 NOINLINE" //
      "RECORD 3 WORDS 2 NOINLINE STATE optionZbuiltinZTZwordzseq"   
    let sym = symbol(name, modname.f, empty:seq.mytype, mytype(towords.typ + "erecord"), code)
     firstpass(modname.f, uses.f + mytype(towords.typ + "encoding"), defines.f + sym, exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
   else
    assert parameter.modname.f in [ mytype."", mytype."T"]report"KLJKL"
    let sizeofsym = symbol(merge("type:" + print.t), modname.f, empty:seq.mytype, mytype."internaltype", input)
    let constructor = symbol(name, modname.f, @(+, parameter, empty:seq.mytype, types.b), t,"STUB")
    let syms = @(+, definefld("STUB", modname.f, [ t]), [ constructor, sizeofsym], types.b)
    + if kind = "sequence"_1 then
      let seqtype=mytype(towords.parameter.t + "seq"_1)
    [ symbol("toseq"_1, modname.f, [ t], seqtype,"STUB"),
       symbol(merge("to:"+print.t), modname.f, [ seqtype],t ,"STUB")
    ]
    else empty:seq.symbol
     firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
 else if input_1 in "Function function"then
 let t = parse(stubdict, getheader.input)
  let code = bodyonly.code.t
  let name = funcname.t
  let paratypes = funcparametertypes.t
   assert iscomplex.modname.f = hasT(input, 2)report"Must use type T in function name or parameters in parameterized module and T cannot be used in non - parameterized module" + getheader.input
   let firstinstruction = code_1
    if firstinstruction in "usemangleZinternal1"then
    let sym = symbol(name, mytype.if iscomplex.modname.f then"T builtin"else"builtin", paratypes, funcreturntype.t, input)
      firstpass(modname.f, uses.f, defines.f + sym, if input_1 = "Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
    else
     let sym = symbol(name, modname.f, paratypes, funcreturntype.t, input)
      if firstinstruction in "exportZinternal1"then
      firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f, exportmodule.f, rawsrc.f)
      else if firstinstruction in "unboundZinternal1"then
      firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + sym, exportmodule.f, rawsrc.f)
      else
       assert not(sym in defines.f)report"Function" + name.sym + "is defined twice in module" + print.modname.f
        firstpass(modname.f, uses.f, defines.f + sym, if input_1 = "Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
 else if input_1 in "module Module"then
 firstpass(mytype.if length.input > 2 then"T" + input_2 else [ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f, input_2 in exported, rawsrc.f)
 else f

function definedeepcopy(dict:set.symbol, templates:symbolset, knownsymbols:symbolset, type:mytype, org:symbol)resultpair
 // assert towords.type in ["int seq","int","word3","stat5","word seq","llvmtypeele","word","llvmconst","const3","inst","flddesc seq","match5","flddesc","templatepart seq","templatepart","internalbc","persistant"]report"definedeepcopy"+ towords.type //
 let body = if abstracttype.type in "encoding int word"then resultpair(knownsymbols,"LOCAL 1")
 else
  // assert length.print.type = 1 &or print.type in ["match5","seq.int","llvmconst","match5","inst","libsym","llvmtypeele","word3","const3","seq.word","stat5","seq.flddesc","flddesc","seq.templatepart","templatepart","set.mod2desc"]report"DDD"+ print.type //
  if abstracttype.type = "seq"_1 then
  let typepara = parameter.type
   let dc = deepcopymangle.typepara
   let pseqidx = mangle("_"_1, type, [ mytype."T pseq", mytype."int"])
   let cat = mangle("+"_1, type, [ mytype."T seq", mytype."T"])
   let blockittype = if abstracttype.parameter.type in "seq word char int"then mytype."int blockseq"
   else mytype(towords.type + "blockseq")
   let blockit = mangle("blockit"_1, blockittype, [ mytype."T seq"])
    resultpair(knownsymbols,"LIT 0 LIT 0 RECORD 2 LOCAL 1 FREF" + dc + "FREF" + cat + "FREF"
    + pseqidx
    + "APPLY 5"
    + blockit)
  else
   let xx = lookup(dict, merge("type:" + print.type), empty:seq.mytype)
    assert cardinality.xx = 1 ∧ (src.xx_1)_1 = "WORDS"_1 report"can not find type deepcopy" + print.type + print.org
    let z = subseq(src.xx_1, 3, toint.(src.xx_1)_2 + 2)
    let y = subfld(z, 2, 0, 2)
     resultpair(knownsymbols
     , if last.y = "1"_1 then
     // only one element in record so type is not represent by actual record //"LOCAL 1"
      + subseq(y, 6, length.y - 2)
     else
      assert z_1 ≠ "1"_1 report"Err99a"
       y)
 let sym = symbol("deepcopy"_1, mytype(towords.type + "deepcopy"), [ mytype."T"], type, size.body)
    let t44= postbind(dict, mytype."", templates, known.body + sym, src.sym, sym, org)
              resultpair(t44, [ mangledname.lookupsymbol(t44,mangledname.sym)])

function subfld(desc:seq.word, i:int, fldno:int, starttype:int)seq.word
 if i > length.desc then"RECORD" + toword.fldno
 else if i < length.desc ∧ desc_(i + 1) = "."_1 then
 subfld(desc, i + 2, fldno, starttype)
 else
  let fldtype = mytype.@(+,_.desc,"", arithseq((i - starttype + 2) / 2, -2, i))
   {(if abstracttype.fldtype in "encoding int word"then"LOCAL 1 LIT" + toword.fldno + "IDXUC"
   else
    assert abstracttype.fldtype = "seq"_1 report"ERR99" + desc
     "LOCAL 1 LIT" + toword.fldno + "IDXUC" + deepcopymangle.fldtype)
   + subfld(desc, i + 1, fldno + 1, i + 1)}