#!/usr/local/bin/tau

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


use seq.mytype

use set.mytype

use parse

use stacktrace

use stdlib

use seq.symbol

use set.symbol

use symbol

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

type linkage is record symset:symbolset, mods:seq.firstpass, result:seq.symbol

Function symset(linkage)symbolset export

Function mods(linkage)seq.firstpass export

function result (linkage)seq.symbol export


Function type:linkage internaltype export

Function pass1(allsrc:seq.seq.seq.word, exports:seq.word, librarysyms:symbolset, librarymods:set.firstpass)linkage
// assert false report print.librarysyms //
 let a = @(+, gathersymbols.exports, librarymods, allsrc)
 let d1 = resolveunboundexports.expanduse.a
 let alltypes = @(+, findtypes.d1, empty:seq.typedesc, toseq.d1)
 let zx = processtypedef(empty:set.symbol, alltypes, 1, empty:seq.typedesc, empty:seq.symbol)
// assert false report @(+,mangledname,"",zx) //
  let d2 = asset.@(+, fixfirstpass.asset.zx, empty:seq.firstpass, toseq.d1)
  let simple = @(+, findsimple, empty:seq.firstpass, toseq.d2)
  let c=      @(+, bind3(d2),empty:seq.symbol,simple)
  let abstractmods = @(+, templates.d2, empty:seq.firstpass, toseq.d2)
  let parsedabstract=@(∪, defines, empty:set.symbol, abstractmods)
  let abstractmods2=@(+, fixfirstpass.parsedabstract, empty:seq.firstpass, abstractmods)
  let templates = @(+, identity, emptysymbolset, toseq.parsedabstract)
   let allsymbols=@(&cup,      defines,empty:set.symbol, toseq.d2)
  let templatemap=@( maptemp.templates,identity,templates,toseq.allsymbols)
  // assert false report "XX"+ @(+,mangledname,"",toseq.templatemap) //
  let source1=@(replace,identity,librarysyms,c)
  let source=@(fldchanges,identity,source1,zx)
   let aa=@(+,mangledname,"",toseq.@(∪, exports, empty:set.symbol, simple))
  let root= symbol("Wroot"_1, mytype."W",   empty:seq.mytype  , mytype."int", empty:seq.sig,aa)
    let result=postbind(templatemap,allsymbols,replace(source,root) ,empty:set.word,"WrootZW",1,empty:seq.symbol)
    let X=  @(replace,identity,emptysymbolset,result)
     assert cardinality(asset.toseq.X &cap asset.toseq.templates)=0 report 
    "CHECK pass1"+@(+,mangledname,"",toseq.(asset.toseq.X &cap asset.toseq.templates))
    linkage(@(+,identity,X,toseq.templates), sort(simple + abstractmods2),  result
 )

   function  maptemp(templates:symbolset,st:symbolset,  s:symbol) symbolset
            if src.s="STUB" &or ( template.s="none"_1  )  then st else 
                  let s2=lookupsymbol(templates,template.s)
                 assert isdefined.s2 report "maptemp function:"+print2.s
                  mapsymbol(st,mangledname.s, changesrc(s, src.s2))
                
    
    
  /function  maptemp(templates:set.symbol,st:symbolset,  s:symbol) symbolset
            if src.s="STUB" &or ( template.s="none"_1 &and not(parameter.modname.s=mytype."T") )  then st else 
             let mn=if template.s="none"_1   then mangledname.s else template.s
                 let s2=lookup(templates,mn) 
                 assert cardinality.s2=1 report  "maptemp function"+ mn
                  mapsymbol(st,mangledname.s, changesrc(s, src.s2_1))
                 

function fldchanges(st:symbolset,s:symbol) symbolset
if (towords.modname.s)_1 ="T"_1 &or length.towords.modname.s=0 then st else
   let newparams=  @(+,replaceT(parameter.modname.s),empty:seq.mytype,paratypes.s)
   let sym=symbol(name.s, modname.s,   newparams  , replaceT(parameter.modname.s,resulttype.s), code.s,src.s)
    mapsymbol(st, mangledname.sym ,sym )


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
    let syms = definestructure(kind.td, k2, 1, ptype, modname, if kind.td in "sequence"then 1 else 0, 
    empty:seq.mytype,empty:seq.sig,"", empty:seq.symbol)
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

  
function removeflat2(p:int, i:int)seq.sig
 if i = -1 then empty:seq.sig
 else
  removeflat2(p, i - 1) + [local.p ,lit.i, IDXUC]

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
    if   (code.b)_1 = "parsedfunc"_1 then
   [ changesrc(s, subseq(code.b, toint.(code.b)_2 + 3, length.code.b))]
   else 
   [ changesrc(s, code.b)]
 else [ s]

    
 function bind3( modset:set.firstpass,   f:firstpass) seq.symbol
   let dict = builddict(modset, f) ∪ headdict
    @(+,bind2.dict,empty:seq.symbol,   toseq.defines.f)
   
function bind2( dict:set.symbol,s:symbol) symbol
let symsrc = src.s
  let code=if length.symsrc > 0 &and symsrc_1 in "Function function" then
  let b = parse(bindinfo(dict,"", empty:seq.mytype), symsrc)
    bodyonly.code.b
   else
      symsrc 
    changesrc(s,code)
    
    
 

    



function definestructure(kind:word, flds:seq.flddesc, i:int, ptype:seq.mytype, modname:mytype, offset:int, 
paras:seq.mytype, constructor2:seq.sig, desc:seq.word, symbols:seq.symbol)seq.symbol
 if i > length.flds then
 if kind = "sequence"_1 then
   let constructor=cvt(constructor2,1,"")   
  let mn = mangle("_"_1, modname, [mytype(towords.parameter.modname + abstracttype.ptype_1), mytype."int"])
    let indexfunc= sig("_", [mytype(towords.parameter.modname + abstracttype.ptype_1), mytype."int"], modname, empty:seq.sig,parameter.modname) 
   // assert false report print.[indexfunc] +returntype.decode.indexfunc //
   let consrc ="FREF" + mn + constructor + "RECORD" + toword.countflds(constructor2,1,1)
   let consrc2=[FREFsig.indexfunc]+constructor2+RECORD.countflds(constructor2,1,1)
    let con = symbol(abstracttype.ptype_1, modname, paras, mytype(towords.parameter.modname + abstracttype.ptype_1), empty:seq.sig,consrc)
   let seqtype=mytype(towords.parameter.modname + "seq"_1)
   let symtoseq = symbol("toseq"_1, modname, ptype, seqtype,[local1],"")
   let symfromseq=symbol(merge("to:"+print.ptype_1),modname,[seqtype],ptype_1,
    "LOCAL 1 LIT 0 IDXUC FREF" + mn + "Q3DZbuiltinZintZint LIT 2 LIT 3 BR 3 LOCAL 1 EXITBLOCK 1 LIT 0 LIT 0 RECORD 2 EXITBLOCK 1 
   BLOCK 3")
   let t ="1 seq." + print.parameter.modname
   let descsym = symbol(merge("type:" + print.resulttype.con), modname, empty:seq.mytype, mytype."internaltype","WORDS" + toword.length.t + t)
    symbols +   symtoseq + // symfromseq+ // con + descsym
  else
   let consrc2= if length.paras = 1 then[local1] else constructor2 + RECORD.countflds(constructor2,1,0)
   let con = symbol(abstracttype.ptype_1, modname, paras, mytype(towords.parameter.modname + abstracttype.ptype_1), consrc2,"")
   let descsym = symbol(merge("type:" + print.resulttype.con), modname, empty:seq.mytype, mytype."internaltype","WORDS" + toword(length.desc + 1) + toword.offset + desc)
    symbols + con + descsym
 else
  let fldtype = fldtype.flds_i
  let fldname = fldname.flds_i
  let tsize = toint.(desc.flds_i)_1
  let newoffset = if offset = 0 then tsize else offset + tsize
   let fldcode = if offset = 0 ∧ i + 1 > length.flds then [local1]
  else if tsize = 1 then [ local1, lit.offset ,  IDXUC ]
  else
   // should use a GEP instruction //
   //"LOCAL 1 LIT"+ toword.offset +"LIT"+ toword.tsize +"castZbuiltinZTzseqZintZint"//
   [ local1, lit(8 * offset) ,  plusOp] 
  let fldsym = symbol(fldname, modname,   ptype  , fldtype, fldcode,"")
  let  confld2=if tsize = 1 then [local(length.paras + 1)] else removeflat2(length.paras + 1,tsize-1)
   definestructure(kind, flds, i + 1, ptype, modname, newoffset, paras + fldtype,constructor2+confld2, desc + subseq(desc.flds_i, 2, length.desc.flds_i), symbols + fldsym)

function  countflds(s:seq.sig,i:int,len:int) int
  if i > length.s then len else
   countflds(s,i+1, if islocal.s_i then len+1 else len)

function cvt(s:seq.sig,i:int,result:seq.word) seq.word
if i > length.s then result else
  let rep=decode.s_i
 let inst= if module.rep="$int" then "LIT"+fsig.rep
  else if module.rep="local" then "LOCAL"+fsig.rep
  else 
   assert s_i=IDXUC   report "unexpected"+fsig.rep
   "IDXUC" 
  cvt(s,i+1,result+inst)
  

use funcsig

use seq.sig

function topara(i:int)seq.word"LOCAL" + toword.i


function postbind(templatemap: symbolset,dict:set.symbol,source :symbolset,working:set.word,toprocess:
 seq.word,i:int,result:seq.symbol) seq.symbol
  if i > length.toprocess then 
    result
    else
      let s=toprocess_i
        let w=working+s
        if  cardinality.w=cardinality.working then 
          postbind(templatemap,dict,source,w,toprocess,i+1,result)
        else 
     let sym= lookupsymbol(source,s) 
      assert isdefined.sym report "KJHG"+mangledname.sym+s  
     if   length.src.sym = 0 then 
      postbind(templatemap,dict,source,w,toprocess,i+1,result+sym)
     else 
    let r=postbind2( dict,    src.sym, 1, "", sym,templatemap,empty:set.word,source)
     postbind(templatemap,dict,source.r,w,toseq(calls.r-w)+subseq(toprocess,i+1,length.toprocess),1,result+sym.r)
 
     
type resultpb is record calls:set.word,source:symbolset,sym:symbol

function postbind2(  dict:set.symbol,     code:seq.word,
 i:int, result:seq.word, thissymbol:symbol,templatemap:symbolset,calls:set.word,source:symbolset)resultpb
  if i > length.code then  
    let newsym=changesrc(thissymbol, result)
    resultpb( calls, source,newsym)
  else if code_i in "IDXUC FREF if assertZbuiltinZwordzseq NOINLINE TESTOPT optionZbuiltinZTZwordzseq allocatespaceZbuiltinZint"then
 postbind2(  dict,    code, i + 1, result + code_i, thissymbol,templatemap,calls,source)
 else if code_i = "WORDS"_1 then
 let l = toint.code_(i + 1) + 2
   postbind2(  dict,      code, i + l, result + subseq(code, i, i + l - 1), thissymbol,templatemap,calls,source)
 else if code_i = "COMMENT"_1 then
   postbind2(  dict,      code, i + 2 + toint.code_(i + 1), result + subseq(code, i, i + 1 + toint.code_(i + 1)), thissymbol,templatemap,calls,source)
 else if code_i in "LIT APPLY RECORD SET WORD DEFINE EXITBLOCK BLOCK BR LOCAL"then
 postbind2(  dict,   code, i + 2, result + subseq(code, i, i + 1), thissymbol,templatemap,calls,source)
 else if isdefined.lookupsymbol(source,code_i)  then
     postbind2( dict,    code, i + 1, result + code_i, thissymbol,templatemap,calls+code_i,source)
  else 
   let down=codedown(code_i)
    if down_2 in ["builtin ","local" ] &or last.down_2="para"_1 then
          postbind2( dict,   code, i + 1, result + code_i, thissymbol,templatemap,calls,source)
   else 
       let modpara=parameter.modname.thissymbol
       let params2=   @(+, replaceT.modpara, empty:seq.mytype, @(+, mytype, empty:seq.mytype, subseq(down, 3, length.down))) 
      let z =X(replaceT(modpara, mytype.down_2),params2,code_i,down_1_1,thissymbol,dict,source,templatemap)
    let name=mangledname.sym.z
            assert noT.name report "postbind2"+name+code_i+print.modname.thissymbol  
      if place.z="C" then  
        let ssss=lookupsymbol(source,name) 
          let newsource=if isdefined.ssss then source else replace(source, sym.z ) 
         postbind2( dict,    code, i + 1, result + name, thissymbol,templatemap,calls+name,newsource)
     else 
     postbind2( dict,   code, i + 1, result + name, thissymbol,templatemap,calls+name,source)

       
function noT(m:word) boolean let d=codedown.m  
   not("T"_1 in @(+,identity,"",subseq(d,3,length.d))) &or d_2="builtin"
   

type resultpair is record  sym:symbol,place:seq.word
  
    
function X(newmodname:mytype,params2:seq.mytype,mangledname:word,name:word,org:symbol, dict:set.symbol,   knownsymbols:symbolset,templatemap:symbolset)resultpair
   let templatename = abstracttype.newmodname
    let newmodpara = parameter.newmodname
      if name = "deepcopy"_1 &and  templatename in "process"  then
              resultpair(definedeepcopy(dict, params2_1,org),"C")
           else
       let f=lookupsymbol(templatemap,mangledname) 
           if isdefined.f then
               let newsym  =  if  length.src.f > 0 &and ((src.f)_1 = "FROMSEQ51Zinternal1"_1 )  then
              let resulttype=replaceT(newmodpara, resulttype.f)
             let mn = mangle("_"_1, newmodname, [ mytype(towords.newmodpara + abstracttype.resulttype), mytype."int"])
             let newsrc ="LOCAL 1 LIT 0 IDXUC FREF" + mn + "Q3DZbuiltinZintZint LIT 2 LIT 3 BR 3 LOCAL 1 EXITBLOCK 1 LIT 0 LIT 0 RECORD 2 EXITBLOCK 1 
                       BLOCK 3"
                symbol(name, newmodname, params2, resulttype, newsrc)  
              else if templatename="seq"_1 &and  name =   merge."sizeoftype:T"  then
                 let typeastext=print.newmodpara 
               let z = if typeastext = "int"then"1"
                       else
                        let xx = lookup(dict, merge("type:" + typeastext), empty:seq.mytype)
                        assert cardinality.xx = 1 ∧ (src.xx_1)_1 = "WORDS"_1 report"can not find type sizeof" + typeastext + print.org
                        subseq(src.xx_1, 3, length.src.xx_1)
                        symbol(name, newmodname, empty:seq.mytype, mytype."int","LIT" + z_1)
                else 
                     symbol(name, newmodname, params2, replaceT(newmodpara, resulttype.f), src.f) 
                  resultpair( newsym,"C" )
         else
            let m2= mangle(name,newmodname,params2)          
            let sym10=if not (m2=mangledname)then lookupsymbol(knownsymbols,m2) else f
              if isdefined.sym10 then   resultpair(  sym10,"B" )
            else    
           let k = lookup(dict, replaceTinname( newmodpara, name), params2)
          // case for examples like frombits:T(bits)T which needs to find frombits:bit(bits)bit //
          assert cardinality.k = 1 report"cannot find template for" +  mangledname +
          mangle(name,newmodname,params2) +towords.newmodpara+ "&br"+ 
          @(+,print,"",toseq.k)  
            + name + "("
           + @(seperator.",", print,"", params2)
           + ") &br while process"
           + print.org
           + "templatename"
           + templatename
           + mangledname
           + "&br newmodpara:"
           + print.newmodpara
           + toword.cardinality.k     
           // +@(+,mangledname,"",toseq.templatemap)  //
             assert mangledname ≠ mangledname.k_1 report"ERR12" + mangledname + mangledname.k_1 
              let sym5=lookupsymbol(knownsymbols, mangledname.k_1)
             if not.isdefined.sym5 then
                let down=codedown.mangledname.k_1
                  let paras=     @(+, mytype, empty:seq.mytype, subseq(down, 3, length.down) ) 
                 X( mytype.down_2 ,paras,mangledname.k_1,down_1_1, org, dict , knownsymbols,templatemap)
             else 
               resultpair(  k_1,"D" )
           

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
    let adde = mangle("add"_1, mytype(towords.typ + "encoding"), [ mytype(towords.typ +" encodingstate"), mytype(towords.typ+"  encodingrep")])
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
    [ symbol("toseq"_1, modname.f, [ t], seqtype,"STUB") ] else //,
       symbol(merge("to:"+print.t), modname.f, [ seqtype],t ,"STUB")
    ]  
    else // empty:seq.symbol
     firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f, exportmodule.f, rawsrc.f)
 else if input_1 in "Function function"then
 let t = parse(stubdict, getheader.input)
  let code = bodyonly.code.t
  let name = funcname.t
  let paratypes = funcparametertypes.t
   assert iscomplex.modname.f = hasT(input, 2)report"Must use type T in function name or parameters in parameterized module and T cannot be used in non - parameterized module" + getheader.input
   let firstinstruction = code_1
    let sym =if firstinstruction in "usemangleZinternal1"then
      let builtinname = mangle(name, mytype."builtin", paratypes )
      let src = @(+, topara,"", arithseq(length.paratypes, 1, 1)) + builtinname
       symbol(name, mytype.if iscomplex.modname.f then"T builtin"else"builtin", paratypes, funcreturntype.t, src)
      else    if code_1 = "WORDS"_1  &and (  
  let l = toint.code_2 + 3
      l ≤ length.code ∧ code_l = "builtinZinternal1Zwordzseq"_1) then
         let src=subseq(code, 1 + 2, toint.code_2 + 2)
          symbol(name, modname.f, paratypes, funcreturntype.t,src )
      else symbol(name, modname.f, paratypes, funcreturntype.t, input)  
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

function definedeepcopy( dict:set.symbol, type:mytype ,org:symbol)symbol
 // assert towords.type in ["int seq","int","word3","stat5","word seq","llvmtypeele","word","llvmconst","const3","inst","flddesc seq","match5","flddesc","templatepart seq","templatepart","internalbc","persistant"]report"definedeepcopy"+ towords.type //
 let body= if abstracttype.type in "encoding int word"then "LOCAL 1"
 else
  // assert length.print.type = 1 &or print.type in ["match5","seq.int","llvmconst","match5","inst","libsym","llvmtypeele","word3","const3","seq.word","stat5","seq.flddesc","flddesc","seq.templatepart","templatepart","set.mod2desc"]report"DDD"+ print.type //
  if abstracttype.type = "seq"_1 then
  let typepara = parameter.type
   let dc = deepcopymangle.typepara
   let pseqidx = mangle("_"_1, type, [ mytype(towords.type + "pseq"), mytype."int"])
   let cat = mangle("+"_1, type, [ mytype(towords.type + "seq"), type])
   let blockittype = if abstracttype.parameter.type in "seq word char int"then mytype."int blockseq"
   else mytype(towords.type + "blockseq")
   let blockit = mangle("blockit"_1, blockittype, [ mytype(towords.parameter.blockittype+"seq")])
    "LIT 0 LIT 0 RECORD 2 LOCAL 1 FREF" + dc + "FREF" + cat + "FREF"
    + pseqidx
    + "APPLY 5"
    + blockit
  else
   let xx = lookup(dict, merge("type:" + print.type), empty:seq.mytype)
    assert cardinality.xx = 1 ∧ (src.xx_1)_1 = "WORDS"_1 report"can not find type deepcopy" + print.type +print.org
    let z = subseq(src.xx_1, 3, toint.(src.xx_1)_2 + 2)
    let y = subfld(z, 2, 0, 2)
    if last.y = "1"_1 then
     // only one element in record so type is not represent by actual record //"LOCAL 1"
      + subseq(y, 6, length.y - 2)
     else
      assert z_1 ≠ "1"_1 report"Err99a"
       y
    symbol("deepcopy"_1, mytype(towords.type + "process"), [ type], type, body)
 
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