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
 asset.@(+, replaceTsymbol.with, empty:seq.symbol, toseq.defines.f), 
 asset.@(+, replaceTsymbol.with, empty:seq.symbol, 
 toseq.exports.f), @(+, replaceTsymbol.with, empty:seq.symbol, unboundexports.f), 
 empty:set.symbol)

function =(a:firstpass, b:firstpass)boolean modname.a = modname.b

Function ?(a:firstpass, b:firstpass)ordering toalphaseq.towords.modname.a ? toalphaseq.towords.modname.b

Function print(b:firstpass)seq.word
 " &br  &br" + print.modname.b + " &br defines" + printdict.defines.b
 + " &br unboundexports"
 + printdict.asset.unboundexports.b

Function find(modset:set.firstpass, name:mytype)set.firstpass
 findelement(firstpass(name, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol)
 , modset)

type linkage is record   result:prg,compiled:seq.sig,abstractmods:seq.expmod,
simplemods: seq.expmod

Function abstractmods(l:linkage) seq.expmod  export

Function simplemods(l:linkage) seq.expmod   export

function result (linkage) prg export

function compiled(linkage)seq.sig export


Function type:linkage internaltype export

use seq.unboundexport 

use seq.liblib


Function pass1(allsrc:seq.seq.seq.word, exports:seq.word, libs:seq.liblib)linkage
   let librarysyms=libknown.libs
   let librarymods=asset.libfirstpass.libs
// assert false report print.librarysyms //
  let discard=getinstance.esymboltext
  let a = @(+, gathersymbols, librarymods, allsrc)
  let u0=expanduse.(a)
 // let u1=@(+,getunboundexport,empty:seq.unboundexport,toseq.u0)
   let d1=       resolveexport(u0,empty:set.symbol,mytype."1",u1,1,empty:seq.unboundexport)
  // let d1 = resolveunboundexports.u0 
  let alltypes = @(+, findtypes.d1, empty:seq.typedesc, toseq.d1)
  let zx = processtypedef(empty:set.symbol, alltypes, 1, empty:seq.typedesc, empty:seq.symbol)
  let d2 = asset.@(+, fixfirstpass.asset.zx, empty:seq.firstpass, toseq.d1)
  let abstractsimple=split(toseq.d2,1,empty:seq.firstpass,empty:seq.firstpass)
  let simple = abstractsimple_2
  let allsymbols=@(&cup,      defines,empty:set.symbol, toseq.d2)
  let xxx=@(+,toplaceholder,empty:seq.sig,toseq.allsymbols)
  let simple2=@(+,simplemods.exports,  empty:seq.expmod ,simple )
  let c1= @(addtomap,identity,emptyprg,librarysyms)
  let c2=      @( bind3(d2),identity,c1,simple)
  let root=placeholder("Wroot",empty:seq.mytype,mytype."W",mytype."int")
  let c3=@(addtomap,identity,c2,zx)
  let source=map(c3,root, @(+, exports, empty:seq.sig, simple2))
  let temp33=@(bind3.d2,identity,emptyprg,abstractsimple_1)
  let templatemap2=@( maptemp.temp33,identity,temp33,toseq.allsymbols)
  let result=postbind(templatemap2,allsymbols,  source   ,empty:set.sig, [root],1,emptyprg)
  let c4=@(+,ecvt,empty:set.sig, keys.c1) &cap @(+,ecvt,empty:set.sig,keys.result)
  linkage(result,toseq.c4,@(+,abstractmods(exports,templatemap2), empty:seq.expmod ,abstractsimple_1),simple2)
 
 use set.sig
 

 function addtomap(newdict:prg,s:symbol)prg
 map(newdict,toplaceholder.s, code.s )
            
   
    function  maptemp(templates:prg,st:prg,  s:symbol) prg
               if  length.code.s > 0 &and (code.s)_1=exit  &or  ( template.s="none"_1  )  then st else 
                   let key=toplaceholder.s
                  let s2=lookupcode(templates,toPH.template.s)
                  assert not.isempty.s2 report "maptemp function:"+print2.s
                  map (st,key, target.s2_1,code.s2_1 )
                 
    function toPH(w:word) sig
      let d= codedown.w
placeholder(  d_1 ,@(+, mytype, empty:seq.mytype, subseq(d, 3, length.d)), mytype.d_2,mytype."?")
                
        use seq.target          
                                 


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
    let typdesc=gettypedesc(defined,typ)
    if typdesc="" then empty:seq.flddesc
    else subflddefined(s, T, i + 1, defined, result + flddesc(typdesc, combined.next))
       
         
function gettypedesc(dict:set.symbol,typ:mytype) seq.word
let sym = lookup(dict, merge("type:" + print.typ), empty:seq.mytype)
     if cardinality.sym = 0  then ""
     else fsig.decode((code.sym_1)_1)
  

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
     firstpass(modname.f, uses.f, newdefines, newexports, unboundexports.f, unbound.f)

type typedesc is record s:symbol, kind:word, name:word, flds:seq.flddesc

function cvty(t:flddesc)seq.word
 [ toword.length.towords.combined.t] + towords.combined.t
 + if desc.t = ""then""else desc.t + "/"

function findtypes(dict:set.symbol, s:symbol)seq.typedesc
 if resulttype.s = mytype."internaltype"then
 if length.src.s=0 &or (src.s)_1 in "WORDS"then
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
  
type  unboundexport is  record modname:mytype,unbound:symbol

function getunboundexport(f: firstpass) seq.unboundexport
    @(+,unboundexport(modname.f),empty:seq.unboundexport, unboundexports.f)
    
function  resolveexport( modset:set.firstpass,lastdict:set.symbol,lastmodname:mytype,toprocess:seq.unboundexport,i:int,
     unresolved:seq.unboundexport) set.firstpass
if i > length.toprocess then 
      if length.unresolved=0 then  modset
      else 
          assert length.toprocess &ne length.unresolved report"unresolved exports" + @(+, print,"",unresolved)
          resolveexport(modset,empty:set.symbol,mytype."1",unresolved,1,empty:seq.unboundexport)
else
  let u=toprocess_i
  let dict= if lastmodname=modname.u then lastdict else   
         let e = find(modset, modname.u)
          @(∪, builddict.modset, defines.e_1 ∪ unbound.e_1, uses.e_1)
  let x = findelement2(dict, unbound.u)
//  assert not(mangledname.unbound.u= "typeQ3AwordZwords"_1)
  report print.u+toword.cardinality.x //
  if cardinality.x = 1 then
     assert resulttype.x_1 = resulttype.unbound.u report"export return type missmatch" + print.unbound.u + print.x_1
     let f=find(modset, modname.u)_1
     let newf=firstpass(modname.f, uses.f, defines.f, replace(exports.f ,x), unboundexports.f, unbound.f)
     // let t=replace(modset,newf)
     let f2=find(modset, modname.u)_1 //
      resolveexport(replace(modset,newf),dict,modname.u,toprocess,i+1,unresolved) 
  else 
      resolveexport(modset,dict,modname.u,toprocess,i+1,unresolved) 

    
function print(x:unboundexport) seq.word "&br"+
print.modname.x+print.unbound.x +mangledname.unbound.x

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
  let new = @(resolveexport.dict, identity, firstpass(modname.f, uses.f, defines.f, exports.f, empty:seq.symbol, unbound.f), unboundexports.f)
   replace(modset, new)

function resolveexport(dict:set.symbol, f:firstpass, s:symbol)firstpass
 let x = findelement2(dict, s)
  if cardinality.x = 1 then
  assert resulttype.x_1 = resulttype.s report"export return type missmatch" + print.s + print.x_1
    firstpass(modname.f, uses.f, defines.f, exports.f ∪ x, unboundexports.f, unbound.f)
  else
   firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + s, unbound.f)

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


 use seq.seq.firstpass
 
function split(s:seq.firstpass,i:int,abstract:seq.firstpass,simple:seq.firstpass) seq.seq.firstpass
if i > length.s then [abstract,simple] else 
 let f=s_i
 if length.towords.modname.f = 1 ∧ length.uses.f > 0 then 
  split(s,i+1,abstract,simple+f)
 else if parameter.modname.f = mytype."T"then
  split(s,i+1,abstract+f,simple)
  else  split(s,i+1,abstract,simple)
 
function bind3( modset:set.firstpass, p:prg,  f:firstpass) prg
   let dict = builddict(modset, f) ∪ headdict
    @(bind2.dict,identity,p,   toseq.defines.f)
       
function bind2(dict:set.symbol,p:prg,s:symbol) prg
  let ph=toplaceholder.s
  let symsrc = src.s
  let code=if length.symsrc > 0 &and symsrc_1 in "Function function" then
      let symsrc2=     text.decode(esymboltext,to:encoding.symboltext(valueofencoding.ph))  
     let b = parse(bindinfo(dict,"", empty:seq.mytype), symsrc2)
     let cd=code.b
        let src2= if cd_1 in "usemangleZinternal1"then
               let name = funcname.b
               let paratypes = funcparametertypes.b
                  let code2=@(+, local,empty:seq.sig, arithseq(length.paratypes, 1, 1))+
               sig([name],paratypes,mytype."builtin",empty:seq.sig,funcreturntype.b)
           @(+, topara,"", arithseq(length.paratypes , 1, 1)) + mangle(name, mytype."builtin", paratypes )
        else    if cd_1 = "WORDS"_1  &and (  
        let l = toint.cd_2 + 3
           l ≤ length.cd ∧ cd_l = "builtinZinternal1Zwordzseq"_1) then
          subseq(cd, 1 + 2, toint.cd_2 + 2)
       else cd 
    scannew(src2,1,empty:seq.sig)
    else if  length.symsrc > 0  &and symsrc _1 in "type" then   [exit,wordssig.symsrc ]  
   else   code.s  
 map(p,ph,ph, code )
 
 
    
function definestructure(kind:word, flds:seq.flddesc, i:int, ptype:seq.mytype, modname:mytype, offset:int, 
paras:seq.mytype, constructor2:seq.sig, desc:seq.word, symbols:seq.symbol)seq.symbol
 if i > length.flds then
 if kind = "sequence"_1 then
  let mn = mangle("_"_1, modname, [mytype(towords.parameter.modname + abstracttype.ptype_1), mytype."int"])
    let indexfunc= placeholder("_", [mytype(towords.parameter.modname + abstracttype.ptype_1), mytype."int"], modname,parameter.modname) 
   let concode2=[FREFsig.indexfunc]+constructor2+RECORD.countflds(constructor2,1,1)
    let con = symbol(abstracttype.ptype_1, modname, paras, mytype(towords.parameter.modname + abstracttype.ptype_1), concode2,"")
   let seqtype=mytype(towords.parameter.modname + "seq"_1)
   let symtoseq = symbol("toseq"_1, modname, ptype, seqtype,[local1],"")
   let symfromseq=symbol(merge("to:"+print.ptype_1),modname,[seqtype],ptype_1,
    [local1,lit.0,IDXUC,FREFsig.indexfunc,eqOp,lit.2,lit.3,br,local1,exit,emptyseqOp,exit,block.3],"")
   let descsym = symbol(merge("type:" + print.resulttype.con), modname, empty:seq.mytype, mytype."internaltype",
   [wordssig("1 seq." + print.parameter.modname)],"")
    symbols +   symtoseq +  symfromseq+  con + descsym
  else
   let concode2= if length.paras = 1 then[local1] else constructor2 + RECORD.countflds(constructor2,1,0)
   let con = symbol(abstracttype.ptype_1, modname, paras, mytype(towords.parameter.modname + abstracttype.ptype_1), concode2,"")
   let descsym = symbol(merge("type:" + print.resulttype.con), modname, empty:seq.mytype, mytype."internaltype",
   [wordssig([toword.offset] + desc)],"")
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

  

use funcsig

use seq.sig



function topara(i:int)seq.word"LOCAL" + toword.i

type  lookR is record  isdefined:boolean ,code:seq.sig,ph:sig

   
function postbind(templatemap: prg,dict:set.symbol,source :prg,working:set.sig,toprocess: seq.sig,i:int,result:prg) prg
  if i > length.toprocess then   result
  else
        let s=toprocess_i
        let w=working+s
        if  cardinality.w=cardinality.working then 
          postbind(templatemap,dict,source,w,toprocess,i+1,result)
        else 
          let lr=lookupcode(source,s)
          assert not.isempty.lr report "KJHG"+print.s  
          let modname=mytype.module.decode.s
          if  modname = mytype."builtin" then 
             postbind(templatemap,dict,source,w,toprocess,i+1,result)
          else 
           let r=postbind3( dict,   code.lr_1, 1, empty:seq.sig,modname,print.s,templatemap,empty:set.sig,source)
           postbind(templatemap,dict,source.r,w,toseq(calls.r-w)+subseq(toprocess,i+1,length.toprocess),1,
           if  length.toprocess=1 &and toprocess_1=placeholder("Wroot",empty:seq.mytype,mytype."W",mytype."int")    
           then result else  add(result,s,code.r))
 
     
type resultpb is record calls:set.sig,source:prg,code:seq.sig


 
function postbind3(dict:set.symbol,code:seq.sig,
 i:int,result:seq.sig, modname:mytype,org:seq.word,templatemap:prg,calls:set.sig,source:prg)resultpb
 if i > length.code then  
 resultpb(calls , source,result)
 else if isplaceholder.code_i then
   let x=decode.code_i
   let s=if module.x="$fref" then  (code.x)_1 else code_i
   let lr=lookupcode(source,s)
   if not.isempty.lr  then 
        let p2=if module.x="$fref" then  FREFsig.s else   s 
            postbind3( dict,code, i+1, result+p2 , modname,org,templatemap,calls +s , source )
   else 
       let rep=decode.s
       let modpara=parameter.modname 
       let params2=   @(+, replaceT.modpara, empty:seq.mytype, paratypes.rep) 
       let z =X(replaceT(modpara, mytype.module.rep),params2,s,(fsig.rep)_1,org,dict,source,templatemap)
         if place.z="C" then  
                    let ssss=lookupcode(source,ph.z) 
                    if not.isempty.ssss then 
                       let p2=if module.x="$fref" then  FREFsig.target.ssss_1 else   target.ssss_1 
                        postbind3( dict,code, i+1, result+p2 , modname,org,templatemap,calls +target.ssss_1 , source)   
                      else 
                         let p2=if module.x="$fref" then  FREFsig.ph.z else   ph.z 
                        postbind3( dict,code, i+1, result+p2 , modname,org,templatemap,calls +ph.z , add(source, ph.z,code.z ))
         else 
           let p2=if module.x="$fref" then  FREFsig.ph.z else   ph.z 
           postbind3( dict,code, i+1, result+p2 , modname,org,templatemap,calls +ph.z , source)
 else
  postbind3(dict,code,i+1,result+code_i,modname,org,templatemap,calls,source)
   

type resultpair is record ph:sig,code:seq.sig,place:seq.word
  
    
function X(newmodname:mytype,params2:seq.mytype,s:sig,name:word,org:seq.word, dict:set.symbol,   knownsymbols:prg,templatemap:prg)resultpair
   let templatename = abstracttype.newmodname
   let newmodpara = parameter.newmodname
      if name = "deepcopy"_1 &and  templatename in "process"  then
               let type= params2_1
          resultpair( placeholder("deepcopy" ,  [type],mytype(towords.type + "process"), type),
         definedeepcopy(dict, type,org),"C")           
       else  if templatename in " process"  &and  name =   merge."sizeoftype:T"  then
                 let typeastext=print.newmodpara 
               let z = if typeastext = "int"then 1
                       else
                         let typdesc=  gettypedesc(dict,newmodpara)
                         assert  length.typdesc > 0 report"can not find type sizeof" + typeastext + org
                         toint.typdesc_1
                    resultpair(  placeholder([name],  empty:seq.mytype,newmodname, mytype."int"),[lit.z] ,"C")
    else     
     let f=lookupcode(templatemap,s) 
    if not.isempty.f then
        let rep2=decode.target.f_1
        resultpair(     placeholder([name],  params2,newmodname, replaceT(newmodpara, mytype.returntype.rep2)),code.f_1,  "C" )
     else
        let m2=  placeholder([name],  params2,newmodname, mytype."?")
        let sym10=if not (m2=s)then lookupcode(knownsymbols,m2) else f
        if not.isempty.sym10 then   resultpair(  target.sym10_1,code.sym10_1,"B" )
        else    
           let k = lookup(dict, replaceTinname( newmodpara, name), params2)
          // case for examples like frombits:T(bits)T which needs to find frombits:bit(bits)bit //
          assert cardinality.k = 1 report"cannot find template for" + 
          @(+,print,"",toseq.k)  
            + name + "("
           + @(seperator.",", print,"", params2)
           + ") &br while process"
           + org
           + "templatename"
           + templatename
           + "&br newmodpara:"
           + print.newmodpara
           + toword.cardinality.k     
             let ph=toplaceholder.k_1
             assert not(s =  ph) report"ERR12" + print.[s,ph]  
              let sym5=lookupcode(knownsymbols, ph)
             if isempty.sym5 then
                let rep=decode.ph
                           X( mytype.module.rep ,paratypes.rep,ph,(fsig.rep)_1, org, dict , knownsymbols,templatemap)
             else 
               resultpair(  ph,code.k_1,"D" )
           

Function headdict set.symbol
let modulename = mytype."internal1"
 asset
 .[ symbol("builtin"_1, modulename, [ mytype."internal1"], mytype."internal",""), 
 symbol("builtin"_1, modulename, [ mytype."word seq"], mytype."internal",""), 
  symbol("export"_1, modulename, empty:seq.mytype, mytype."internal1",""), 
symbol("unbound"_1, modulename, empty:seq.mytype, mytype."internal1",""), 
symbol("stub"_1, modulename, empty:seq.mytype, mytype."internal1",""), 
symbol("usemangle"_1, modulename, empty:seq.mytype, mytype."internal1","")]

function gathersymbols(input:seq.seq.word)firstpass
 @(wrapgathersymbols( headdict)
 , identity
 , firstpass(mytype."?", empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol)
 , input)

function wrapgathersymbols( stubdict:set.symbol, f:firstpass, input:seq.word)firstpass gathersymbols( stubdict, f, input)

function definefld( modname:mytype, t:seq.mytype, m:mytype)symbol 
symbol(abstracttype.m, modname, t, parameter.m, "")

function hasT(s:seq.word, i:int)boolean
 // used to determine it type T is specified somewhere in function sig //
 if s_(i + 1) in ":."then
 // s_i is name // hasT(s, i + 2)
 else
  // at end of type //
  if s_i = "T"_1 then true
  else if s_(i + 1) in ",("then hasT(s, i + 2)
  else // at end of parameter list or beginning of function type // false

 
type  symboltext is record ph:sig,modname:mytype,text:seq.word

type  esymboltext is encoding symboltext

function hash(s:symboltext) int valueofencoding.ph.s

function =(a:symboltext,b:symboltext) boolean ph.a=ph.b

function assignencoding(int, s:symboltext) int valueofencoding.ph.s


function gathersymbols(stubdict:set.symbol, f:firstpass, input:seq.word)firstpass
 // assert print.modname.f in ["?","stdlib","UTF8","altgen"]∨(print.modname.f ="bitpackedseq.T"∧ cardinality.defines.f + cardinality.unbound.f < 8)report print.modname.f + printdict.unbound.f //
 if length.input = 0 then 
  let k= defines.f &cap asset.unboundexports.f
   if isempty.k then f else
      firstpass(modname.f, uses.f , defines.f, 
      exports.f &cup k, toseq.(asset.unboundexports.f-k), unbound.f)
 else if input_1 in "use"then
 let t = parse(empty:set.symbol, subseq(input, 2, length.input))
   firstpass(modname.f, uses.f + mytype.code.t, defines.f, exports.f, unboundexports.f, unbound.f)
 else if input_1 in "type"then
 let b = parse(empty:set.symbol, input)
  let kind =(code.b)_1
  let name =(code.b)_2
  let t = mytype(towords.parameter.modname.f + name)
   if kind in "encoding"then
     assert parameter.modname.f = mytype.""report"encoding in template?"
     let typ = parameter.(types.b)_1
     let addefunc= placeholder("add",[ mytype(towords.typ +" encodingstate"), mytype(towords.typ+"  encodingrep")]
      , mytype(towords.typ + "encoding"),mytype(towords.typ +" encodingstate"))
     let code2=[FREFsig.addefunc,lit.if name = "wordencoding"_1 then 1 else 0,wordsig.merge([ name] + print.modname.f),
        RECORD.3,wordssig."NOINLINE STATE",optionOp]
     let sym = symbol(name, modname.f, empty:seq.mytype, mytype(towords.typ + "erecord"), code2,"")
       firstpass(modname.f, uses.f + mytype(towords.typ + "encoding"), defines.f + sym, exports.f, unboundexports.f, unbound.f)
   else
    assert parameter.modname.f in [ mytype."", mytype."T"]report"KLJKL"
    let sizeofsym = symbol(merge("type:" + print.t), modname.f, empty:seq.mytype, mytype."internaltype", input)
    let constructor = symbol(name, modname.f, @(+, parameter, empty:seq.mytype, types.b), t,"")
    let syms = @(+, definefld(modname.f, [ t]), [ constructor, sizeofsym], types.b)
    + if kind = "sequence"_1 then
      let seqtype=mytype(towords.parameter.t + "seq"_1)
    [ symbol("toseq"_1, modname.f, [ t], seqtype,"")     ,
       symbol(merge("to:"+print.t), modname.f, [ seqtype],t ,"")
    ]  
    else   empty:seq.symbol
     firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f)
 else if input_1 in "Function function"then
 let t = parse(stubdict, getheader.input)
  let code = code.t
   let name = funcname.t
  let paratypes = funcparametertypes.t
  assert iscomplex.modname.f = hasT(input, 2)report"Must use type T in function name or parameters in parameterized module and T cannot be used in non - parameterized module" + getheader.input
    let sym =  if code_1 in "usemangleZinternal1"then
              symbol(name, mytype.if iscomplex.modname.f then"T builtin"else"builtin", paratypes, funcreturntype.t, "function")
      else   symbol(name, modname.f, paratypes, funcreturntype.t, if last.input in "export unbound"  then "" else "function")  
      if last.input in "export" then
       firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f)
      else if last.input in "unbound" then
       firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + sym)
      else
        assert not(sym in defines.f)report"Function" + name.sym + "is defined twice in module" + print.modname.f
        let discard= encode(esymboltext,symboltext(toplaceholder.sym,modname.f,input))
        firstpass(modname.f, uses.f, defines.f + sym, if input_1 = "Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f)
 else if input_1 in "module Module"then
 firstpass(mytype.if length.input > 2 then"T" + input_2 else [ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f)
 else f

   
function definedeepcopy( dict:set.symbol, type:mytype ,org:seq.word) seq.sig
 // assert towords.type in ["int seq","int","word3","stat5","word seq","llvmtypeele","word","llvmconst","const3","inst","flddesc seq","match5","flddesc","templatepart seq","templatepart","internalbc","persistant"]report"definedeepcopy"+ towords.type //
  if abstracttype.type in "encoding int word"then [local1]
 else
  // assert length.print.type = 1 &or print.type in ["match5","seq.int","llvmconst","match5","inst","libsym","llvmtypeele","word3","const3","seq.word","stat5","seq.flddesc","flddesc","seq.templatepart","templatepart","set.mod2desc"]report"DDD"+ print.type //
  if abstracttype.type = "seq"_1 then
  let typepara = parameter.type
   let dc = placeholder("deepcopy",[typepara],mytype."process",typepara  )
   let pseqidx = placeholder("_",  [ mytype(towords.type + "pseq"), mytype."int"],type, type )
   let cat = placeholder("+",  [ mytype(towords.type + "seq"),type], mytype(towords.type + "seq"),mytype(towords.type + "seq"))
   let blockittype = if abstracttype.parameter.type in "seq word char int"then mytype."int blockseq"
   else mytype(towords.type + "blockseq")
   let blockit = placeholder("blockit",  [ mytype(towords.parameter.blockittype+"seq")],blockittype,mytype(towords.parameter.blockittype+"seq"))
    [emptyseqOp, local1, FREFsig.dc ,FREFsig.cat, FREFsig.pseqidx,apply.5,blockit]
  else
   let typedesc=gettypedesc(dict,type)
    assert length.typedesc > 0 report"can not find type deepcopy" + print.type +org
     let y = subfld(typedesc, 2, 0, 2)
    if last.y = RECORD.1 then
     // only one element in record so type is not represent by actual record //[local1]
      + subseq(y, 4, length.y - 1)
     else
      assert typedesc_1 ≠ "1"_1 report"Err99a"
       y
  
   
function subfld(desc:seq.word, i:int, fldno:int, starttype:int)seq.sig
 if i > length.desc then [RECORD.fldno]
 else if i < length.desc ∧ desc_(i + 1) = "."_1 then
 subfld(desc, i + 2, fldno, starttype)
 else
  let fldtype = mytype.@(+,_.desc,"", arithseq((i - starttype + 2) / 2, -2, i))
   {(if abstracttype.fldtype in "encoding int word"then [ local1,lit.fldno,IDXUC ]  
   else
    assert abstracttype.fldtype = "seq"_1 report"ERR99" + desc
     [ local1,lit.fldno,IDXUC,placeholder("deepcopy",[fldtype],mytype."process",fldtype  )])
   + subfld(desc, i + 1, fldno + 1, i + 1)}
 
   
-------------------------


use seq.cached

use seq.expmod

use intercode
  
function  simplemods(exported:seq.word, f:firstpass) seq.expmod 
  if  not( abstracttype.modname.f in exported )   &or length.towords.modname.f &ne  1 then  empty:seq.expmod 
  else 
    let b2=@(+,   toplaceholder,empty:seq.sig,toseq.exports.f )
  [expmod(abstracttype.modname.f,b2,empty:seq.sig,empty:seq.mytype)]
  
Function toplaceholder( s:symbol) sig  
   if (length.towords.modname.s > 1)  &and   not((towords.modname.s)_1="T"_1) then
      let newparams=  @(+,replaceT(parameter.modname.s),empty:seq.mytype,paratypes.s)
      placeholder([name.s], newparams,modname.s,      replaceT(parameter.modname.s,resulttype.s))
   else 
    placeholder ([name.s] , paratypes.s, modname.s ,resulttype.s)
    
 
    
function abstractmods(exported:seq.word,templatemap:prg, f:firstpass) seq.expmod
  if  not( abstracttype.modname.f in exported )  &or not.isabstract.modname.f then empty:seq.expmod  else 
     let defs=@(+,tosig.templatemap,empty:seq.sig,toseq.defines.f ) 
    let exp=@(+,tosig.templatemap ,empty:seq.sig,toseq.exports.f ) 
          [ expmod(abstracttype.modname.f,exp,defs,uses.f)]
       
   Function tosig(templatemap:prg, s:symbol) sig  
       let ph=toplaceholder.s
       let t=lookupcode(templatemap,ph)
       let code2=if isempty.t then empty:seq.sig else code.t_1
        sig ([name.s] , paratypes.s, modname.s , code2,resulttype.s)
   
   -----------------------
   
/   Function prepare(s:seq.word,i:int,result:seq.word) seq.word
  if i > length.s then  result 
  else 
   let this = s_i 
   if this  in "LOCAL LIT WORD RECORD APPLY BLOCK EXITBLOCK BR DEFINE FREF"   then    prepare(s,i+2,result+[ this,s_(i+1)] )
        else if this = "COMMENT"_1 then prepare(s, i + 2 + toint.s_(i + 1), result)
      else if this = "IDXUC"_1 then   prepare( s, i + 1,  result + this)
      else if this = "SET"_1 then prepare( s, i + 2,  result)
      else if this = "WORDS"_1 then
         let l = toint.s_(i + 1)
         prepare( s, i + 2 + l,   result + subseq(s, i , i + 1 + l))
    else     if this="builtinZinternal1Zwordzseq"_1 then 
   // comment keeps this from being striped off //   prepare(s, i + 1,   result)
    else      
        let d = codedown.this
         assert length.d > 1 report"BBBP 3" + this+s
       if d_2=" local" then 
              prepare(s, i + 1,  result +"LOCAL"+d_1)
          else if last.d_2 = "para"_1 then
                 prepare( s, i + 1, result + "LOCAL"+d_2_1)
         else  prepare( s, i + 1,  result + this)
 
 