run mylib test

Module pass1

run main test1


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

use seq.seq.seq.word

use seq.seq.word

use set.word

use words

use format

use seq.mapele
 
 
 
 function replaceTmyinternaltype(with:mytype,it:myinternaltype) myinternaltype
 myinternaltype(size.it,kind.it,name.it,replaceT(with,modname.it),subflds.it)

function =(a:firstpass, b:firstpass)boolean modname.a = modname.b

Function ?(a:firstpass, b:firstpass)ordering toalphaseq.towords.modname.a ? toalphaseq.towords.modname.b

Function print(b:firstpass)seq.word
 " &br  &br" + print.modname.b + " &br defines" + printdict.defines.b
 + " &br unboundexports"
 + printdict.asset.unboundexports.b

Function find(modset:set.firstpass, name:mytype)set.firstpass
 findelement(firstpass(name, empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol,empty:seq.myinternaltype)
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
   let librarysyms=libsymbols.libs
   let librarymods=asset.libfirstpass.libs
// assert false report print.librarysyms //
  let discard=getinstance.esymboltext
  let a = @(+, gathersymbols, librarymods, allsrc)
  let expand1=expanduse.(expanduseresult(a,empty:seq.mapele))
  let u0=firstpasses.expand1
 // let u1=@(+,getunboundexport,empty:seq.unboundexport,toseq.u0)
   let d1=       resolveexport(u0,empty:set.symbol,mytype."1",u1,1,empty:seq.unboundexport)
  // let d1 = resolveunboundexports.u0 
  let alltypes = @(+,  types , empty:seq.myinternaltype,  toseq.d1)
  let alltypes1=processtypedef(empty:seq.myinternaltype, alltypes, 1, empty:seq.myinternaltype)
  let abstractsimple1=split(toseq.d1,1,empty:seq.firstpass,empty:seq.firstpass)
  let simple =  abstractsimple1_2  
  let abstract=abstractsimple1_1
  let allsymbols1=@(&cup,      defines,empty:set.symbol, toseq.d1)
  let simple2=@(+,simplemods.exports,  empty:seq.expmod ,abstractsimple1_2 )
  let c2= @( bind3(d1),identity,librarysyms,simple)
  let root=placeholder("Wroot",empty:seq.mytype,mytype."W",mytype."int")
  let c3 = processtypedef(empty:seq.myinternaltype, alltypes, 1, empty:seq.myinternaltype, c2)
  let source=map(c3,root, @(+, exports, empty:seq.sig, simple2))
  let temp33=@(mapabstracttype,identity,otherlibsyms.libs,alltypes)
  let temp34=@(bind3(d1),identity, temp33,abstract)
  let templatemap2=@( maptemp.temp34,identity,temp34,// toseq.allsymbols1 // map.expand1)
  let result=postbind(alltypes1,templatemap2,allsymbols1,  source   ,empty:set.sig, [root],1,emptyprg)
  let c4=@(+,ecvt,empty:set.sig, keys.librarysyms) &cap @(+,ecvt,empty:set.sig,keys.result)
  linkage(result,toseq.c4,@(+,abstractmods(exports,templatemap2), empty:seq.expmod ,abstract),simple2)
 
 use set.sig
 
   function   mapabstracttype(p:prg,it:myinternaltype) prg
       if towords.parameter.modname.it="T" then 
         let ph=placeholder([merge("type:" + print.mytype(towords.parameter.modname.it + name.it))],
           empty:seq.mytype,modname.it, mytype."internaltype")
         map(p,ph,ph,ascode.it)
       else p

   function  maptemp(templates:prg,st:prg,  s:mapele) prg
                   let key=(pair.s)_1
                   let target=(pair.s)_2
                  let s2=lookupcode(templates,target)
                 //  assert not.isempty.s2 report "maptemp function:"+print.key+print.target //
                  if isempty.s2 then
                     map (st,key, target,empty:seq.sig)
                  else 
                  map (st,key, target,code.s2_1 )
        
   
                 
                
        use seq.target          
                                 


function processtypedef(defined:seq.myinternaltype, undefined:seq.myinternaltype, i:int, newundefined:seq.myinternaltype, other:prg)prg
 if i > length.undefined then
 if length.newundefined = 0 then other
  else
    assert length.undefined > length.newundefined 
    report"ProBLEM" + @(seperator." &br",  name, "", newundefined)
    processtypedef(defined, newundefined, 1, empty:seq.myinternaltype, other)
 else if "T"_1 in towords.modname.undefined_i then 
    processtypedef(defined , undefined, i + 1, newundefined, other)
 else if kind.undefined_i = "defined"_1 then
    processtypedef(defined + undefined_i, undefined, i + 1, newundefined, other)
 else if kind.undefined_i = "encoding"_1 then
 let td = undefined_i
    let typ = parameter.(subflds.td)_1
     let addefunc= placeholder("add",[ mytype(towords.typ +" encodingstate"), mytype(towords.typ+"  encodingrep")]
      , mytype(towords.typ + "encoding"),mytype(towords.typ +" encodingstate"))
     let code2=[FREFsig.addefunc,lit.if name.td = "wordencoding"_1 then 1 else 0,wordsig.merge([ name.td] + print.modname.td),
        RECORD.3,wordssig."NOINLINE STATE",optionOp]
     let ph= placeholder([name.td],  empty:seq.mytype,modname.td, mytype(towords.typ + "erecord"))
    processtypedef(defined , undefined, i + 1, newundefined, map(other ,ph,ph,code2) )
 else 
  let td = undefined_i
   let k2 = subflddefined(subflds.td, parameter.modname.td, 1, defined, empty:seq.flddesc)
   if length.k2 = 0 then processtypedef(defined, undefined, i + 1, newundefined + undefined_i, other)
   else
    let modname = modname.td
    let syms = if kind.td="sequence"_1 then definesequence(other,  k2,  name.td, modname )
    else definerecord(other,  k2,  name.td, modname )
      let dd=if kind.td="sequence"_1 then
         myinternaltype(1,"defined"_1,name.td,modname,[mytype(towords.parameter.modname + "seq"_1)])
      else 
         myinternaltype(offset.last.k2+ size.last.k2,"defined"_1,name.td,modname,@(+,flatflds,empty:seq.mytype,k2))
   let descsym = placeholder([merge("type:" + print.mytype(towords.parameter.modname + name.td))],empty:seq.mytype, modname, 
    mytype."internaltype")
     processtypedef(defined + dd, undefined, i + 1, newundefined, map(syms,descsym,descsym,ascode.dd))

function processtypedef(defined:seq.myinternaltype, undefined:seq.myinternaltype, i:int, newundefined:seq.myinternaltype)seq.myinternaltype
 if i > length.undefined then
 if length.newundefined = 0 then defined
  else
    assert length.undefined > length.newundefined 
    report"ProBLEM" + @(seperator." &br",  name, "", newundefined)
    processtypedef(defined, newundefined, 1, empty:seq.myinternaltype)
 else if "T"_1 in towords.modname.undefined_i then 
    processtypedef(defined , undefined, i + 1, newundefined)
 else if kind.undefined_i in "defined encoding"  then
    processtypedef(defined + undefined_i, undefined, i + 1, newundefined)
 else
  let td = undefined_i
   let k2 = subflddefined(subflds.td, parameter.modname.td, 1, defined, empty:seq.flddesc)
   if length.k2 = 0 then processtypedef(defined, undefined, i + 1, newundefined + undefined_i)
   else
    let modname = modname.td
       let dd=if kind.td="sequence"_1 then
         myinternaltype(1,"defined"_1,name.td,modname,[mytype(towords.parameter.modname + "seq"_1)])
      else 
         myinternaltype(offset.last.k2+ size.last.k2,"defined"_1,name.td,modname,@(+,flatflds,empty:seq.mytype,k2))
     processtypedef(defined + dd, undefined, i + 1, newundefined )


type flddesc is record offset:int,fldno:int,description:myinternaltype, combined:mytype

function fldname(t:flddesc)word abstracttype.combined.t

function fldtype(t:flddesc)mytype parameter.combined.t

function flatflds(t:flddesc) seq.mytype subflds.description.t

function size(t:flddesc) int   size.description.t 
    
    use seq.myinternaltype
 
 function subflddefined(s:seq.mytype, T:mytype, i:int, defined:seq.myinternaltype, result:seq.flddesc)seq.flddesc
 // check to see all flds of type are defined. //
 if i > length.s then result
 else
  let next = s_i
  let fldtype=parameter.next
  let t = towords.fldtype
  let typ = if t_1 = "T"_1 then mytype(towords.T + subseq(t, 2, length.t))
  else fldtype
  let offset=if isempty.result then 0 else offset.last.result+size.last.result
   if abstracttype.typ in "word int seq"then
   subflddefined(s, T, i + 1, defined, result + flddesc(offset ,i,
    myinternaltype(1,"defined"_1,abstracttype.typ,mytype."defined",[typ]), next))
   else 
    let typdesc=lookuptype( defined,typ)
    if isempty.typdesc then empty:seq.flddesc
    else subflddefined(s, T, i + 1, defined, result + flddesc(offset,i,typdesc_1, next))
        
function         lookuptype(defined:seq.myinternaltype,typ:mytype) seq.myinternaltype
        findelement(    myinternaltype(0,"?"_1,abstracttype.typ,mytype(towords.parameter.typ+"?") ,empty:seq.mytype), defined)
  
        
  

function =(a:myinternaltype,b:myinternaltype) boolean 
   name.a=name.b &and  parameter.modname.a=parameter.modname.b


function isdefined(it:myinternaltype) boolean  size.it &ne 0 
    
function  ascode(it:myinternaltype) seq.sig
     [lit.size.it,wordsig.kind.it,wordsig.name.it,wordssig.towords.modname.it, lit.0,lit.length.subflds.it]
     +@(+,wordssig,empty:seq.sig,@(+,towords,empty:seq.seq.word,subflds.it))
     +RECORD(length.subflds.it+2)+RECORD.5
     
     use seq.fsignrep
     

function print(it:myinternaltype) seq.word
  [toword.size.it,kind.it,name.it]+print.modname.it+@(+,print,"",subflds.it)


  
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
     let newf=firstpass(modname.f, uses.f, defines.f, replace(exports.f ,x), unboundexports.f, unbound.f,types.f)
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
  let new = @(resolveexport.dict, identity, firstpass(modname.f, uses.f, defines.f, exports.f, empty:seq.symbol, unbound.f,types.f), unboundexports.f)
   replace(modset, new)

function resolveexport(dict:set.symbol, f:firstpass, s:symbol)firstpass
 let x = findelement2(dict, s)
  if cardinality.x = 1 then
  assert resulttype.x_1 = resulttype.s report"export return type missmatch" + print.s + print.x_1
    firstpass(modname.f, uses.f, defines.f, exports.f ∪ x, unboundexports.f, unbound.f,types.f)
  else
   firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + s, unbound.f,types.f)

function expanduse(acc:expanduseresult)expanduseresult
  let modset=firstpasses.acc
 let newset = @(expanduse2, identity,acc, toseq.asset.@(+, uses, empty:seq.mytype, toseq.modset))
  if cardinality.firstpasses.newset > cardinality.modset then expanduse.newset else acc 
  
type expanduseresult is record firstpasses:set.firstpass,map:seq.mapele

function expanduse2(acc:expanduseresult, use:mytype)expanduseresult
  let modset=firstpasses.acc
 let x = find(modset, use)
  if iscomplex.use ∧ not(parameter.use = mytype."T")then
  if isempty.x then
   let template = find(modset, mytype("T" + abstracttype.use))
     assert not.isempty.template report"Cannot find module" + print.use
     + @(+, print,"", @(+, modname, empty:seq.mytype, toseq.modset))
     let f=template_1 let with=parameter.use
   let defs=@(+, replaceTsymbol2.with, empty:seq.mapele, toseq.defines.f)
   let exps=@(+, replaceTsymbol2.with, empty:seq.mapele, toseq.exports.f)
   let unb=@(+, replaceTsymbol2.with, empty:seq.mapele, unboundexports.f)
     expanduseresult(modset+firstpass(replaceT(with, modname.f), @(+, replaceT.with, empty:seq.mytype, uses.f), 
     asset.@(+, s, empty:seq.symbol, defs), 
    asset.@(+, s, empty:seq.symbol, exps)
    , @(+, s, empty:seq.symbol, unb), 
     empty:set.symbol,@(+,replaceTmyinternaltype.with,empty:seq.myinternaltype,types.f))
     , map.acc+defs+exps+unb)
  else acc
  else
   assert not.isempty.x report"Cannot find module" + print.use
   + @(+, print,"", @(+, modname, empty:seq.mytype, toseq.modset))
   acc

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
    @(bind2(dict),identity,p,   toseq.defines.f)
    
    use seq.symboltext
       
function bind2(dict:set.symbol,p:prg,s:symbol) prg
  let ph=toplaceholder.s
  let txt=findencode(esymboltext,symboltext(ph,mytype."?","?"))
  if not.isempty.txt then 
       let  symsrc2=     text.txt_1
       let b = parse( dict , symsrc2)
       let cd=codex.b
       let src2= if subseq(symsrc2,length.symsrc2-2,length.symsrc2) ="builtin.usemangle" then
             let name = funcname.b
             let paratypes = funcparametertypes.b
             let code2=@(+, local,empty:seq.sig, arithseq(length.paratypes, 1, 1))+
               sig(name,paratypes,mytype."builtin",funcreturntype.b)
             @(+, topara,"", arithseq(length.paratypes , 1, 1)) + mangle(merge.name, mytype."builtin", paratypes )
            else    if cd_1 = "WORDS"_1  &and (  
               let l = toint.cd_2 + 3
               l ≤ length.cd ∧ cd_l = "builtinZinternal1Zwordzseq"_1) then
               subseq(cd, 1 + 2, toint.cd_2 + 2)
             else cd 
       map(p,ph,ph,  scannew(src2,1,empty:seq.sig))
    else  
       if  parameter.modname.s=mytype."T"  then
        map(p,ph,ph, empty:seq.sig ) else p           
 
 
    
function definesequence(other:prg,flds:seq.flddesc,  name:word, modname:mytype)prg
    let ptype = [ mytype.if parameter.modname = mytype.""then [ name]else"T" + name]
     let constructor2=@(+,confld,empty:seq.sig,flds)
   let paras=@(+,fldtype,empty:seq.mytype,flds) 
    let  symbols=@( fldsym(modname,ptype,length.flds,1), identity,other, flds)
   let indexfunc= placeholder("_", [mytype(towords.parameter.modname + name), mytype."int"], modname,parameter.modname) 
   let concode2=[FREFsig.indexfunc]+constructor2+RECORD.countflds(constructor2,1,1)
    let con =map(symbols, placeholder2([name],  paras,modname, mytype(towords.parameter.modname + name) ),concode2)
   let seqtype=mytype(towords.parameter.modname + "seq"_1)
   let symtoseq = map(con,placeholder2("toseq" ,  ptype,modname, seqtype),[local1])
   let symfromseq=map(symtoseq,placeholder2([merge("to:"+print.ptype_1)],[seqtype],modname,ptype_1),
    [local1,lit.0,IDXUC,FREFsig.indexfunc,eqOp,lit.2,lit.3,br,local1,exit,emptyseqOp,exit,block.3] )
       symfromseq 

function definerecord(other:prg, flds:seq.flddesc,  name:word, modname:mytype) prg
    let ptype = [ mytype.if parameter.modname = mytype.""then [ name]else"T" + name]
    let constructor2=@(+,confld,empty:seq.sig,flds)
  let paras=@(+,fldtype,empty:seq.mytype,flds) 
    let  symbols=@( fldsym(modname,ptype,length.flds,0),identity,other,flds)
   let concode2= if length.paras = 1 then[local1] else constructor2 + RECORD.countflds(constructor2,1,0)
   let con = placeholder2([name],  paras,modname, mytype(towords.parameter.modname + name) )
      map ( symbols , con ,con,concode2)
    
  
 
    function fldsym(modname:mytype,ptype:seq.mytype,noflds:int,offsetcorrection:int,p:prg,fld:flddesc) prg
       let offset=offset.fld+offsetcorrection
  let fldcode = if fldno.fld=1  ∧  noflds =1 then [local1]
  else if size.fld= 1 then [ local1, lit.offset ,  IDXUC ]
  else
   // should use a GEP instruction //
   //"LOCAL 1 LIT"+ toword.offset +"LIT"+ toword.tsize +"castZbuiltinZTzseqZintZint"//
   [ local1, lit(8 * offset) ,  plusOp] 
   let ph=placeholder2([fldname.fld],    ptype  , modname,fldtype.fld)
   map(p,ph,ph,fldcode)
   
 
      
 function    confld(fld:flddesc) seq.sig
     let tsize=size.fld
     if tsize = 1 then [local(fldno.fld)] else removeflat2(fldno.fld,tsize-1)
     

function  countflds(s:seq.sig,i:int,len:int) int
  if i > length.s then len else
   countflds(s,i+1, if islocal.s_i then len+1 else len)

  

use funcsig

use seq.sig



function topara(i:int)seq.word"LOCAL" + toword.i

type  lookR is record  isdefined:boolean ,code:seq.sig,ph:sig

   
function postbind(alltypes:seq.myinternaltype,templatemap: prg,dict:set.symbol,source :prg,working:set.sig,toprocess: seq.sig,i:int,result:prg) prg
  if i > length.toprocess then   result
  else
        let s=toprocess_i
        let w=working+s
        if  cardinality.w=cardinality.working then 
          postbind(alltypes,templatemap,dict,source,w,toprocess,i+1,result)
        else 
          let lr=lookupcode(source,s)
          assert not.isempty.lr report "KJHG"+print.s  
          let modname=mytype.module.decode.s
          if  modname = mytype."builtin" then 
             postbind(alltypes,templatemap,dict,source,w,toprocess,i+1,result)
          else 
           let r=postbind3(alltypes, dict,   code.lr_1, 1, empty:seq.sig,modname,print.s,templatemap,empty:set.sig,source)
           postbind(alltypes,templatemap,dict,source.r,w,toseq(calls.r-w)+subseq(toprocess,i+1,length.toprocess),1,
           if  length.toprocess=1 &and toprocess_1=placeholder("Wroot",empty:seq.mytype,mytype."W",mytype."int")    
           then result else  add(result,s,code.r))
 
     
type resultpb is record calls:set.sig,source:prg,code:seq.sig


 
function postbind3(alltypes:seq.myinternaltype,dict:set.symbol,code:seq.sig,
 i:int,result:seq.sig, modname:mytype,org:seq.word,templatemap:prg,calls:set.sig,source:prg)resultpb
 if i > length.code then  
 resultpb(calls , source,result)
 else if isplaceholder.code_i then
   let x=decode.code_i
   let s=if module.x="$fref" then  (constantcode.x)_1 else code_i
   let lr=lookupcode(source,s)
   if not.isempty.lr  then 
        let p2=if module.x="$fref" then  FREFsig.s else   s 
            postbind3( alltypes,dict,code, i+1, result+p2 , modname,org,templatemap,calls +s , source )
   else 
       let rep=decode.s
       let modpara=parameter.modname 
       let params2=   @(+, replaceT.modpara, empty:seq.mytype, paratypes.rep) 
       let z =X(alltypes,replaceT(modpara, mytype.module.rep),params2,s,name.rep,org,dict,source,templatemap)
         if place.z="C" then  
                    let ssss=lookupcode(source,ph.z) 
                    if not.isempty.ssss then 
                       let p2=if module.x="$fref" then  FREFsig.target.ssss_1 else   target.ssss_1 
                        postbind3(alltypes, dict,code, i+1, result+p2 , modname,org,templatemap,calls +target.ssss_1 , source)   
                      else 
                         let p2=if module.x="$fref" then  FREFsig.ph.z else   ph.z 
                        postbind3(alltypes, dict,code, i+1, result+p2 , modname,org,templatemap,calls +ph.z , add(source, ph.z,code.z ))
         else 
           let p2=if module.x="$fref" then  FREFsig.ph.z else   ph.z 
           postbind3(alltypes, dict,code, i+1, result+p2 , modname,org,templatemap,calls +ph.z , source)
 else
  postbind3(alltypes,dict,code,i+1,result+code_i,modname,org,templatemap,calls,source)
   

type resultpair is record ph:sig,code:seq.sig,place:seq.word
  
    
function X(alltypes:seq.myinternaltype,newmodname:mytype,params2:seq.mytype,s:sig,name:seq.word,org:seq.word, dict:set.symbol,   knownsymbols:prg,templatemap:prg)resultpair
   let templatename = abstracttype.newmodname
   let newmodpara = parameter.newmodname
      if name = "deepcopy" &and  templatename in "process"  then
               let type= params2_1
          resultpair( placeholder("deepcopy" ,  [type],mytype(towords.type + "process"), type),
         definedeepcopy(alltypes, type,org),"C")           
       else  if templatename in " process"  &and  merge.name  =   merge."sizeoftype:T"  then
                 let typeastext=print.newmodpara 
               let z = if typeastext = "int"then 1
                       else
                         let typdesc=lookuptype(alltypes,newmodpara)
                          assert  not.isempty.typdesc  report"can not find type sizeof" + typeastext + org
                         size.typdesc_1 
                    resultpair(  placeholder( name ,  empty:seq.mytype,newmodname, mytype."int"),[lit.z] ,"C")
    else     
     let f=lookupcode(templatemap,s) 
    if not.isempty.f then
        let rep2=decode.target.f_1
        resultpair(     placeholder( name ,  params2,newmodname, replaceT(newmodpara, mytype.returntype.rep2)),code.f_1,  "C" )
     else
        let m2=  placeholder( name ,  params2,newmodname, mytype."?")
        let sym10=if not (m2=s)then lookupcode(knownsymbols,m2) else f
        if not.isempty.sym10 then   resultpair(  target.sym10_1,code.sym10_1,"B" )
        else    
           let k = lookup(dict, [replaceTinname( newmodpara, merge.name)], params2)
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
                           X(alltypes, mytype.module.rep ,paratypes.rep,ph,name.rep, org, dict , knownsymbols,templatemap)
             else 
               resultpair(  ph,code.sym5_1,"D" )
           

Function headdict set.symbol
let modulename = mytype."internal1"
 asset
 .[ newsymbol("builtin", modulename, [ mytype."internal1"], mytype."internal" ), 
 newsymbol("builtin", modulename, [ mytype."word seq"], mytype."internal" ), 
  newsymbol("export", modulename, empty:seq.mytype, mytype."internal1" ), 
newsymbol("unbound", modulename, empty:seq.mytype, mytype."internal1" ), 
newsymbol("stub", modulename, empty:seq.mytype, mytype."internal1" ), 
newsymbol("usemangle", modulename, empty:seq.mytype, mytype."internal1" )]

function gathersymbols(input:seq.seq.word)firstpass
 @(wrapgathersymbols( headdict)
 , identity
 , firstpass(mytype."?", empty:seq.mytype, empty:set.symbol, empty:set.symbol, empty:seq.symbol, empty:set.symbol,empty:seq.myinternaltype)
 , input)

function wrapgathersymbols( stubdict:set.symbol, f:firstpass, input:seq.word)firstpass gathersymbols( stubdict, f, input)

function definefld( modname:mytype, t:seq.mytype, m:mytype)symbol 
newsymbol([abstracttype.m], modname, t, parameter.m)

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
  if length.input = 0 then 
  let k= defines.f &cap asset.unboundexports.f
   if isempty.k then f else
      firstpass(modname.f, uses.f , defines.f, 
      exports.f &cup k, toseq.(asset.unboundexports.f-k), unbound.f,types.f)
 else if input_1 in "use"then
 let t = parse(empty:set.symbol, subseq(input, 2, length.input))
   firstpass(modname.f, uses.f + (types.t)_1, defines.f, exports.f, unboundexports.f, unbound.f,types.f)
 else if input_1 in "type"then
 let b = parse(empty:set.symbol, input)
  let kind =input_4
  let name =input_2
   let t = mytype(towords.parameter.modname.f + name)
   if kind in "encoding"then
     assert parameter.modname.f = mytype.""report"encoding in template?"
     let typ = parameter.(types.b)_1
     let it=myinternaltype(0,kind,name,modname.f,types.b)
     let sym = newsymbol([name], modname.f, empty:seq.mytype, mytype(towords.typ + "erecord"))
       firstpass(modname.f, uses.f + mytype(towords.typ + "encoding"), defines.f + sym, exports.f, unboundexports.f, unbound.f,types.f+it)
   else
    assert parameter.modname.f in [ mytype."", mytype."T"]report"KLJKL"
    let it=myinternaltype(0,kind,name,modname.f,types.b)
    let sizeofsym = newsymbol( "type:" + print.t , modname.f, empty:seq.mytype, mytype."internaltype")
    let constructor = newsymbol([name], modname.f, @(+, parameter, empty:seq.mytype, types.b), t)
    let syms = @(+, definefld(modname.f, [ t]), [ constructor, sizeofsym], types.b)
    + if kind = "sequence"_1 then
      let seqtype=mytype(towords.parameter.t + "seq"_1)
    [ newsymbol("toseq ", modname.f, [ t], seqtype )     ,
       newsymbol( "to:"+print.t , modname.f, [ seqtype],t  )
    ]  
    else   empty:seq.symbol
     firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f,types.f+it)
 else if input_1 in "Function function"then
  let t = parse(stubdict, getheader.input)
  let name = funcname.t
  let paratypes = funcparametertypes.t
  assert iscomplex.modname.f = hasT(input, 2)report"Must use type T in function name or parameters in parameterized module and T cannot be used in non - parameterized module" + getheader.input
     let sym =  if subseq(input,length.input-2,length.input) ="builtin.usemangle" then
              newsymbol( name , mytype.if iscomplex.modname.f then"T builtin"else"builtin", paratypes, funcreturntype.t)
      else   newsymbol( name , modname.f, paratypes, funcreturntype.t)  
      if last.input in "export" then
       firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f,types.f)
      else if last.input in "unbound" then
       firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + sym,types.f)
      else
        assert not(sym in defines.f)report"Function" + name.sym + "is defined twice in module" + print.modname.f
        let discard= encode(esymboltext,symboltext(toplaceholder.sym,modname.f,input))
        firstpass(modname.f, uses.f, defines.f + sym, if input_1 = "Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f,types.f)
 else if input_1 in "module Module"then
 firstpass(mytype.if length.input > 2 then"T" + input_2 else [ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f,types.f)
 else f

   
function definedeepcopy(alltypes:seq.myinternaltype, type:mytype ,org:seq.word) seq.sig
  if abstracttype.type in "encoding int word"then [local1]
 else
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
     let typedesc=lookuptype(alltypes, type)
    assert  not.isempty.typedesc  report"can not find type deepcopy" + print.type +org
      let y=subfld(subflds.typedesc_1,1,empty:seq.sig)
    if last.y = RECORD.1 then
     // only one element in record so type is not represent by actual record //[local1]
      + subseq(y, 4, length.y - 1)
     else
      assert size.typedesc_1  ≠ 1 report"Err99a"
       y
  
   

function subfld(flds:seq.mytype,fldno:int,result:seq.sig) seq.sig
  if fldno > length.flds then result+[RECORD.length.flds]
  else let fldtype=flds_fldno
  let t=if abstracttype.fldtype in "encoding int word"then [ local1,lit.(fldno-1),IDXUC ]  
   else
    assert abstracttype.fldtype = "seq"_1 report"ERR99" + print.fldtype
     [ local1,lit.(fldno-1),IDXUC,placeholder("deepcopy",[fldtype],mytype."process",fldtype  )]
     subfld(flds,fldno+1,result+t) 

 
   
-------------------------


use seq.cached

use seq.expmod

use intercode
  
function  simplemods(exported:seq.word, f:firstpass) seq.expmod 
  if  not( abstracttype.modname.f in exported )   &or length.towords.modname.f &ne  1 then  empty:seq.expmod 
  else 
    let b2=@(+,   toplaceholder,empty:seq.sig,toseq.exports.f )
  [expmod(abstracttype.modname.f,b2,empty:seq.sig,empty:seq.mytype)]
   
    
function abstractmods(exported:seq.word,templatemap:prg, f:firstpass) seq.expmod
  if  not( abstracttype.modname.f in exported )  &or not.isabstract.modname.f then empty:seq.expmod  else 
     let defs=@(+,tosig.templatemap,empty:seq.sig,toseq.defines.f ) 
    let exp=@(+,tosig.templatemap ,empty:seq.sig,toseq.exports.f ) 
          [ expmod(abstracttype.modname.f,exp,defs,uses.f)]
       
   Function tosig(templatemap:prg, s:symbol) sig  
       let ph=toplaceholder.s
       let t=lookupcode(templatemap,ph)
       let code2=if isempty.t then empty:seq.sig else code.t_1
        sig58 (name.s , paratypes.s, modname.s , code2,resulttype.s)
   

 
 