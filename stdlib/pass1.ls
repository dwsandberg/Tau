Module pass1

run mylib testnew

use otherseq.firstpass

use process.firstpass

use seq.firstpass

use set.firstpass

use seq.flddesc

use blockseq.int

use libdesc

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

use seq.mapele

use  postbind 

 
 
 
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

type linkage is record   result:program,compiled:set.symbol,
roots:seq.symbol,mods:seq.firstpass,templates:program, alltypes:seq.myinternaltype

function result (linkage) program export

function compiled(linkage)seq.symbol export

function roots(linkage)seq.symbol export

function mods(linkage)seq.firstpass export

function templates(linkage) program export

Function alltypes(linkage) seq.myinternaltype export

Function type:linkage internaltype export

use seq.unboundexport 

use seq.liblib


Function pass1(allsrc:seq.seq.seq.word, exports:seq.word, libs:seq.liblib)linkage
   let librarymods=asset.libfirstpass.libs
   let alllibsym=@(&cup,defines, empty:set.symbol,toseq.librarymods) 
  // let discard=getinstance:encodingstate.symboltext //
  let a = @(+, gathersymbols, librarymods, allsrc)
  let expand1=expanduse.(expanduseresult(a,empty:seq.mapele))
  let u0=firstpasses.expand1
 // let u1=@(+,getunboundexport,empty:seq.unboundexport,toseq.u0)
   let d1=       resolveexport(u0,empty:set.symbol,mytype."1",u1,1,empty:seq.unboundexport)
  // let d1 = resolveunboundexports.u0 
  let allsymbols1=@(&cup,      defines,empty:set.symbol, toseq.d1)
  let alltypes = @(+,  types , empty:seq.myinternaltype,  toseq.d1)
   let librarysyms=libsymbols(alllibsym,libs)
    let c2 = processtypedef(empty:seq.myinternaltype, alltypes, 1, empty:seq.myinternaltype, librarysyms)
 let abstractsimple1=split(toseq.d1,1,empty:seq.firstpass,empty:seq.firstpass)
  let simple =  abstractsimple1_2  
  let abstract=abstractsimple1_1
   let c3= @( bind3(d1),identity,prg.c2,simple)
  let root=newsymbol("Wroot",mytype."W",empty:seq.mytype,mytype."int")
  let roots=@(+,roots.exports,  empty:seq.symbol ,simple )
  let source= map(c3,root,roots) 
  let temp33=@(mapabstracttype,identity,otherlibsyms(alllibsym,libs),alltypes)
  let temp34= @(bind3(d1),identity,   temp33,abstract)
  let templatemap=@( maptemp.temp34,identity,temp34,// toseq.allsymbols1 // map.expand1)
   let result=postbind(defined.c2,allsymbols1 ,empty:set.symbol, [ root],1,emptyprogram,source,templatemap)
    let compiled=(toset.librarysyms &cap toset.result)
  let result2= @( processOption,identity,result,@(+,identity,empty:seq.seq.word,allsrc) )
   linkage(result2,compiled, roots,simple+abstract ,templatemap,defined.c2)
 
   function   mapabstracttype(p:program,it:myinternaltype) program
       if towords.parameter.modname.it="T" then 
         let sym=newsymbol("type:" + print.mytype(towords.parameter.modname.it + name.it),modname.it,
           empty:seq.mytype, mytype."internaltype")
         map(p,sym,ascode.it)
       else p

        
   function  maptemp(templates:program,st:program,  s:mapele) program
                  let s2=lookupcode(templates,target.s)
                  if isdefined.s2 then
                      map (st,key.s, target.s,code.s2 )
                   else                     map (st,key.s, target.s,empty:seq.symbol)


function defineinternaltype(td:myinternaltype,k2:seq.flddesc) myinternaltype
   let modname = modname.td
        if kind.td="sequence"_1 then
          myinternaltype(1,"seq"_1,name.td,modname,[mytype(towords.parameter.modname + "seq"_1)])
      else if kind.td="encoding"_1 then
        myinternaltype(1,kind.td,name.td,modname,@(+,flatflds,empty:seq.mytype,k2))
       else 
         let flat=@(+,flatflds,empty:seq.mytype,k2)
         let def=if name.td="real"_1 then name.td else if flat=[mytype."int"] then "int"_1 
            else if length.flat=1 &and abstracttype.flat_1="seq"_1 then "seq"_1 
            else   if flat=[mytype."real"] then "real"_1 
            else "ptr"_1
         myinternaltype(offset.last.k2+ size.last.k2,def,name.td,modname,flat)

function print(f:flddesc)  seq.word 
"&br"+toword.offset.f +print.fldtype.f+toword.size.description.f

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
   if abstracttype.typ in "int seq real"then
   subflddefined(s, T, i + 1, defined, result + flddesc(offset ,i,
    myinternaltype(1, abstracttype.typ ,abstracttype.typ,mytype."defined",[typ]), next))
   else 
    let typdesc=lookuptype( defined,typ)
    if isempty.typdesc then empty:seq.flddesc
    else subflddefined(s, T, i + 1, defined, result + flddesc(offset,i,typdesc_1, next))
        
  
        
  

function =(a:myinternaltype,b:myinternaltype) boolean 
   name.a=name.b &and  parameter.modname.a=parameter.modname.b


function isdefined(it:myinternaltype) boolean  size.it &ne 0 

function  ascode(it:myinternaltype) seq.symbol
     [Lit.size.it,Word.kind.it,Word.name.it,Words.towords.modname.it, Lit.0,Lit.length.subflds.it]
     +@(+,Words,empty:seq.symbol,@(+,towords,empty:seq.seq.word,subflds.it))
     +Sequence(length.subflds.it,"ptr")+Record.[mytype."int",mytype."int",mytype."ptr",mytype."int",mytype."ptr"]
     


  
  
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
print.modname.x+print.unbound.x

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
 
     use seq.symboltext

 
function split(s:seq.firstpass,i:int,abstract:seq.firstpass,simple:seq.firstpass) seq.seq.firstpass
if i > length.s then [abstract,simple] else 
 let f=s_i
 if length.towords.modname.f = 1 ∧ length.uses.f > 0 then 
  split(s,i+1,abstract,simple+f)
 else if parameter.modname.f = mytype."T"then
  split(s,i+1,abstract+f,simple)
  else  split(s,i+1,abstract,simple)
         
 
 function bind3( modset:set.firstpass, p:program,  f:firstpass) program
   let dict = builddict(modset, f) ∪ headdict
    @(bind2(dict),identity,p,   toseq.defines.f)
    
       
function bind2(dict:set.symbol,p:program,s:symbol) program
   let txt=findencode(symboltext(s,mytype."?","?"))
  if not.isempty.txt then 
       let  symsrc2=     text.txt_1
       let b = parse( dict , symsrc2)
        if subseq(symsrc2,length.symsrc2-2,length.symsrc2) ="builtin.usemangle" then
              let code2=@(+, Local,empty:seq.symbol, arithseq(length.funcparametertypes.b, 1, 1))+
              symbol(fsig.s,if  length.module.s=1 then  "builtin" else  "T builtin",returntype.s)
            map(p,s,  code2)
         else 
            map(p,s, parsedcode.b)
    else  
     if  parameter.modname.s=mytype."T"  &and not(s in toset.p ) then
         map(p,s, empty:seq.symbol ) else p           
          
 
 type processtypedefresult is  record defined:seq.myinternaltype,prg:program 
 
 function processtypedef(defined:seq.myinternaltype, undefined:seq.myinternaltype, i:int, newundefined:seq.myinternaltype
 , other:program) processtypedefresult
 if i > length.undefined then
 if length.newundefined = 0 then processtypedefresult(defined,other)
  else
    assert length.undefined > length.newundefined 
    report"unresolved types:" + @(seperator." &br",  print2, "", newundefined)
     processtypedef(defined, newundefined, 1, empty:seq.myinternaltype, other)
 else if "T"_1 in towords.modname.undefined_i then 
    processtypedef(defined , undefined, i + 1, newundefined, other)
 else if kind.undefined_i in "int real seq address ptr encoding"  then
    processtypedef(defined + undefined_i, undefined, i + 1, newundefined, other)
 else 
  let td = undefined_i
   let k2 = subflddefined(subflds.td, parameter.modname.td, 1, defined, empty:seq.flddesc)
   if length.k2 = 0 then processtypedef(defined, undefined, i + 1, newundefined + undefined_i, other)
   else
    let modname = modname.td
    let dd=defineinternaltype(td,k2)
    let syms = if kind.td="sequence"_1 then definesequence(other,  k2,  name.td, modname,    @(+,flatflds,empty:seq.mytype,k2) )
    else definerecord(other,  k2,  name.td, modname,subflds.dd )
    let descsym = 
     newsymbol( "type:" + print.mytype(towords.parameter.modname + name.td) ,modname,empty:seq.mytype, 
    mytype."internaltype")
     processtypedef(defined + dd, undefined, i + 1, newundefined, map(syms,descsym,ascode.dd))

  function definesequence(other:program,flds:seq.flddesc,  name:word, modname:mytype,flatflds:seq.mytype)program
    let ptype = [ mytype.if parameter.modname = mytype.""then [ name]else towords.parameter.modname + name]
     let constructor2=buildconstructor(flds,flatflds,1,1,0,empty:seq.symbol)
    let paras=@(+,fldtype,empty:seq.mytype,flds) 
    let  symbols=@( fldsym(modname,ptype,length.flds,1), identity,other, flds)
   let indexfunc= newsymbol("_", modname, [mytype(towords.parameter.modname + name), mytype."int"],parameter.modname) 
   let concode2=[Fref.indexfunc]+constructor2+Record([mytype."int"]+  flatflds)  
    let con =map(symbols, newsymbol([name],modname,  paras, mytype(towords.parameter.modname + name) ),concode2)
   let seqtype=mytype(towords.parameter.modname + "seq"_1)
   let symtoseq = map(con,newsymbol("toseq" ,modname,  ptype, seqtype),[Local.1])
   let symfromseq=map(symtoseq,newsymbol( "to:"+print.ptype_1,modname ,[seqtype],ptype_1),
    [Local.1,Lit.0,Idx."int"_1,Fref.indexfunc,EqOp,Lit.2,Lit.3,Br,Local.1,Exit]+Emptyseq+[Exit,Block(mytype."ptr",3)] )
       symfromseq 

   
   function definerecord(other:program, flds:seq.flddesc,  name:word, modname:mytype,flatflds:seq.mytype) program
    let ptype = [ mytype.if parameter.modname = mytype.""then [ name]else"T" + name]
    let constructor2=buildconstructor(flds,flatflds,1,1,0,empty:seq.symbol)
     let paras=@(+,fldtype,empty:seq.mytype,flds) 
    let  symbols=@( fldsym(modname,ptype,length.flds,0),identity,other,flds)
   let concode2= if length.paras = 1 then 
   //     assert length.flatflds > 1 &or abstracttype(flatflds_1) in"seq int real"  report "HJK"+towords.flatflds_1 //
     [Local.1] else constructor2  + Record.flatflds
  let con = newsymbol([name],modname,  paras, mytype(towords.parameter.modname + name) )
      map ( symbols  ,con,concode2)

      
    function fldsym(modname:mytype,ptype:seq.mytype,noflds:int,offsetcorrection:int,p:program,fld:flddesc) program
       let offset=offset.fld+offsetcorrection
  let fldcode =   if fldno.fld=1  ∧  noflds =1 then [Local.1]
  else  if size.fld= 1 &or // this is a special case for access process result // fldname.fld="resultb"_1 &and abstracttype.modname="process"_1  then 
   [ Local.1, Lit.offset ,  Idx.kind.description.fld  ]
    else
   // should use a GEP instruction //
   [Local.1 ,Lit.offset,Lit.size.fld ,symbol("cast(T seq,int,int)","builtin","ptr") ]
   let sym= newsymbol([fldname.fld], modname,    ptype  ,fldtype.fld)
   map(p,sym,fldcode)
    
  
 function buildconstructor(  flds:seq.flddesc,flatflds:seq.mytype,fldno:int,j:int,subfld:int,result:seq.symbol)
 seq.symbol
   if j > length.flatflds then result else 
   let nextoffset=if length.flds > fldno then offset.flds_(fldno+1) else length.flatflds+1
   let newresult=result+if size.flds_fldno=1 then  [Local.fldno] else 
     [Local.fldno ,Lit.subfld, Idx.abstracttype.flatflds_j]
   if nextoffset=j then
       buildconstructor(flds,flatflds,fldno+1,j+1,0, newresult)
   else 
       buildconstructor(flds,flatflds,fldno,j+1,subfld+1, newresult)
 

 

      

Function headdict set.symbol
 asset
 .[ symbol("builtin(internal)", "headdict",   "internal1" ), 
  // symbol("builtin(word seq)", "headdict",    "internal" ), //
  symbol("export", "headdict",   "internal1" ), 
  symbol("unbound", "headdict",   "internal1" ), 
  symbol("stub", "headdict", "internal1" ), 
  symbol("usemangle", "headdict",   "internal" )]


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

 
type  symboltext is record ph:symbol,modname:mytype,text:seq.word


use encoding.symboltext

function hash(s:symboltext) int   hash(fsig.ph.s+module.ph.s)

function =(a:symboltext,b:symboltext) boolean ph.a=ph.b

function assignencoding(l:int, s:symboltext) int assignrandom(l,s)


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
    assert parameter.modname.f in [ mytype."", mytype."T"]report"KLJKL"
    let it=myinternaltype(0,kind,name,modname.f,types.b)
    let sizeofsym = newsymbol( "type:" + print.t , modname.f, empty:seq.mytype, mytype."internaltype")
    let constructor = newsymbol([name], modname.f, @(+, parameter, empty:seq.mytype, types.b), t)
    let syms = @(+, definefld(modname.f, [ t]), [ constructor, sizeofsym], types.b)
    + if kind = "sequence"_1 then
      let seqtype=mytype(towords.parameter.t + "seq"_1)
    [ newsymbol("toseq ", modname.f, [ t], seqtype )    
     ,      newsymbol( "to:"+print.t , modname.f, [ seqtype],t  )
    ]  
    else   empty:seq.symbol
     firstpass(modname.f, uses.f, defines.f ∪ asset.syms, exports.f, unboundexports.f, unbound.f,types.f+it)
 else if input_1 in "Function function"then
  let t = parse(stubdict, getheader.input)
  let name = funcname.t
  let paratypes = funcparametertypes.t
  assert iscomplex.modname.f = hasT(input, 2)report"Must use type T in function name or parameters in parameterized module and T cannot be used in non - parameterized module" + getheader.input
     let sym =  newsymbol( name , modname.f, paratypes, funcreturntype.t)  
      if last.input in "export" then
       firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f + sym, unbound.f,types.f)
      else if last.input in "unbound" then
       firstpass(modname.f, uses.f, defines.f, exports.f, unboundexports.f, unbound.f + sym,types.f)
      else
        assert not(sym in defines.f)report"Function" + name.sym + "is defined twice in module" + print.modname.f
        let discard= encode(symboltext(sym,modname.f,input))
        firstpass(modname.f, uses.f, defines.f + sym, if input_1 = "Function"_1 then exports.f + sym else exports.f, unboundexports.f, unbound.f,types.f)
 else if input_1 in "module Module"then
 firstpass(mytype.if length.input > 2 then"T" + input_2 else [ input_2], uses.f, defines.f, exports.f, unboundexports.f, unbound.f,types.f)
 else f

   

  
function roots(exported:seq.word,f:firstpass) seq.symbol
   if  not( abstracttype.modname.f in exported )   &or length.towords.modname.f &ne  1 then empty:seq.symbol 
   else toseq.exports.f
 

 
