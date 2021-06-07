Module symbolE

use symbol

use program

use seq.symbol

use standard

Function getCode(p:program, s:symbol) seq.symbol code.lookupcode(p,s)

Export type:program

Export emptyprogram program  

Export map(p:program, s:symbol, code:seq.symbol)program

Export typeboolean mytype

Export typereal mytype

Export typeint mytype

Export typeptr mytype

Export type:mytype

Export type:symbol

Export =(symbol,symbol) boolean

Export =(mytype,mytype) boolean

Export type:typedict

Export parameter(mytype) mytype

Export Lit(int) symbol

Export fsighash(symbol) int

Export hash(symbol) int

Export value(symbol) int

Export Sequence(mytype,int) symbol

Export Record(seq.mytype) symbol

Export paratypes(symbol) seq.mytype

Export print(symbol) seq.word

Export Constant2(seq.symbol) symbol

Export constantcode(symbol) seq.symbol


Export resulttype(symbol) mytype

Export Emptyseq(mytype) seq.symbol

 Export isstartorloop(symbol) boolean

Export islocal(symbol) boolean

Export isrecordconstant(symbol) boolean

Export isconst(symbol) boolean

Export isSequence(symbol) boolean

Export isRecord(symbol) boolean

Export isstart(symbol) boolean

Export iscontinue(symbol) boolean

Export isdefine(symbol) boolean

Export isFref(symbol) boolean


Export modname(symbol) mytype

Export isbr(symbol) boolean

Export isloopblock(symbol) boolean

Export firstvar(symbol) int


Export removeoptions(seq.symbol) seq.symbol

Export Exit symbol

Export EndBlock symbol

Export brt(s:symbol)int  

Export brf(s:symbol)int  


Export replaceTsymbol(mytype, symbol) symbol

 
Export abortsymbol(mytype) symbol

Export isabstract(m:modref) boolean 

 
Export nopara(symbol) int 

Export print(seq.symbol) seq.word


Export inmodule(sym:symbol,module:seq.word) boolean 

 
 

Export symbol3(module:modref,name:seq.word,p1:mytype,p2:mytype,p3:mytype,p4:mytype,rt:mytype) symbol
 
Export symbol3(module:modref,name:seq.word,p1:mytype,p2:mytype,p3:mytype,rt:mytype) symbol
 
Export symbol3(module:modref,name:seq.word,p1:mytype,p2:mytype,rt:mytype) symbol
 
Export symbol3(module:modref,name:seq.word,p1:mytype,rt:mytype) symbol
 
Export symbol3(module:modref,name:seq.word, rt:mytype) symbol
 
Export seqof(base:mytype) mytype   


 
Export typeref(  seq.word) mytype


Export moduleref(a:seq.word) modref

Export typebits mytype   

Export typebit mytype  

Export typebyte mytype  

Export typeword mytype  

Export typeT mytype  

Export isword(symbol) boolean

Export iswordseq(symbol) boolean

Export fldname(a:mytype) word    

Export fldtype(a:mytype) mytype  

Export abstracttypeof(a:mytype)  mytype  

Export addabstract(a:mytype,t:mytype) mytype  

Export Littrue symbol

Export Litfalse symbol

Export deepcopysym(set.symbol, mytype) set.symbol

Export lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol


Export lookupLocal(dict:set.symbol, name: seq.word)set.symbol 
 
Export isabstract(mytype) boolean

Export print(mytype) seq.word

Export isseq(mytype) boolean

Export Parameter(word, mytype, int) symbol

Export Local(seq.word, mytype) symbol

Export  Fref(symbol) symbol

Export moduleref(seq.word, mytype) modref 

Export symbol3(modref, seq.word, seq.mytype, mytype) symbol

Export symbol3(modref, seq.word, mytype) symbol

Export symbol4(modref, word, mytype, seq.mytype, mytype) symbol

Export type:modref


Export tomodref(m:mytype) modref

Export ifthenelse(seq.symbol, seq.symbol, seq.symbol, mytype) seq.symbol

Export NotOp  symbol

Export   Define(seq.word) symbol

Export  Words(seq.word) symbol

Export worddata(s:symbol) seq.word  

Export wordname(symbol)  word

Export getbasetype(typedict,mytype) mytype

Export print(program,symbol) seq.word

Export Optionsym symbol

 Export alltypes(compileinfo) typedict
 
 Export prg(compileinfo) program
 
 Export roots(compileinfo) seq.symbol
 
 Export toseq(program) seq.symbol 
 
 Export parameternumber(s:symbol) word
 
 Export packedtypes seq.mytype

Export isexit(symbol) boolean

Export isblock(symbol) boolean

Export module(symbol) modref

Export isparameter(symbol) boolean

Export type:compileinfo 

Export Local(int) symbol

Export getoption(seq.symbol) seq.word

Export para(modref) mytype


Export Define(int) symbol

Export Define(word) symbol

Export Local(word) symbol



Export isspecial(symbol) boolean

Export Br2(int, int) symbol

Export GetSeqLength symbol

Export GetSeqType symbol


Export PlusOp symbol

Export GtOp symbol

Export EqOp symbol


Export Loopblock(seq.mytype, int, mytype) symbol

Export continue(int) symbol

Export start(mytype)  symbol

Export seqeletype(mytype) mytype

Export isconstantorspecial(symbol) boolean

Export Word(word)  symbol

Export mangledname(s:symbol)word

Export internalmod modref 



Module program

use symbol 

use seq.symbol

use set.symbol

use words

use seq.mytype
 
use standard

use seq.myinternaltype

use set.word

Export type:programele

use seq.programele


Export type:program

type programele is data:seq.symbol

Function target(a:programele)symbol (data.a)_1

Function code(a:programele)seq.symbol subseq(data.a, 2, length.data.a)

Function isdefined(a:programele)boolean not.isempty.data.a

Function emptyprogram program program2.empty:set.symbol

type program is toset:set.symbol

Function ∪(p:program, a:program)program program(toset.p ∪ toset.a)

Function toseq(p:program)seq.symbol toseq.toset.p

Function ∈(s:symbol, p:program)boolean s ∈ toset.p

Function program2(a:set.symbol)program program.a

Function toseqprogramele(p:program)seq.programele
 for acc = empty:seq.programele, e = toseq.toset.p do acc + programele.zcode.e /for(acc)

Function lookupcode(p:program, s:symbol)programele
let t = findelement(s, toset.p)
 if isempty.t then programele.empty:seq.symbol else programele.zcode.t_1
 

Function map(p:program, s:symbol, target:symbol, code:seq.symbol)program
  program.replace(toset.p, addzcode (s, [ target] + code))

/type program is toset:set.symbol

/Function program2(a:set.symbol)program program(for(s ∈ toseq.a, acc = empty:hashset.symbol)acc + s)

/Function ∪(p:program, a:program)program program(tohashset.p ∪ tohashset.a)

/Function toseq(p:program)seq.symbol toseq.asset.toseq.tohashset.p

/Function ∈(s:symbol, p:program)boolean not.isempty.findelement(s, tohashset.p)

/Function lookupcode(p:program, s:symbol)programele let t = findelement(s, tohashset.p)if isempty.t then programele.empty:seq.symbol else programele.zcode.t_1

Function map(p:program, s:symbol, code:seq.symbol)program map(p, s, s, code)

Function addoption(p:program, s:symbol, option:seq.word)program
let code = code.lookupcode(p, s)
let current = asset.getoption.code
 if current = asset.option then p
 else
  let newcode = removeoptions.code + Words.toseq(current ∪ asset.option) + Optionsym
   map(p, s, newcode)
   
Function print(p:program, i:symbol)seq.word
let d = lookupcode(p, i)
 if not.isdefined.d then print.i
 else
  print.i + for acc ="", @e = code.d do acc + print.@e /for(acc)

Function printwithoutconstants(p:program, i:symbol)seq.word
let d = lookupcode(p, i)
 if not.isdefined.d then print.i
 else
  print.i
  + for acc ="", @e = removeconstant.code.d do acc + print.@e /for(acc)
  
Export type:firstpass

use mytype

type firstpass is module:modref, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unbound:set.symbol, types:seq.myinternaltype, prg:program

 
 
Export  firstpass(module:modref, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.myinternaltype, p:program)firstpass


Export module(f:firstpass) modref

 

Export defines(firstpass)set.symbol

Export exports(firstpass)set.symbol

Export uses(firstpass)seq.mytype

Export unboundexports(firstpass)seq.symbol

Export unbound(firstpass)set.symbol

Export types(firstpass)seq.myinternaltype

Export prg(firstpass)program

Function ?(a:firstpass, b:firstpass)ordering toalphaseq.print.module.a ? toalphaseq.print.module.b


type compileinfo is alltypes:typedict,prg:program,roots:seq.symbol 

Export compileinfo(alltypes:typedict,prg:program,roots:seq.symbol) compileinfo

Export alltypes(compileinfo)typedict

Export prg(compileinfo)program

Export roots(compileinfo) seq.symbol  

Export type:compileinfo 


Module symbol

use bits

use mytype

use standard

use seq.char

use seq.myinternaltype

use otherseq.mytype

use seq.mytype


use seq.symbol

use set.symbol

use encoding.symbolconstant

use otherseq.word

use set.word

use seq.seq.char

use otherseq.seq.word

use seq.seq.word

Export print(modref) seq.word

Export replaceT(mytype,modref) modref

Export type:symbol

Export typeint mytype

Export typeptr mytype

Export typeboolean mytype

Export typereal mytype

Export type:set.symbol

Export type:mytype

Export isabstract(a:mytype)boolean

Export parameter(m:mytype)mytype

Export print(p:mytype)seq.word

Export =(t:mytype, b:mytype)boolean

Export replaceT(with:mytype, m:mytype)mytype

Export iscomplex(a:mytype)boolean

Export   worddata(s:symbol) seq.word  




Function =(a:symbol, b:symbol)boolean
 flags.a = flags.b ∧ worddata.a = worddata.b ∧ (types.a >> 1= types.b >> 1) ∧ module.a = module.b
∧ issimplename.a = issimplename.b

Function =(a:modref,b:modref) boolean  name.a=name.b /and para.a=para.b

type symbol is worddata:seq.word, module:modref,   zcode:seq.symbol, flags:bits,types:seq.mytype

Export module(symbol) modref

Function moduleS(s:symbol) seq.word  
if issimple.module.s then [name.module.s] else oldTypeRep.para.module.s+name.module.s


function nameofmodule(a:symbol) word   name.module.a


Function modname(s:symbol) mytype   let m=module.s
 addabstract( typeref.[name.m,name.m,library.m],para.m)


Function fsighash(s:symbol)int toint(flags.s >> 4)

---internal

function extrabits2(types:seq.mytype,name:word,flags:bits) bits
 bits.hash( types >> 1,name) << 4 ∨ (flags /and 0x0F)


function extrabits(fsig:seq.word, flags:bits)bits bits.hash.fsig << 4 ∨ (flags /and 0x0F)


Function extrabits(s:symbol)int toint.flags.s

Function cleansymbol(sym:symbol,code:seq.symbol)symbol
 addzcode(sym,[ if isempty.zcode.sym then sym else addzcode( sym,  empty:seq.symbol)] + code)
 
 --- end internal
 
 Function wordname(s:symbol) word first.worddata.s
   
  
 
          
function fsig(name:word,nametype:seq.mytype,paratypes:seq.mytype) seq.word
  let fullname=if isempty.nametype then [name] else  [name]+":"+print.first.nametype 
   if length.paratypes=0 then fullname else
         for  acc= fullname+"(" ,t =paratypes do  acc+oldTypeRep.t +"," /for( acc >> 1 +")")
 
 
 Function checkwellformed(sym:symbol) boolean
     not.issimple.module.sym =
     for acc=false,t=types.sym while not.acc do  isabstract.t /for(acc)
   
 
function issimplename(sym:symbol) boolean (flags.sym /and simplenamebit) /ne 0x0 

Function paratypes(s:symbol)seq.mytype
if issimplename.s then  types.s >> 1 else  subseq(types.s,2,length.types.s-1)


Function resulttype(s:symbol)mytype  
  last.types.s 
  
Function nopara(s:symbol)int
 if isconst.s ∨ islocal.s ∨ isparameter.s then 0
 else if isspecial.s ∧ nameofmodule.s ∉ "$record $loopblock"then
  if   isdefine.s ∨ isbr.s /or isexit.s then 1
  else
   assert nameofmodule.s  /in "$continue $sequence " report "CHeKC"+print.s
    toint.wordname.s
 else 
  length.types.s-if issimplename.s then  1 else  2
  
 
Function ?(a:symbol, b:symbol)ordering
 fsighash.a ? fsighash.b ∧ worddata.a ? worddata.b ∧ (types.a >> 1)  ? (types.b  >> 1) 
  ∧ issimplename.a ? issimplename.b
 ∧ name.module.a ? name.module.b
 ∧ para.module.a ? para.module.b
 

Function ?2(a:symbol, b:symbol)ordering 
 fsighash.a ? fsighash.b ∧ worddata.a ? worddata.b ∧ (types.a >> 1) ? (types.b  >> 1)
 ∧ issimplename.a ? issimplename.b
 

--- internal

Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
  let sym=if length.name=1 then symbol3(internalmod,name,types,type?)
    else symbol4(internalmod,name_1,parsetype(name << 2),types,type?)
findelement2(dict, sym )

Function lookupsymbol(dict:set.symbol, sym:symbol)set.symbol
findelement2(dict, sym )


Function lookupLocal(dict:set.symbol, name: seq.word)set.symbol 
   lookup(dict,name,empty:seq.mytype)
   


Function printdict(s:set.symbol)seq.word
 for acc ="", @e = toseq.s do acc + print.@e /for(acc)



Function replaceTsymbol(with:mytype, s:symbol)symbol
 if with = typeT /or isconst.s then s
 else
     let newtypes=for acc=empty:seq.mytype, t= types.s do  acc+ replaceT(with,t) /for(acc)
    let newfsig2=fsig(wordname.s,if issimplename.s then empty:seq.mytype else [first.newtypes],
     if issimplename.s then newtypes >> 1 else subseq(newtypes,2,length.newtypes-1))
   symbol([wordname.s],   replaceT(with, module.s) , zcode.s,extrabits2(newtypes,wordname.s,flags.s),newtypes)

Function Words(s:seq.word)symbol symbol(s, moduleref."$words", empty:seq.symbol,extrabits(s,constbit)
,[seqof.typeword])

Function addzcode (s:symbol,zcode:seq.symbol) symbol
 symbol(worddata.s, module.s,  zcode, flags.s,types.s)

function symbolZ(module:modref, name:word,namePara:seq.mytype,paras:seq.mytype,rt:mytype,flag:bits) symbol
  let fsig=fsig(name,namePara,paras)
  symbol([name] ,   module ,  empty:seq.symbol, extrabits2(
    namePara+paras+rt ,name,
  if isempty.namePara  then simplenamebit /or flag else flag),
  namePara+paras+rt )
  
_______________________________

Function Parameter(name:word, type:mytype, parano:int)symbol
symbol3(moduleref("$parameter", addabstract( typeref.[toword.parano,"."_1,"."_1],type)),[name],empty:seq.mytype,type,specialbit)


Function parameternumber(s:symbol) word   
  abstracttype.para.module.s

Function isparameter(s:symbol)boolean
    nameofmodule.s = "$parameter"_1

Function istype(s:symbol)boolean 
 not.issimplename.s /and wordname.s="type"_1

Function Fld(offset:int,type:mytype) seq.symbol
  [Lit.offset,Idx.type]

Function Idx(type:mytype)symbol
let kind2=if isseq.type then  typeptr  else  type
 symbol3(moduleref("builtin",kind2),"load",[typeptr,typeint],kind2)
 

Function seqeletype(type:mytype)mytype
let para = parameter.type
  if para  ∈ [typeint ,typereal,typeboolean] then para
 else if para  ∈ [typebyte ,typebit ]then typeint  else typeptr
 

Function Record(types:seq.mytype)symbol
 symbol3(moduleref."$record","RECORD",types,typeptr,specialbit)
 
Function Sequence(eletype:mytype, length:int)symbol
symbol([toword.length],moduleref("$sequence", eletype),empty:seq.symbol,extrabits([toword.length],specialbit /or simplenamebit),[seqof.eletype])



symbol3(moduleref("$sequence", eletype),[toword.length],empty:seq.mytype,seqof.eletype ,specialbit)
  
Function continue(i:int)symbol 
symbol3(moduleref."$continue",[toword.i],empty:seq.mytype,type?,specialbit)


Function Constant2(args:seq.symbol)symbol
  addzcode(symbol3( moduleref."$constant", [toword.valueofencoding.encode.symbolconstant.args],empty:seq.mytype,typeptr,constbit)  ,args)
 
Function Emptyseq(type:mytype)seq.symbol [ Sequence(type, 0)]

Function isrecordconstant(s:symbol)boolean nameofmodule.s = first."$constant"

function hash(s:seq.symbol)int
 hash.for acc ="", e = s do acc + worddata.e + name.module.e /for(acc)

 
function assignencoding( p:seq.encodingpair.symbolconstant,a:symbolconstant)int   length.p +1


type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function isconstantorspecial(s:symbol)boolean isconst.s ∨ isspecial.s

function specialbit bits bits.4

function simplenamebit bits bits.2

function constbit bits bits.1

Function isspecial(s:symbol)boolean(flags.s ∧ specialbit) = specialbit

Function isconst(s:symbol)boolean(flags.s ∧ constbit) = constbit


Function isFref(s:symbol)boolean nameofmodule.s = first."$fref"


Function Exit symbol symbol3(moduleref."$exitblock","EXITBLOCK",empty:seq.mytype, type?,specialbit )


Function ifthenelse(c:seq.symbol, t:seq.symbol, e:seq.symbol, type:mytype)seq.symbol
 [ start.type] + c + Br2(1, 2) + t + Exit + e + Exit
 + EndBlock

Function Br2(t:int, f:int)symbol
 symbolZ(moduleref("$br"),"BR2"_1, [TypeFromOldTyperep([toword.f,toword.t])],empty:seq.mytype,type?,specialbit)

 
Function start(t:mytype)symbol symbol3(moduleref("$loopblock",t),"/start",empty:seq.mytype,t, specialbit)

Function EndBlock symbol symbol3(moduleref."$block","BLOCK",empty:seq.mytype,typeint, specialbit)

Function isstartorloop(sym:symbol)boolean nameofmodule.sym ∈ "$loopblock"

Function isstart(sym:symbol)boolean
 nameofmodule.sym  = "$loopblock"_1 ∧  wordname.sym  ≠ "LOOPBLOCK"_1


Function isloopblock(s:symbol)boolean
 nameofmodule.s = "$loopblock"_1 ∧ wordname.s = "LOOPBLOCK"_1

Function Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype)symbol
 symbol4(moduleref( "$loopblock",resulttype),"LOOPBLOCK"_1,TypeFromOldTyperep.[toword.firstvar],types,resulttype )

Function firstvar(a:symbol)int toint.abstracttype.first.types.a

Function brt(s:symbol)int toint.abstracttype.first.types.s

Function brf(s:symbol)int toint.abstracttype.parameter.first.types.s

Function Local(i:int)symbol Local.toword.i

Function Local(w:word)symbol Local([w],typeint)

Function Local(name:seq.word, type:mytype)symbol symbol3(moduleref."$local",name,  empty:seq.mytype,type, specialbit)

Function islocal(s:symbol)boolean inmodule(s,"$local ")

Function Reallit(i:int)symbol symbol3(moduleref."$real",[toword.i],empty:seq.mytype,typereal,constbit)

Function Lit(i:int)symbol symbol3(moduleref."$int",[toword.i],empty:seq.mytype,typeint,constbit)

Function Littrue symbol  
symbol3(moduleref."standard","true" ,empty:seq.mytype,typeboolean, constbit)

Function Litfalse symbol symbol3(moduleref."standard","false" ,empty:seq.mytype,typeboolean, constbit)



Function Word(s:word)symbol symbol3( moduleref."$word",[ s],empty:seq.mytype, typeword, constbit)

Function Define(s:seq.word)symbol Define.s_1

Function Define(w:word)symbol symbol3(moduleref."$define", [w] ,empty:seq.mytype,  type? , specialbit)

 
Function Define(w:int)symbol Define.toword.w

Function Fref(s:symbol)symbol
addzcode(symbol3(moduleref."$fref",[merge("FREF" + fsig(wordname.s,nametype.s,paratypes.s) 
+ print.s)],empty:seq.mytype,type?,constbit)
,[s])

 
 Function type? mytype  typeref( "? internal .") 

Function Optionsym symbol 
 symbol3(internalmod,"option",typeint,seqof.typeword,type?)

Function EqOp symbol  symbol3(moduleref."standard","=", typeint, typeint, typeboolean)

Function GtOp symbol  symbol3(moduleref."standard",">", typeint, typeint, typeboolean)

Function NotOp symbol  symbol3(moduleref."standard","not", typeboolean, typeboolean)

Function PlusOp symbol  symbol3(moduleref."standard","+", typeint, typeint, typeint)

Function MultOp symbol  symbol3(moduleref."standard","*", typeint, typeint, typeint)


Function GetSeqLength symbol symbol3(moduleref."tausupport","getseqlength",typeptr,typeint)

 
Function GetSeqType symbol symbol3(moduleref."tausupport","getseqtype",typeptr,typeint)

 

Function abortsymbol(typ:mytype) symbol 
let a=if isseq.typ     then typeptr else  typ
replaceTsymbol(a,symbol4(moduleref."tausupport","abort"_1,typeT,[seqof.typeword],typeT))
  

Function isblock(s:symbol)boolean nameofmodule.s = "$block"_1

Function isRecord(s:symbol)boolean nameofmodule.s = first."$record"

Function isSequence(s:symbol)boolean nameofmodule.s = "$sequence"_1

Function iscontinue(s:symbol)boolean nameofmodule.s = first."$continue"

Function isdefine(s:symbol)boolean nameofmodule.s = first."$define"

Function isexit(s:symbol)boolean nameofmodule.s = first."$exitblock"

Function isword(s:symbol)boolean nameofmodule.s = first."$word"

Function iswordseq(s:symbol) boolean nameofmodule.s = first."$words"

Function isbr(s:symbol)boolean nameofmodule.s = first."$br"

Function value(s:symbol)int toint.wordname.s

Function constantcode(s:symbol)seq.symbol
 if isFref.s then zcode.s
 else if isrecordconstant.s then
  if isSequence.last.zcode.s then
   [ Lit.0, Lit.nopara.last.zcode.s] + zcode.s >> 1
  else zcode.s >> 1
 else empty:seq.symbol

Function basesym(s:symbol)symbol if nameofmodule.s = first."$fref"then(zcode.s)_1 else s

Function getoption(code:seq.symbol)seq.word
 if isempty.code ∨ last.code ≠ Optionsym then empty:seq.word else worddata.code_(length.code - 1)

Function removeoptions(code:seq.symbol)seq.symbol
 if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)
 else code
 

 
Export typeref( typ:seq.word) mytype  
 

Export moduleref( seq.word,para:mytype) modref
 
  
Export moduleref( seq.word) modref
    
Export addabstract(a:mytype,t:mytype) mytype   



 
Function typebits mytype  typeref( "bits bits.")

Function typebit mytype typeref(  "bit bits.")

Function typebyte mytype typeref( "byte bits.")

Function typeword mytype typeref( "word words.")

Export typeT mytype  

  
  
Function seqof(base:mytype) mytype  addabstract(typeref( "seq seq ."),base)


Function mangledname(s:symbol)word mangle(fsig(wordname.s,nametype.s,paratypes.s), moduleS.s)


------

Function hash(s:symbol)int toint(flags.s >> 4)


type typedict is data:seq.myinternaltype

Function +(a:typedict, b:seq.myinternaltype)typedict typedict(data.a + b)

Function print(t:typedict)seq.word
 for acc ="", e = data.t do list(acc," /br", print3.e)/for(acc)

type myinternaltype is kind:word, name:word, module:modref, subflds:seq.mytype

Export type:myinternaltype

Export kind(myinternaltype)word

Export name(myinternaltype)word

Function isdefined(it:myinternaltype)boolean kind.it = "defined"_1

Function typekind(t:myinternaltype)word kind.t

Function modpara(t:myinternaltype)mytype para.module.t

Export subflds(myinternaltype)seq.mytype

function =(a:myinternaltype, b:myinternaltype)boolean
 name.a = name.b ∧ para.module.a = para.module.b

Function changesubflds(t:myinternaltype, subflds:seq.mytype)myinternaltype 
myinternaltype("defined"_1, name.t, module.t, subflds)


Export module(m: myinternaltype) modref  

 
Export myinternaltype(kind:word, name:word, module:modref, subflds:seq.mytype)myinternaltype
  
  
Function replaceTmyinternaltype(with:mytype, it:myinternaltype)myinternaltype 
myinternaltype(kind.it, name.it, replaceT(with, module.it), subflds.it)

Function tomyinternaltype(s:seq.word)myinternaltype
let t = parseit(s, 1, [ s_1], empty:seq.seq.word)
 myinternaltype(t_2_1, t_3_1, tomodref.TypeFromOldTyperep.t_4, 
 for acc = empty:seq.mytype, e = subseq(t, 5, length.t)do acc + TypeFromOldTyperep.e /for(acc))

function parseit(s:seq.word, i:int, fld:seq.word, flds:seq.seq.word)seq.seq.word
 if i > length.s then flds + fld
 else if s_i = "."_1 then
  parseit(s, i + 2, [ s_(i + 1)] + fld, flds)
 else { end of fld } parseit(s, i + 1, [ s_i], flds + fld)

Function print3(it:myinternaltype)seq.word
 if not.isdefined.it then
  "module:" + print.module.it + "type" + name.it + "is"
  + kind.it
  + for acc ="", e = subflds.it do list(acc,",", printfld.e)/for(acc)
 else
  [ kind.it, name.it] + print.module.it
  + for acc ="", e = subflds.it do acc + print.e /for(acc)

function printfld(f:mytype)seq.word [ fldname.f,":"_1] + print.parameter.f


Export moduleS(symbol)seq.word

Export type:symbol

Export zcode(symbol)seq.symbol

Export isabstract(m:modref) boolean 

Function print(f:symbol)seq.word
let module = nameofmodule.f
 if islocal.f ∨ isparameter.f then [ merge(["%"_1] + wordname.f)]
 else if module  /in "$int $real" then worddata.f
 else if module /in "$words"then
  if '"'_1 ∈ worddata.f then"'" + worddata.f + "'"
  else '"' + worddata.f + '"'
 else if module /in "$word"then"WORD" + wordname.f
 else if isrecordconstant.f then [wordname.f]
 else if isFref.f then"FREF" + print.(constantcode.f)_1
 else if not.isspecial.f /or isloopblock.f  then
    let fullname=if issimplename.f then [wordname.f] else  [wordname.f]+":"+print.first.types.f 
    for  acc= fullname+"(" ,t =paratypes.f do  acc+oldTypeRep.t +"," /for( acc >> 1 +")"+ print.module.f
    +if isloopblock.f  then "/br" else "" )
 else 
  if isdefine.f then "DEFINE"+wordname.f
  else if isstart.f then
   "/start" + "(" + print.resulttype.f + ") /br"
  else if isblock.f   then"EndBlock  /br"
  else if isexit.f      then"Exit  /br"
  else if isbr.f then
   "Br2(" + toword.brt.f + "," + toword.brf.f + ") /br"
   else if iscontinue.f then "CONTINUE"+wordname.f + " /br"
  else 
   fsig(wordname.f,nametype.f,paratypes.f)
  
   function nametype(sym:symbol) seq.mytype 
    if issimplename.sym then empty:seq.mytype else [first.types.sym] 
 
  

Function findelement(d:typedict, type:mytype)seq.myinternaltype
 findelement(myinternaltype("?"_1, abstracttype.type,    moduleref("?", parameter.type) , empty:seq.mytype), data.d)

Export typedict(seq.myinternaltype)typedict

Export type:typedict


Function getbasetype(d:typedict,intype:mytype) mytype
{ base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.bit 
   seq.packed2 seq.packed3 seq.packed4 seq.packed5 seq.packed6 or $base.x where x is a integer}
  if abstracttypeof.intype = typeref ( "$base $base .") then { used for type of next in for expression } intype
 else
  let isseq =  isseq.intype 
  let type= if isseq then parameter.intype else intype
  if  type ∈ packedtypes then 
     if isseq then intype else typeptr
  else  if  type ∈ [typeint, typeboolean ,typereal, typeptr]then 
     if isseq then intype else type
  else if  type   ∈ [ typebit, typebyte ] then 
    if isseq then  intype else typeint
  else if isseq.type  /and isseq then seqof.typeptr
  else 
   let t = findelement(d, type)
   assert length.t = 1 report"type not found" + print.type + stacktrace
   let size = length.subflds.t_1
     if size > 1 then
     if not.isseq then typeptr
     else if size = 2 then seqof.typeref(  "packed2 tausupport .")
     else if size = 3 then seqof.typeref(  "packed3  tausupport .")
     else if size = 4 then seqof.typeref(  "packed4  tausupport .")
     else if size = 5 then seqof.typeref(  "packed5  tausupport .")
     else if size = 6 then seqof.typeref(  "packed6  tausupport .")  
     else seqof.typeptr
    else
     let basetype =(subflds.t_1)_1
      if isseq.basetype   /and isseq  then seqof.typeptr
      else let basetype2=getbasetype(d,basetype)
         if not.isseq then basetype2
         else    if isseq.basetype2     then seqof.typeptr
         else seqof.basetype2 
         
Function packedtypes seq.mytype [
typeref(  "packed2 tausupport .")
,typeref(  "packed3 tausupport .")
,typeref(  "packed4 tausupport .")
,typeref(  "packed5 tausupport .")
,typeref(  "packed6 tausupport .")
 ]
         
 

Function getsubflds(d:typedict, type:mytype)seq.mytype
 if type = typeint ∨ type = typereal ∨ type = typeptr then [ type]
 else
  { if type = typeboolean then typeinfo.[ typeboolean]else }
  if isseq.type   then  [ typeptr]
  else
   let t = findelement(d, type)
    assert length.t = 1 report"type not found" + print.type + stacktrace
     subflds.t_1

Function buildargcode(alltypes:typedict, sym:symbol)int
 { needed because the call interface implementation for reals is different than other types is some implementations }
 for acc = 1, typ = paratypes.sym + resulttype.sym do
  acc * 2
  + if getbasetype(alltypes, typ) = typereal then 1 else 0
 /for(acc)

Function typesym(it:myinternaltype)symbol
let t = addabstract(typeref3(module.it, name.it ), para.module.it)
       symbol4(module.it,"type"_1 ,t  ,   [ t], t)

Function deepcopysym(d:typedict, type:mytype)symbol typesym(d, type)

Function typesym(d:typedict, type:mytype)symbol
 if type = typeint then symbol3(moduleref."tausupport", "deepcopy ",typeint,typeint)
 else if type = typereal then symbol3(moduleref."tausupport", "deepcopy ",typereal,typereal)
 else
  let e = findelement(d, type)
   assert length.e = 1 report"type not found" + print.type + stacktrace
   let it = e_1
   let t = addabstract(typeref3(module.it, name.it ), para.module.it)
        symbol4(module.it,"type"_1 ,t  ,   [ t], t)

   
Function deepcopysym(dict:set.symbol, type:mytype)set.symbol
 if type ∈ [ typeint, typereal]then asset.[ typesym(typedict.empty:seq.myinternaltype, type)]
 else lookup(dict,"type:" + print.type, [ type])

Function removeconstant(s:seq.symbol)seq.symbol
 for acc = empty:seq.symbol, @e = s do
  acc + if isrecordconstant.@e then removeconstant.zcode.@e else [ @e]
 /for(acc)

_______________________________________________

Function print(s:seq.symbol)seq.word
 for acc ="", e = s do
  acc +  print.e
 /for(acc)



__________

Export type:modref

Export issimple(m:modref)boolean     

Export para(modref) mytype


Export tomodref(m:mytype) modref

Export name(modref) word

  
 Function symbol3(module:modref,name:seq.word, paras:seq.mytype, rt:mytype) symbol
      symbol3(module,name,paras,rt,0x0)
  
function symbol3(module:modref,name:seq.word, paras:seq.mytype, rt:mytype,flags:bits) symbol
    symbolZ(module,name_1,empty:seq.mytype,paras,rt, flags)
 


Function symbol4(module:modref, name:word,namePara:mytype,paras:seq.mytype,rt:mytype) symbol
   symbolZ(module,name,[namePara],paras,rt,if name /in "LOOPBLOCK" then specialbit else 0x0)
  
 

 
Function symbol3(module:modref,name:seq.word,p1:mytype,p2:mytype,p3:mytype,p4:mytype,rt:mytype) symbol
  symbol3( module, name,[p1,p2,p3,p4],rt)

Function symbol3(module:modref,name:seq.word,p1:mytype,p2:mytype,p3:mytype,rt:mytype) symbol
  symbol3( module, name,[p1,p2,p3],rt)

Function symbol3(module:modref,name:seq.word,p1:mytype,p2:mytype ,rt:mytype) symbol
  symbol3( module, name,[p1,p2 ],rt)

Function symbol3(module:modref,name:seq.word,p1:mytype,rt:mytype) symbol
 symbol3( module, name,[p1],rt)

Function symbol3(module:modref,name:seq.word, rt:mytype) symbol
   symbol3( module, name,empty:seq.mytype,rt)

Function inmodule(sym:symbol,module:seq.word) boolean nameofmodule.sym= first.module

Function symboladdword symbol 
let seqchar=seqof.typeref("char UTF8 .") 
let state=addabstract(typeref."encodingstate encoding . ",seqof.seqchar)
symbol3(moduleref("encoding",seqchar ),"add",
[state , addabstract(typeref."encodingpair encoding . ",seqof.seqchar)],state)

 

Function abortedsymbol symbol symbol3(moduleref."builtin","aborted",[ addabstract(typeref."process process . ",typeT)],typeboolean)



Export isseq(a:mytype) boolean    

Export isencoding(a:mytype) boolean  

Function fldname(a:mytype) word   abstracttype.a

Function fldtype(a:mytype) mytype parameter.a 

Export  abstracttypeof(a:mytype)  mytype  

Export internalmod modref

use words



Function typeinname(a:seq.word) seq.mytype
if length.a = 1 then empty:seq.mytype
else 
 assert a_2 /in ":" report "typeiname format problem"
 for   r=""  , w =a << 2  while w /nin "("  do
    if w /in "." then r else [w]+ r
 /for ( [TypeFromOldTyperep.r])

use encoding.symbol

use mangle

function assignencoding(a:seq.encodingpair.symbol, symbol) int length.a+1

Export isabstract(m:modref) boolean 

Export  TypeFromOldTyperep(m:seq.word)  mytype  

Export isabstract(m:modref)boolean

Export types(symbol) seq.mytype

___________________________________________________________

module hashset.T

use bits

use standard

use seq.T

use otherseq.seq.T

use seq.seq.T

type hashset is table:seq.seq.T, cardinality:int, mask:bits

unbound hash(T)int

unbound =(T, T)boolean

Function ∪(a:hashset.T, b:hashset.T)hashset.T
 if cardinality.b > cardinality.a then b ∪ a
 else for acc = a, e = toseq.b do acc + e /for(acc)

function clean(s:seq.T, mask:bits, idx:int)seq.T
let currenthash = tobits(idx - 1)
 for acc = empty:seq.T, e = s do
  if e ∈ acc ∨ (tobits.hash.e ∧ mask) ≠ currenthash then acc else acc + e
 /for(acc)

Function +(s:hashset.T, a:T)hashset.T
let idx = toint(tobits.hash.a ∧ mask.s) + 1
 assert between(idx, 1, length.table.s)report"XXX" + print.idx + print.length.table.s + print.mask.s
 let list =(table.s)_idx
 let t = replace(table.s, idx, clean([ a] + list, mask.s, idx))
  assert not.isempty.clean([ a] + list, mask.s, idx)report"XX"
   if a ∈ list then hashset(t, cardinality.s, mask.s)
   else
    let newmask = bits.-1 >> (64 - floorlog2((cardinality.s + 1) * 3 / 2))
     if toint.newmask ≤ toint.mask.s then hashset(t, cardinality.s + 1, mask.s)
     else hashset(t + t, cardinality.s + 1, mask.s << 1 ∨ 0x1)

Function findelement(ele:T, s:hashset.T)seq.T
let idx = toint(tobits.hash.ele ∧ mask.s) + 1
 findelement(ele,(table.s)_idx)

Function toseq(s:hashset.T)seq.T
 for acc = empty:seq.T, idx = 1, e = table.s do
  next(acc + clean(e, mask.s, idx), idx + 1)
 /for(acc)

Function empty:hashset.T hashset.T hashset([ empty:seq.T, empty:seq.T, empty:seq.T, empty:seq.T], 0, 0x3)

Export type:hashset.T

Export cardinality(hashset.T)int


