
Module symbol

use seq.typedef

use bits

use mytype

use standard

use seq.char


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

Export isabstract(m:mytype)boolean

Export parameter(mytype)mytype

Export print(p:mytype)seq.word

Export =(t:mytype, b:mytype)boolean

Export replaceT(with:mytype, m:mytype)mytype

Export iscomplex(a:mytype)boolean

Export   worddata(s:symbol) seq.word  

Export =(a:modref,b:modref) boolean   

---internal

type symbol is worddata:seq.word, module:modref,types:seq.mytype, raw:bits,hashbits:bits, zcode:seq.symbol

Export type:symbol

Export worddata(symbol) seq.word

Export module(symbol)modref

Export types(symbol)seq.mytype

Export raw(symbol)bits

Export zcode(symbol) seq.symbol

Function =(a:symbol, b:symbol)boolean
 hashbits.a = hashbits.b ∧ worddata.a = worddata.b ∧ (types.a >> 1= types.b >> 1) 
 ∧ issimplename.a = issimplename.b
 ∧ module.a = module.b

 /and (name.module.a /nin "$fref"  /or zcode.a=zcode.b)

Function ?(a:symbol, b:symbol)ordering
 fsighash.a ? fsighash.b ∧ worddata.a ? worddata.b ∧ (types.a >> 1)  ? (types.b  >> 1) 
  ∧ issimplename.a ? issimplename.b
 ∧ module.a ? module.b
 
Function ?2(a:symbol, b:symbol)ordering 
 fsighash.a ? fsighash.b ∧ worddata.a ? worddata.b ∧ (types.a >> 1) ? (types.b  >> 1)
 ∧ issimplename.a ? issimplename.b

function extrabits(types:seq.mytype,other:int,flags:bits) bits
 bits.hash( types ,other) << 4 ∨ (flags /and 0x0F)
 
Function extrabits(s:symbol)int toint.hashbits.s

Function Words(s:seq.word)symbol 
symbol(s, moduleref."$words",[ typeptr],0x0,extrabits(empty:seq.mytype,hash.s,constbit), empty:seq.symbol)

function specialbit bits bits.4

function simplenamebit bits bits.2

function constbit bits bits.1

Function issimplename(sym:symbol) boolean (hashbits.sym /and simplenamebit) /ne 0x0 

Function isspecial(s:symbol)boolean(hashbits.s ∧ specialbit) = specialbit

Function isconst(s:symbol)boolean(hashbits.s ∧ constbit) = constbit

Function isunbound(sym:symbol)boolean (raw.sym /and unboundbit) /ne 0x0

function unboundbit bits  0x1 << 41

function requiresbit bits  0x1 << 42

Function hasrequires(sym:symbol)boolean (raw.sym /and requiresbit) /ne 0x0

Function hash(sym:symbol)int toint(hashbits.sym >> 4)

Function fsighash(s:symbol)int toint(hashbits.s >> 4)

Function setunbound(sym:symbol) symbol
  symbol( worddata.sym,module.sym,types.sym,raw.sym /or unboundbit,hashbits.sym,empty:seq.symbol) 

Function setrequires(sym:symbol)symbol 
 symbol( worddata.sym,module.sym,types.sym,raw.sym /or requiresbit,hashbits.sym,empty:seq.symbol) 

Function addzcode (s:symbol,zcode:seq.symbol) symbol
 symbol(worddata.s, module.s,types.s, raw.s,hashbits.s,  zcode)

Function replaceTsymbol(with:mytype, sym:symbol)symbol
 if with = typeT /or isconst.sym then sym else
let newtypes = for newtypes = empty:seq.mytype, t = types.sym do newtypes + replaceT(with, t)/for(newtypes)
 let adjustedraw={if isunbound.sym then
      for hasT=false ,t=newtypes while not.hasT do  isabstract.t /for(
       if hasT then raw.sym else   raw.sym   /and xor(unboundbit,tobits.-1)  )
    else} raw.sym
symbol( worddata.sym,replaceT(with, module.sym), newtypes, adjustedraw,extrabits(newtypes,   hash.worddata.sym,hashbits.sym),empty:seq.symbol)

function symbolZ(module:modref, name:word,namePara:seq.mytype,paras:seq.mytype,rt:mytype,flags:bits,raw:bits) symbol
   let types=namePara+paras+rt
  symbol([name] ,   module , types,raw
  , extrabits( types ,hash.[name],
  if isempty.namePara  then simplenamebit /or flags else flags),  empty:seq.symbol )
  
Function Br2(t:int, f:int)symbol
 let raw=bits.t << 20 ∨ bits.f
 symbolZ(moduleref("$br"),"BR2"_1, 
  [ typeref([ toword.toint.raw,"."_1,"."_1])  ]
  ,empty:seq.mytype,type?,specialbit,bits.t << 20 ∨ bits.f)

Function brt(s:symbol)int toint(raw.s >> 20 ∧ 0xFFFFF)

Function brf(s:symbol)int toint(raw.s ∧ 0xFFFFF)

Function type? mytype  typeref( "? internal .") 

Function printrep(s :symbol) seq.word
    if name.module.s = "$int"_1 then [ name.s]
    else   if iswords.s then   '"'+ worddata.s+'"' 
    else 
     "("+[library.module.s,name.module.s]+ printrep.para.module.s
    +name.s+toword.toint.raw.s 
    +for acc = "", t =  types.s   do
     acc + printrep.t  
    /for(acc   + ")")/if

Function name(sym:symbol) word first.worddata.sym 


Function iswords(s:symbol)boolean name.module.s ∈ "$words"

Function islocal(s:symbol)boolean name.module.s ∈ "$local " 

Function isdefine(s:symbol)boolean name.module.s ∈ "$define"

Function isbr(s:symbol)boolean name.module.s ∈ "$br"

Function isexit(s:symbol)boolean name.module.s ∈ "$exitblock"


Function value(sym:symbol)int toint.raw.sym

Function nopara(s:symbol)int
 if isconst.s ∨ islocal.s   then 0
 else if isspecial.s ∧ name.module.s ∉ "$record $loopblock"then
  if   isdefine.s ∨ isbr.s /or isexit.s then 1
  else
  { assert name.module.s  /in "$continue $sequence " report "CHeKC"+print.s}
    toint.name.s
 else 
  length.types.s-if issimplename.s then  1 else  2

Export raw(symbol) bits

Export type:symbol

Export worddata(symbol) seq.word

Export module(symbol)modref

Export types(symbol)seq.mytype

Export =(a:symbol, b:symbol) boolean
  
Export ?(a:symbol, b:symbol)ordering
  
Export ?2(a:symbol,b:symbol) ordering  
  
Export Words(s:seq.word)symbol 

Export issimplename(sym:symbol) boolean 

Export isspecial(s:symbol)boolean 

Export isconst(s:symbol)boolean   

Export isunbound(sym:symbol)boolean 

Export hash(sym:symbol) int  

Export fsighash(s:symbol)int 

Export setunbound(sym:symbol) symbol
 
Export setrequires(sym:symbol)symbol 
 
Export addzcode (s:symbol,zcode:seq.symbol) symbol
  
Export replaceTsymbol(with:mytype, sym:symbol)symbol

Export Br2(l1:int, l2:int)symbol
  
Export brt(s:symbol)int  

Export brf(s:symbol)int  

Export name(sym:symbol) word 

Export iswords(s:symbol)boolean 

Export islocal(s:symbol)boolean 

Export isdefine(s:symbol)boolean 

Export isbr(symbol)boolean 

Export isexit(s:symbol)boolean  

Export value(sym:symbol)int

Export nopara(sym:symbol)int
  
--- end internal


Export extrabits(s:symbol)int 

 
function fsig(name:word,nametype:seq.mytype,paratypes:seq.mytype) seq.word
  let fullname=if isempty.nametype then [name] else  [name]+":"+print.first.nametype 
 if length.paratypes = 0 then fullname
 else
         for  acc= fullname+"(" ,t =paratypes do  acc+oldTypeRep.t +"," /for( acc >> 1 +")")

function fsig2(name:word,nametype:seq.mytype,paratypes:seq.mytype) seq.word
  let fullname=if isempty.nametype then [name] else  [name]+":"+print.first.nametype 
 if length.paratypes = 0 then fullname
 else
         for  acc= fullname+"(" ,t =paratypes do  acc+print.t +"," /for( acc >> 1 +")")

 
 Function checkwellformed(sym:symbol) boolean
 not.issimple.module.sym
 = for acc = false, t = types.sym while not.acc do isabstract.t /for(acc)
   
--- internal

Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
  let sym=if length.name=1 then symbol(internalmod,name,types,type?)
    else symbol4(internalmod,name_1,parsetype(name << 2),types,type?)
findelement2(dict, sym )

Function lookupsymbol(dict:set.symbol, sym:symbol)set.symbol findelement2(dict, sym)

Function lookupbysig(dict:set.symbol, name:seq.word)set.symbol lookup(dict, name, empty:seq.mytype)

Function printdict(s:set.symbol)seq.word
 for acc ="", @e = toseq.s do acc + print.@e /for(acc)

_______________________________
 
Function istype(s:symbol)boolean 
 not.issimplename.s /and wordname.s="type"_1 /and nopara.s=1

 
Function Record(types:seq.mytype)symbol
 symbol(moduleref."$record","RECORD",types,typeptr,specialbit)
 
 Function Reallit(i:int)symbol 
symbolZ(moduleref."$real",toword.i ,empty:seq.mytype,empty:seq.mytype,typereal,constbit,tobits.i)

----------------------
 
Function Exit symbol symbol(moduleref."$exitblock","EXITBLOCK", type?,specialbit )

Function Start(t:mytype)symbol symbol(moduleref("$loopblock",t),"Start",t, specialbit)

Function EndBlock symbol symbol(moduleref."$block","BLOCK",typeint, specialbit)

Function NotOp symbol  symbol(moduleref."standard","not", typeboolean, typeboolean)

Function PlusOp symbol  symbol(moduleref."standard","+", typeint, typeint, typeint)

Function paratypes(s:symbol)seq.mytype
if issimplename.s then  types.s >> 1 else  subseq(types.s,2,length.types.s-1)

Function resulttype(s:symbol)mytype  last.types.s 

Function fullname(s:symbol) seq.word  if issimplename.s then
 [name.s] else [name.s]+":"+print.first.types.s

Function print(s:symbol)seq.word
 if islocal.s  then 
{ let x = toword.value.s
  [ merge("%"+ if x = name.s then [ x]else [ x, first.".", name.s]/if)]
 }[ merge(["%"_1] + wordname.s)]
 else if name.module.s  /in "$int $real" then [name.s]
 else if iswords.s then
  if '"'_1 ∈ worddata.s then"'" + worddata.s + "'"
  else '"' + worddata.s + '"'
 else if isword.s then"WORD" + wordname.s
 else if isrecordconstant.s then  {[wordname.s]}  "{"+print.removeconstant.zcode.s+"}"
 else if isFref.s then"FREF" + print.(constantcode.s)_1
 else if not.isspecial.s /or isloopblock.s  then
    print.module.s + ":" +fsig2(wordname.s,nametype.s,paratypes.s)
     +if isloopblock.s  then "/br" else print.resulttype.s 
 else if isdefine.s then"Define" + name.s
  else if isstart.s then  "Start" + "(" + print.resulttype.s + ") /br"
  else if isblock.s   then"EndBlock  /br"
  else if isexit.s      then"Exit  /br"
  else if isbr.s then
   "Br2(" + toword.brt.s + "," + toword.brf.s + ") /br"
   else if iscontinue.s then "CONTINUE"+wordname.s + " /br"
  else 
   print.module.s + ":" + fsig2(wordname.s,nametype.s,paratypes.s)+print.resulttype.s
     
Function print(s:seq.symbol)seq.word for acc ="", sym = s do acc +  print.sym /for(acc)
 
Function Lit(i:int)symbol 
symbolZ(moduleref."$int",toword.i ,empty:seq.mytype,empty:seq.mytype,typeint,constbit,tobits.i)

Function Sequence(eletype:mytype, length:int)symbol
symbolZ(moduleref("$sequence", eletype),toword.length,empty:seq.mytype,empty:seq.mytype,seqof.eletype
,specialbit /or simplenamebit, tobits.length)

Function symbol(m:modref, name:seq.word, returntype:mytype, b:bits)symbol 
symbol(m, name , empty:seq.mytype, returntype,b )

Function symbol(module:modref,name:seq.word, paras:seq.mytype, rt:mytype) symbol
      symbol(module,name,paras,rt,0x0)
  
Function symbol(module:modref,name:seq.word,para:mytype,para2:mytype,para3:mytype,returntype:mytype) symbol
  symbol( module, name,[para,para2,para3],returntype)

Function symbol(module:modref,name:seq.word,para:mytype,para2:mytype ,returntype:mytype) symbol
  symbol( module, name,[para,para2 ],returntype)

Function symbol(module:modref,name:seq.word,para:mytype,returntype:mytype) symbol
 symbol( module, name,[para],returntype)

Function symbol(module:modref,name:seq.word, returntype:mytype) symbol
   symbol( module, name,empty:seq.mytype,returntype)

Function symbol(module:modref,name:seq.word, paras:seq.mytype, rt:mytype,hashbits:bits) symbol
    symbolZ(module,name_1,empty:seq.mytype,paras,rt, hashbits,0x0)
    
Function symbol4(module:modref, name:word,namePara:mytype,paras:seq.mytype,rt:mytype) symbol
   symbolZ(module,name,[namePara],paras,rt,if name /in "LOOPBLOCK" then specialbit else 0x0,0x0)

Function ifthenelse(cond:seq.symbol, thenclause:seq.symbol, elseclause:seq.symbol, m:mytype)seq.symbol
 [ Start.m] + cond + Br2(1, 2) + thenclause + Exit + elseclause + Exit
 + EndBlock

Function Littrue symbol  symbol(moduleref."standard","true" ,typeboolean, constbit)

Function Litfalse symbol symbol(moduleref."standard","false" , typeboolean, constbit)
  
Function continue(i:int)symbol symbol(moduleref."$continue",[toword.i],type?,specialbit)

Function Word(s:word)symbol symbol( moduleref."$word",[ s],  typeword, constbit)

Function isstartorloop(sym:symbol)boolean name.module.sym ∈ "$loopblock"

Function isstart(sym:symbol)boolean
 name.module.sym  = "$loopblock"_1 ∧  wordname.sym  ≠ "LOOPBLOCK"_1

Function isloopblock(s:symbol)boolean
 name.module.s = "$loopblock"_1 ∧ wordname.s = "LOOPBLOCK"_1

Function Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype)symbol
 symbol4(moduleref( "$loopblock",resulttype),"LOOPBLOCK"_1,
 typeref( [toword.firstvar,"."_1,"."_1]),types,resulttype )

Function firstvar(a:symbol)int toint.abstracttype.first.types.a

Function inmodule(sym:symbol,module:seq.word) boolean name.module.sym ∈ module

Function EqOp symbol  symbol(moduleref."standard","=", typeint, typeint, typeboolean)

Function GtOp symbol  symbol(moduleref."standard",">", typeint, typeint, typeboolean)

Function isblock(s:symbol)boolean name.module.s = "$block"_1

Function iscontinue(s:symbol)boolean name.module.s ∈ "$continue"

Function isSequence(s:symbol)boolean name.module.s = "$sequence"_1

Function isRecord(s:symbol)boolean name.module.s = first."$record"

Function iswordseq(s:symbol) boolean name.module.s = first."$words"

Function isword(s:symbol)boolean name.module.s ∈ "$word"

Function isrecordconstant(s:symbol)boolean name.module.s = first."$constant"

Function isFref(s:symbol)boolean name.module.s = first."$fref"

Function wordname(s:symbol) word first.worddata.s

Function constantcode(s:symbol)seq.symbol
 if isFref.s then zcode.s
 else if isrecordconstant.s then
  if isSequence.last.zcode.s then
   [ Lit.0, Lit.nopara.last.zcode.s] + zcode.s >> 1
  else zcode.s >> 1
 else empty:seq.symbol
 
Function typebit mytype typeref."bit bits."

Function typebits mytype  typeref."bits bits."

Function typebyte mytype typeref."byte bits."

Function typeword mytype typeref."word words."

_________________

Function Constant2(args:seq.symbol)symbol
  addzcode(symbol( moduleref."$constant", [toword.valueofencoding.encode.symbolconstant.args],empty:seq.mytype,typeptr,constbit)  ,args)
 


function hash(s:seq.symbol)int
 hash.for acc ="", e = s do acc + worddata.e + name.module.e /for(acc)

 
function assignencoding( p:seq.encodingpair.symbolconstant,a:symbolconstant)int   length.p +1


type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function isconstantorspecial(s:symbol)boolean isconst.s ∨ isspecial.s

Function Local(i:int)symbol Local(toword.i, typeint, i)

Function Optionsym symbol 
 symbol(internalmod,"option",typeint,seqof.typeword,type?)
 
 ----------------

Function Define(i:int)symbol Define(toword.i, i)

Function Define(name:word, i:int)symbol 
symbolZ(moduleref."$define",  name ,empty:seq.mytype,empty:seq.mytype, typeint ,specialbit,tobits.i )


Function Fref(s:symbol)symbol
addzcode(symbol(moduleref."$fref",[merge("FREF" + fsig(wordname.s,nametype.s,paratypes.s) 
+ print.s)],empty:seq.mytype,type?,constbit)
,[s])



Function GetSeqLength symbol symbol(moduleref."tausupport","getseqlength",typeptr,typeint)

Function GetSeqType symbol symbol(moduleref."tausupport","getseqtype",typeptr,typeint)

Function abortsymbol(typ:mytype) symbol 
let a=if isseq.typ     then typeptr else  typ
  symbol(builtinmod.a,"assert", seqof.typeword, a)
 
 symbol4(moduleref."tausupport","abort"_1,a,[seqof.typeword],a) 
  
 

Function basesym(s:symbol)symbol 
{only used in postbind } if name.module.s = first."$fref"then(zcode.s)_1 else s

Function getoption(code:seq.symbol)seq.word
 if isempty.code ∨ last.code ≠ Optionsym then empty:seq.word else worddata.code_(length.code - 1)

Function removeoptions(code:seq.symbol)seq.symbol
 if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)
 else code
 
Export typeref(seq.word) mytype  
 
Export moduleref( seq.word,para:mytype) modref
 
Export moduleref( seq.word) modref
    
Export addabstract(a:mytype,t:mytype) mytype   

Export typeT mytype  

  
  
Export seqof(mytype) mytype   

Function mangledname(s:symbol)word mangle(fsig(wordname.s,nametype.s,paratypes.s), 
if issimple.module.s then [name.module.s] else oldTypeRep.para.module.s+name.module.s
)


------


Export type:symbol

Export zcode(symbol)seq.symbol

Function nametype(sym:symbol) seq.mytype 
    if issimplename.sym then empty:seq.mytype else [first.types.sym] 
 

Function removeconstant(s:seq.symbol)seq.symbol
 for acc = empty:seq.symbol, @e = s do
  acc + if isrecordconstant.@e then removeconstant.zcode.@e else [ @e]
 /for(acc)

_______________________________________________

Function deepcopysymI(rt:mytype) symbol
 if rt= typeint then symbol(moduleref."tausupport", "deepcopy ",typeint,typeint)
      else if rt = typereal   then symbol(moduleref."tausupport", "deepcopy ",typereal,typereal)
      else if rt = typeboolean then symbol4(module2.typeboolean,"type"_1, rt, [ rt ],rt)
      else if rt = typebits then symbol4(module2.typebits,"type"_1, rt, [ rt ],rt)
      else if rt= typeword then symbol4(module2.typeword,"type"_1, rt, [ rt ],rt)
      else if   abstracttype.rt="char"_1 then symbol4(moduleref."standard","type"_1, rt, [ rt ],rt)
      else 
    assert  rt =seqof.typeword report "deepcopysymI"+ print.rt+stacktrace
   symbol4(moduleref("seq",typeword),"type"_1, rt, [ rt ],rt)
     
Export type:modref

Export issimple(modref)boolean     

Export para(modref) mytype

Export tomodref(mytype) modref

Export name(modref) word

Export library(modref)word

Export isseq(mytype) boolean    

Export isencoding(mytype) boolean  

Export processof(mytype)mytype

Export  abstracttypeof(mytype)  mytype 

Export  abstracttype(mytype) word 

Export internalmod modref

use words


use mangle


Export isabstract(modref)boolean

Export types(symbol) seq.mytype

Export ?(typedef,typedef)ordering   

Export ?(modref, modref)ordering


Function PreFref symbol symbol(internalmod,"PreFref",   typeint)

Function Local(name:word, type:mytype, parano:int)symbol 
symbolZ( moduleref."$local", name ,empty:seq.mytype,empty:seq.mytype,type,specialbit ,tobits.parano)

Function builtinmod(para:mytype)modref modref("."_1,"builtin"_1, para)

Export typebase(i:int)mytype

Export print(mytype)seq.word

Export replaceT(mytype, mytype)mytype

Export replaceT(mytype, modref)modref

Export =(mytype, mytype)boolean

Export isseq(mytype)boolean

Function deepcopySym(rt:mytype)symbol 
if rt=typereal then symbol(moduleref("tausupport"),"deepcopy",typereal,typereal) 
   else if rt=typeint then symbol(moduleref("tausupport"),"deepcopy",typeint,typeint) 
   else  symbol4(replaceT(parameter.rt,module2.rt),"type"_1, rt, [ rt ],rt)

symbol4(module2.typ,"type"_1, typ, [ typ ],typ)

Function setSym(typ:mytype)symbol
let fldtype = if isseq.typ then typeptr else if isencoding.typ then typeint else typ
 symbol(if fldtype = typeint ∨ fldtype = typeboolean ∨ fldtype = typeptr ∨ fldtype = typereal then
  moduleref."tausupport"
 else builtinmod.fldtype,"set", typeptr, fldtype, typeptr)

Function Getfld(fldtype:mytype)symbol 
let kind2=if isseq.fldtype then  typeptr  else if isencoding.fldtype then typeint else  fldtype
symbol(builtinmod.kind2,"fld", typeptr, typeint,kind2)

Export type:symdef

type symdef is sym:symbol, code:seq.symbol,paragraphno:int

Function symdef(sym:symbol, code:seq.symbol)symdef symdef(sym,code,0)

Export symdef(symbol, seq.symbol,int)symdef

Export sym(symdef)symbol

Export code(symdef)seq.symbol

Export paragraphno(symdef) int  
   
Function ?(a:symdef,b:symdef) ordering sym.a ? sym.b


Module symboldict 

use standard

use symbol

use set.symbol

use seq.symbol

use set.symdef

use seq.commoninfo
  
Export type:commoninfo

Export types(commoninfo)set.mytype

Export modname(commoninfo)modref

Export lib(commoninfo)word

Export mode(commoninfo) word

Export input(commoninfo) seq.word


Export commoninfo(input:seq.word, modname:modref, lib:word, types:set.mytype, mode:word)commoninfo

type commoninfo is input:seq.word, modname:modref, lib:word, types:set.mytype, mode:word

Function lookupbysig(dict:symboldict, sym:symbol)set.symbol findelement2(asset.dict, sym)

Function lookupbysig(dict:symboldict, name:seq.word)set.symbol findelement2(asset.dict, symbol(internalmod, name, typeint))

type symboldict is asset:set.symbol,requires:set.symdef ,commonX:seq.commoninfo

Export type:symboldict

Export asset(symboldict) set.symbol

Function symboldict(d:set.symbol, common:seq.commoninfo)symboldict symboldict(d, empty:set.symdef, common)

Function common(d:symboldict) commoninfo first.commonX.d 

Function requires(d:symboldict,sym:symbol) seq.symbol
 if hasrequires.sym then 
   code.findelement(symdef(sym,empty:seq.symbol),requires.d)_1
 else empty:seq.symbol

Function add(d:symboldict,syms:set.symbol,requires:set.symdef) symboldict
 symboldict(asset.d /cup syms,requires.d /cup requires,commonX.d) 

Function empty:symboldict symboldict symboldict(empty:set.symbol,empty:set.symdef,empty:seq.commoninfo)

Function +(d:symboldict,sym:symbol) symboldict   symboldict(asset.d+sym,requires.d,commonX.d)

Function -(d:symboldict, s:set.symbol) symboldict symboldict(asset.d-s,requires.d,commonX.d)

Function ∪(d:symboldict, s:set.symbol) symboldict symboldict(asset.d ∪ s,requires.d,commonX.d)

Function cardinality(d:symboldict) int cardinality.asset.d

Export type:bindinfo

type bindinfo is dict:symboldict, code:seq.symbol, types:seq.mytype, tokentext:seq.word

Export dict(bindinfo)symboldict

Export code(bindinfo)seq.symbol

Export types(bindinfo)seq.mytype

Export tokentext(bindinfo) seq.word

Export   bindinfo (dict:symboldict, code:seq.symbol, types:seq.mytype, tokentext:seq.word)
bindinfo



