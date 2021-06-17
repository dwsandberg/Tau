


Module symbol

use seq.typedef

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

Export isabstract(m:mytype)boolean

Export parameter(mytype)mytype

Export print(p:mytype)seq.word

Export =(t:mytype, b:mytype)boolean

Export replaceT(with:mytype, m:mytype)mytype

Export iscomplex(a:mytype)boolean

Export   worddata(s:symbol) seq.word  

Export =(a:modref,b:modref) boolean   

---internal

use hidesymbol

Export raw(symbol) bits

Export type:symbol

Export isparameter(symbol) boolean

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

Function cleansymbol(sym:symbol,code:seq.symbol)symbol
 addzcode(sym,[ if isempty.zcode.sym then sym else addzcode( sym,  empty:seq.symbol)] + code)
 
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

Function Parameter(name:word, type:mytype, parano:int)symbol
   symbolZ(moduleref("$parameter"),name,empty:seq.mytype,empty:seq.mytype,type, specialbit,tobits(parano))
 
Function istype(s:symbol)boolean 
 not.issimplename.s /and wordname.s="type"_1

Function Load(type:mytype)symbol
let kind2=if isseq.type then  typeptr  else  type
 symbol(moduleref("builtin",kind2),"load",[typeptr,typeint],kind2)
 
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
 if islocal.s ∨ isparameter.s then 
{ let x = toword.value.s
  [ merge("%"+ if x = name.s then [ x]else [ x, first.".", name.s]/if)]
 }[ merge(["%"_1] + wordname.s)]
 else if name.module.s  /in "$int $real" then [name.s]
 else if iswords.s then
  if '"'_1 ∈ worddata.s then"'" + worddata.s + "'"
  else '"' + worddata.s + '"'
 else if isword.s then"WORD" + wordname.s
 else if isrecordconstant.s then [wordname.s]
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
 
Function Emptyseq(type:mytype)seq.symbol [ Sequence(type, 0)]


function hash(s:seq.symbol)int
 hash.for acc ="", e = s do acc + worddata.e + name.module.e /for(acc)

 
function assignencoding( p:seq.encodingpair.symbolconstant,a:symbolconstant)int   length.p +1


type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function isconstantorspecial(s:symbol)boolean isconst.s ∨ isspecial.s

Function Local(i:int)symbol Local(toword.i, typeint, i)



Function LocalF(name:seq.word, type:mytype)symbol 
let value=if checkinteger.first.name="INTEGER"_1 then toint.first.name else 0
symbolZ(moduleref."$local",name_1,empty:seq.mytype,empty:seq.mytype,type,specialbit,tobits.value)

Function DefineF(name:word)symbol 
let value=if checkinteger.name="INTEGER"_1 then toint.name else 0
symbolZ(moduleref."$define",name ,empty:seq.mytype,empty:seq.mytype,type?,specialbit,tobits.value)

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
replaceTsymbol(a,symbol4(moduleref."tausupport","abort"_1,typeT,[seqof.typeword],typeT))
  

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

type typedict is data:seq.myinternaltype

Function +(a:typedict, b:seq.myinternaltype)typedict typedict(data.a + b)

type myinternaltype is kind:word, name:word, module:modref, subflds:seq.mytype

Export type:myinternaltype

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


function parseit(s:seq.word, i:int, fld:seq.word, flds:seq.seq.word)seq.seq.word
 if i > length.s then flds + fld
 else if s_i = "."_1 then
  parseit(s, i + 2, [ s_(i + 1)] + fld, flds)
 else { end of fld } parseit(s, i + 1, [ s_i], flds + fld)

Export type:symbol

Export zcode(symbol)seq.symbol


Function nametype(sym:symbol) seq.mytype 
    if issimplename.sym then empty:seq.mytype else [first.types.sym] 
 
  

Function findtype(d:typedict, type:mytype)seq.myinternaltype
 findelement(myinternaltype("?"_1, abstracttype.type,    moduleref("?", parameter.type) , empty:seq.mytype), data.d)

Export typedict(seq.myinternaltype)typedict

Export type:typedict



Function typesym(it:myinternaltype)symbol
let t = addabstract(typeref3(module.it, name.it ), para.module.it)
       symbol4(module.it,"type"_1 ,t  ,   [ t], t)

Function deepcopysym(d:typedict, type:mytype)symbol typesym(d, type)

Function typesym(d:typedict, type:mytype)symbol
 if type = typeint then symbol(moduleref."tausupport", "deepcopy ",typeint,typeint)
 else if type = typereal then symbol(moduleref."tausupport", "deepcopy ",typereal,typereal)
 else
  let e = findtype(d, type)
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

Export isseq(mytype) boolean    

Export isencoding(mytype) boolean  

Export processof(mytype)mytype

Export  abstracttypeof(mytype)  mytype 

Export  abstracttype(mytype) word 

Export internalmod modref

use words

/use encoding.symbol

use mangle


Export isabstract(modref)boolean

Export types(symbol) seq.mytype

Export ?(typedef,typedef)ordering   

Export ?(modref, modref)ordering

/function assignencoding(a:seq.encodingpair.symbol, symbol) int length.a+1

Function PreFref symbol symbol(builtinmod.type?,"PreFref",   typeint)

Function Local(name:word, type:mytype, parano:int)symbol 
symbolZ( moduleref."$local", name ,empty:seq.mytype,empty:seq.mytype,type,specialbit ,tobits.parano)

Function builtinmod(para:mytype)modref modref("."_1,"builtin"_1, para)

Export typebase(i:int)mytype

Export print(mytype)seq.word

Export replaceT(mytype, mytype)mytype

Export replaceT(mytype, modref)modref

Export =(mytype, mytype)boolean

Export isseq(mytype)boolean

Function deepcopySym(typ:mytype)symbol symbol4(module2.typ,"type"_1, typ, [ typ ],typ)

Function setSym(typ:mytype)symbol
let fldtype = if isseq.typ then typeptr else if isencoding.typ then typeint else typ
 symbol(if fldtype = typeint ∨ fldtype = typeboolean ∨ fldtype = typeptr ∨ fldtype = typereal then
  moduleref."tausupport"
 else builtinmod.fldtype,"set", typeptr, fldtype, typeptr)

Function fldSym(fldtype:mytype)symbol symbol(builtinmod.fldtype,"fld", typeptr, typeint, fldtype)

Export type:symdef

type symdef is sym:symbol, code:seq.symbol,paragraphno:int

Function symdef(sym:symbol, code:seq.symbol)symdef symdef(sym,code,0)

Export symdef(symbol, seq.symbol,int)symdef

Export sym(symdef)symbol

Export code(symdef)seq.symbol

Export paragraphno(symdef) int  
   
Function ?(a:symdef,b:symdef) ordering sym.a ? sym.b
