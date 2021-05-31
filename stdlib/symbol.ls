Module symbolE

use symbol

use program

use seq.symbol

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


 
Export nopara(symbol) int 

Export print(seq.symbol) seq.word


Export inmodule(sym:symbol,module:seq.word) boolean 

 
Export symbol3(module:seq.word,name:seq.word,p1:mytype,p2:mytype,p3:mytype,p4:mytype,rt:mytype) symbol
 
Export symbol3(module:seq.word,name:seq.word,p1:mytype,p2:mytype,p3:mytype,rt:mytype) symbol
 
Export symbol3(module:seq.word,name:seq.word,p1:mytype,p2:mytype,rt:mytype) symbol
 
Export symbol3(module:seq.word,name:seq.word,p1:mytype,rt:mytype) symbol
 
Export symbol3(module:seq.word,name:seq.word, rt:mytype) symbol
 
Export seqof(base:mytype) mytype   


Export typeref(a:mytype,typ:seq.word) mytype

Export moduleref(a:seq.word) mytype

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

Export moduleref(seq.word, mytype) mytype 

Export symbol3(mytype, seq.word, seq.mytype, mytype) symbol

Export symbol3(mytype, seq.word, mytype) symbol

Export symbol4(mytype, word, mytype, seq.mytype, mytype) symbol

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

Export isparameter(symbol) boolean

Export type:compileinfo 

Export Local(int) symbol

Export getoption(seq.symbol) seq.word


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


type firstpass is modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unbound:set.symbol, types:seq.myinternaltype, prg:program

Function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.myinternaltype)firstpass
 firstpass(modname, uses, defines, exports, unboundexports, unboundx, types, emptyprogram)

Export firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unboundx:set.symbol, types:seq.myinternaltype, program)firstpass

Export modname(firstpass)mytype

Export defines(firstpass)set.symbol

Export exports(firstpass)set.symbol

Export uses(firstpass)seq.mytype

Export unboundexports(firstpass)seq.symbol

Export unbound(firstpass)set.symbol

Export types(firstpass)seq.myinternaltype

Export prg(firstpass)program

Function ?(a:firstpass, b:firstpass)ordering toalphaseq.typerep.modname.a ? toalphaseq.typerep.modname.b


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
 flags.a = flags.b ∧ fsig.a = fsig.b ∧ modname.a = modname.b

type symbol is fsig:seq.word, module:seq.word, resulttype:mytype, zcode:seq.symbol, flags:bits


Function fsighash(s:symbol)int toint(flags.s >> 4)

---internal

function extrabits(fsig:seq.word, flags:bits)bits bits.hash.fsig << 4 ∨ flags

Function typerep(m:mytype)seq.word towords.m

Function extrabits(s:symbol)int toint.flags.s

Function cleansymbol(sym:symbol,code:seq.symbol)symbol
 addzcode(sym,[ if isempty.zcode.sym then sym else addzcode( sym,  empty:seq.symbol)] + code)

 Function addzcode (s:symbol,zcode:seq.symbol) symbol
 symbol(fsig.s, modname.s, resulttype.s, zcode)

function symbol(fsig:seq.word, module:mytype, returntype:mytype, zcode:seq.symbol)symbol
symbol(fsig, typerep.module,  returntype, zcode, extrabits(fsig, bits.0))

function symbol(fsig:seq.word, module:mytype, returntype:mytype, zcode:seq.symbol,flags:bits) symbol
symbol(fsig, typerep.module,  returntype, zcode, extrabits(fsig, flags))

function symbol(fsig:seq.word, module:seq.word, returntype:seq.word, flag:bits)symbol
 symbol(fsig, module, mytype.returntype, empty:seq.symbol, extrabits(fsig, flag))
 
function symbol(fsig:seq.word, module:mytype, returntype:mytype, flag:bits)symbol
let t= symbol(fsig, typerep.module,  returntype, empty:seq.symbol, extrabits(fsig, flag))
{let a=encode.t}
t


Export fsig(symbol)seq.word

function fsig(name:seq.word,paratypes:seq.mytype) seq.word
if length.paratypes = 0 then name
 else
  name + "("
  + for acc ="", @e = paratypes do list(acc,",", typerep.@e)/for(acc)
  + ")"

 
 --- end internal
 
 Function wordname(s:symbol) word 
  (fsig.s)_1
 
  
 Function worddata(s:symbol) seq.word 
 {assert module.s /in ["$words" ,"headdict"] report "worddata"+print.s +stacktrace }
 fsig.s
 
 Function worddata2(s:symbol) seq.word 
{ assert module.s /in ["$words" ] report "worddata"+print.s +stacktrace }
 fsig.s
 
 

Function paratypes(s:symbol)seq.mytype
let a = fsig.s
 if last.a ≠ ")"_1 then empty:seq.mytype
 else 
 for acc = empty:seq.mytype, @e = break(a >> 1,",(", false) << 1 do acc + mytype.@e /for(acc)

Function modname(s:symbol)mytype mytype.module.s

Export resulttype(s:symbol)mytype  

Function nopara(s:symbol)int
 if isconst.s ∨ islocal.s ∨ isparameter.s then 0
 else if isspecial.s ∧ last.module.s ∉ "$record $loopblock"then
  if   isdefine.s ∨ isbr.s then 1
  else
   assert length.fsig.s > 1 report"define problem" + print.s   + stacktrace
    toint.(fsig.s)_2
 else if last.fsig.s ≠ ")"_1 then 0
 else
  for acc = if last.fsig.s = ")"_1 then 1 else 0 /if, e = fsig.s do
   if","_1 = e then acc + 1 else acc
  /for(acc)

Function ?(a:symbol, b:symbol)ordering
 fsighash.a ? fsighash.b ∧ fsig.a ? fsig.b ∧ module.a ? module.b

Function ?2(a:symbol, b:symbol)ordering fsighash.a ? fsighash.b ∧ fsig.a ? fsig.b

--- internal

Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
findelement2(dict, symbol(fsig(name,   types ),"?","?",0x0))

Function lookupsymbol(dict:set.symbol, sym:symbol)set.symbol
findelement2(dict, sym )


Function lookupLocal(dict:set.symbol, name: seq.word)set.symbol findelement2(dict, symbol(name,"?","?",0x0))


Function printdict(s:set.symbol)seq.word
 for acc ="", @e = toseq.s do acc + print.@e /for(acc)



Function replaceTsymbol(with:mytype, s:symbol)symbol
 if with = typeT then s
 else
  let fsig = fsig.s
  let parts = if last.fsig ≠ ")"_1 then [ fsig]else break(fsig >> 1,",(", false)
  let name = parts_1
  let newname = if last.name = "T"_1 then
   name >> 1
   + if typerep.with = ""then""else print.with
  else name
  let newfsig = if length.parts = 1 then newname
  else
   newname + "("
   + for acc ="", @e = parts << 1 do list(acc,",", typerep.replaceT(with, mytype.@e))/for(acc)
   + ")"
   symbol(newfsig,  replaceT(with, modname.s),  replaceT(with, resulttype.s), zcode.s)

Function ?(a:mytype, b:mytype)ordering towords.a ? towords.b



_______________________________

Function Parameter(name:word, type:mytype, parano:int)symbol
 symbol([ name], towords.type+[ toword.parano,"$parameter"_1], towords.type, specialbit)
 
Function parameternumber(s:symbol) word   (module.s)_-2

Function isparameter(s:symbol)boolean
    last.module.s = "$parameter"_1

Function istype(s:symbol)boolean subseq(fsig.s, 1, 2) = "type:"

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
 symbol(fsig("RECORD",types),moduleref."$record",typeptr,specialbit)
 
Function Sequence(eletype:mytype, length:int)symbol
 symbol("SEQUENCE" + toword.length, typerep.eletype + "$sequence", typerep.eletype + "seq", specialbit)
 
Function continue(i:int)symbol symbol(["CONTINUE"_1, toword.i],"$continue","?", specialbit)

Function Constant2(args:seq.symbol)symbol
 { let args = subseq(argsin, 1, length.argsin-1)}
 let fsig ="CONSTANT" + toword.valueofencoding.encode.symbolconstant.args
  symbol(fsig,moduleref."$constant", if isSequence.last.args then resulttype.last.args else typeptr , args,  constbit )

Function Emptyseq(type:mytype)seq.symbol [ Sequence(type, 0)]

Function isrecordconstant(s:symbol)boolean module.s = "$constant"

function hash(s:seq.symbol)int
 hash.for acc ="", e = s do acc + sigandmodule.e /for(acc)

 
function assignencoding( p:seq.encodingpair.symbolconstant,a:symbolconstant)int   length.p +1


type symbolconstant is toseq:seq.symbol

function =(a:symbolconstant, b:symbolconstant)boolean toseq.a = toseq.b

function hash(a:symbolconstant)int hash.toseq.a

Function isconstantorspecial(s:symbol)boolean isconst.s ∨ isspecial.s

function specialbit bits bits.4

function constbit bits bits.1

Function isspecial(s:symbol)boolean(flags.s ∧ specialbit) = specialbit

Function isconst(s:symbol)boolean(flags.s ∧ constbit) = constbit


Function isFref(s:symbol)boolean module.s = "$fref"

function sigandmodule(s:symbol)seq.word fsig.s + module.s

Function Exit symbol symbol("EXITBLOCK 1","$exitblock","?", specialbit)

Function ifthenelse(c:seq.symbol, t:seq.symbol, e:seq.symbol, type:mytype)seq.symbol
 [ start.type] + c + Br2(1, 2) + t + Exit + e + Exit
 + EndBlock

Function Br2(t:int, f:int)symbol
 symbol("BR2:" + toword.t + toword.f + "(boolean)","$br","?", specialbit)

Function start(t:mytype)symbol symbol("/start", typerep.t + "$loopblock", typerep.t, specialbit)

Function EndBlock symbol symbol("BLOCK 0","int $block","int", specialbit)

Function isstartorloop(sym:symbol)boolean last.module.sym ∈ "$loopblock"

Function isstart(sym:symbol)boolean
 last.module.sym = "$loopblock"_1 ∧ (fsig.sym)_1 ≠ "LOOPBLOCK"_1


Function isloopblock(s:symbol)boolean
 last.module.s = "$loopblock"_1 ∧ (fsig.s)_1 = "LOOPBLOCK"_1

Function Loopblock(types:seq.mytype, firstvar:int, resulttype:mytype)symbol
let fsig = for acc ="LOOPBLOCK:" + toword.firstvar + "(", t = types do
 acc + typerep.t + ","
/for(acc >> 1 + ")")
 symbol(fsig, typerep.resulttype + "$loopblock", typerep.resulttype, specialbit)

Function firstvar(a:symbol)int toint.(fsig.a)_3

Function brt(s:symbol)int toint.(fsig.s)_3

Function brf(s:symbol)int toint.(fsig.s)_4

Function Local(i:int)symbol Local.toword.i

Function Local(w:word)symbol symbol([ w],"local $","?", specialbit)

Function Local(name:seq.word, type:mytype)symbol symbol(name,"local $", towords.type, specialbit)

Function islocal(s:symbol)boolean module.s = "local $"

Function Reallit(i:int)symbol symbol([ toword.i],"$real","real", constbit)

Function Lit(i:int)symbol symbol([ toword.i],"$int","int", constbit)

Function Littrue symbol symbol("true","standard","boolean", constbit)

Function Litfalse symbol symbol("false","standard","boolean", constbit)

Function Words(s:seq.word)symbol symbol(s,"$words","word seq", constbit)

Function Word(s:word)symbol symbol([ s],"$word","word", constbit)

Function Define(s:seq.word)symbol Define.s_1

Function Define(w:word)symbol symbol([w],"$define","?", specialbit)

 
Function Define(w:int)symbol Define.toword.w

Function Fref(s:symbol)symbol
let fsig ="FREF" + fsig.s + module.s
 symbol(fsig,"$fref",type?, [ s],   constbit)
 
 Function type? mytype  typeref(moduleref."internal","?") 

Function Optionsym symbol symbol("option(int, word seq)","internal","?",0x0)

Function EqOp symbol symbol("=(int, int)","standard","boolean",0x0)

Function NotOp symbol symbol("not(boolean)","standard","boolean",0x0)

Function GtOp symbol symbol(">(int, int)","standard","boolean",0x0)

Function PlusOp symbol symbol("+(int, int)","standard","int",0x0)

Function MultOp symbol symbol("*(int, int)","standard","int",0x0)

Function GetSeqLength symbol symbol("getseqlength(ptr)","tausupport","int",0x0)

Function GetSeqType symbol symbol("getseqtype(ptr)","tausupport","int",0x0)


Function abortsymbol(typ:mytype) symbol 
let a=if isseq.typ     then typeptr else  typ
replaceTsymbol(a,symbol ("abort:T(word seq)","tausupport","T",0x0))


Function isblock(s:symbol)boolean last.module.s = "$block"_1

Function isRecord(s:symbol)boolean module.s = "$record"

Function isSequence(s:symbol)boolean last.module.s = "$sequence"_1

Function iscontinue(s:symbol)boolean module.s = "$continue"

Function isdefine(s:symbol)boolean module.s = "$define"

Function isexit(s:symbol)boolean module.s = "$exitblock"

Function isword(s:symbol)boolean module.s = "$word"

Function iswordseq(s:symbol) boolean module.s="$words"

Function isbr(s:symbol)boolean module.s = "$br"

Function value(s:symbol)int toint.(fsig.s)_1

Function constantcode(s:symbol)seq.symbol
 if isFref.s then zcode.s
 else if isrecordconstant.s then
  if isSequence.last.zcode.s then
   [ Lit.0, Lit.nopara.last.zcode.s] + zcode.s >> 1
  else zcode.s >> 1
 else empty:seq.symbol

Function basesym(s:symbol)symbol if module.s = "$fref"then(zcode.s)_1 else s

Function getoption(code:seq.symbol)seq.word
 if isempty.code ∨ last.code ≠ Optionsym then empty:seq.word else fsig.code_(length.code - 1)

Function removeoptions(code:seq.symbol)seq.symbol
 if length.code > 0 ∧ last.code = Optionsym then subseq(code, 1, length.code - 2)
 else code
 
Export typeref(modname:mytype,typ:seq.word) mytype  

Export moduleref(modname:seq.word,para:mytype) mytype
 
  
Export moduleref(modname:seq.word) mytype
    
Export addabstract(a:mytype,t:mytype) mytype   



 
Function typebits mytype  typeref(moduleref."bits","bits")

Function typebit mytype typeref(moduleref."bits","bit")

Function typebyte mytype typeref(moduleref."bits","byte")

Function typeword mytype typeref(moduleref."?","word")

Function typeT mytype typeref(moduleref."internal", "T")

  
  
Function seqof(base:mytype) mytype  addabstract(typeref(moduleref."seq","seq"),base)


Function mangledname(s:symbol)word mangle(fsig.s, module.s)


------

Function hash(s:symbol)int toint(flags.s >> 4)


type typedict is data:seq.myinternaltype

Function +(a:typedict, b:seq.myinternaltype)typedict typedict(data.a + b)

Function print(t:typedict)seq.word
 for acc ="", e = data.t do list(acc," /br", print3.e)/for(acc)

type myinternaltype is kind:word, name:word, modname:mytype, subflds:seq.mytype

Export type:myinternaltype

Export kind(myinternaltype)word

Export name(myinternaltype)word

Export modname(myinternaltype)mytype

Function isdefined(it:myinternaltype)boolean kind.it = "defined"_1

Function typekind(t:myinternaltype)word kind.t

Function modpara(t:myinternaltype)mytype parameter.modname.t

Export subflds(myinternaltype)seq.mytype

function =(a:myinternaltype, b:myinternaltype)boolean
 name.a = name.b ∧ parameter.modname.a = parameter.modname.b

Function changesubflds(t:myinternaltype, subflds:seq.mytype)myinternaltype myinternaltype("defined"_1, name.t, modname.t, subflds)

Export myinternaltype(kind:word, name:word, modname:mytype, subflds:seq.mytype)myinternaltype

Function replaceTmyinternaltype(with:mytype, it:myinternaltype)myinternaltype myinternaltype(kind.it, name.it, replaceT(with, modname.it), subflds.it)

Function tomyinternaltype(s:seq.word)myinternaltype
let t = parseit(s, 1, [ s_1], empty:seq.seq.word)
 myinternaltype(t_2_1, t_3_1, mytype.t_4, for acc = empty:seq.mytype, e = subseq(t, 5, length.t)do acc + mytype.e /for(acc))

function parseit(s:seq.word, i:int, fld:seq.word, flds:seq.seq.word)seq.seq.word
 if i > length.s then flds + fld
 else if s_i = "."_1 then
  parseit(s, i + 2, [ s_(i + 1)] + fld, flds)
 else { end of fld } parseit(s, i + 1, [ s_i], flds + fld)

Function print3(it:myinternaltype)seq.word
 if not.isdefined.it then
  "module:" + print.modname.it + "type" + name.it + "is"
  + kind.it
  + for acc ="", e = subflds.it do list(acc,",", printfld.e)/for(acc)
 else
  [ kind.it, name.it] + print.modname.it
  + for acc ="", e = subflds.it do acc + print.e /for(acc)

function printfld(f:mytype)seq.word [ fldname.f,":"_1] + print.parameter.f

Export fsig(symbol)seq.word

Export module(symbol)seq.word

/Export returntype(symbol)seq.word

Export type:symbol

Export zcode(symbol)seq.symbol

Function print(f:symbol)seq.word
let module = module.f
let fsig = fsig.f
 if islocal.f ∨ isparameter.f then [ merge(["%"_1] + fsig)]
 else if module ="$int" /or module= "$real" then fsig
 else if module = "$words"then
  if '"'_1 ∈ fsig then"'" + fsig + "'"
  else '"' + fsig + '"'
 else if module = "$word"then"WORD" + fsig
 else if isspecial.f then
  if isdefine.f then "DEFINE"+wordname.f
  else if isstart.f then
   fsig + "(" + print.resulttype.f + ") /br"
  else if isblock.f   then"EndBlock  /br"
  else if isexit.f      then"Exit  /br"
  else if isbr.f then
   "Br2(" + toword.brt.f + "," + toword.brf.f + ") /br"
  else if fsig_1 ∈ "  LOOPBLOCK  "then fsig + print.modname.f+ " /br" 
  else if iscontinue.f then fsig + " /br"
  else fsig
 else if isrecordconstant.f then fsig
 else if isFref.f then"FREF" + print.(constantcode.f)_1
 else if last.fsig = ")"_1 then fsig else fsig + "()"/if
 + print.modname.f

Function findelement(d:typedict, type:mytype)seq.myinternaltype
 findelement(myinternaltype("?"_1, abstracttype.type, mytype(towords.parameter.type + "?"), empty:seq.mytype), data.d)

Export typedict(seq.myinternaltype)typedict

Export type:typedict


Function getbasetype(d:typedict,intype:mytype) mytype
{ base types are int real boolean ptr seq.int seq.real seq.boolean seq.ptr seq.byte seq.bit 
   seq.packed2 seq.packed3 seq.packed4 seq.packed5 seq.packed6 or $base.x where x is a integer}
  if abstracttypeof.intype = typeref(moduleref."$base","$base") then { used for type of next in for expression } intype
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
     else if size = 2 then seqof.typeref(moduleref."tausupport", "packed2  ")
     else if size = 3 then seqof.typeref(moduleref."tausupport", "packed3  ")
     else if size = 4 then seqof.typeref(moduleref."tausupport", "packed4  ")
     else if size = 5 then seqof.typeref(moduleref."tausupport", "packed5  ")
     else if size = 6 then seqof.typeref(moduleref."tausupport", "packed6  ")  
     else seqof.typeptr
    else
     let basetype =(subflds.t_1)_1
      if isseq.basetype   /and isseq  then seqof.typeptr
      else let basetype2=getbasetype(d,basetype)
         if not.isseq then basetype2
         else    if isseq.basetype2     then seqof.typeptr
         else seqof.basetype2 
         
Function packedtypes seq.mytype [typeref(moduleref."tausupport","packed2")
,typeref(moduleref."tausupport","packed3"),typeref(moduleref."tausupport","packed4"),typeref(moduleref."tausupport","packed5"),typeref(moduleref."tausupport","packed6")]
         
 

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
let t = addabstract(typeref(modname.it,[name.it]), parameter.modname.it)
       symbol4(modname.it,"type"_1 ,t  ,   [ t], t)

Function deepcopysym(d:typedict, type:mytype)symbol typesym(d, type)

Function typesym(d:typedict, type:mytype)symbol
 if type = typeint then symbol("deepcopy(int)","tausupport","int",0x0)
 else if type = typereal then symbol("deepcopy(real)","tausupport","real",0x0)
 else
  let e = findelement(d, type)
   assert length.e = 1 report"type not found" + print.type + stacktrace
   let it = e_1
   let t = addabstract(typeref(modname.it,[name.it]), parameter.modname.it)
        symbol4(modname.it,"type"_1 ,t  ,   [ t], t)

   
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


  
 Function symbol3(module:mytype,name:seq.word, paras:seq.mytype, rt:mytype) symbol
    assert length.name=1 /or subseq(name,1,2) /in ["build.","allocateseq:"] report "name315"+name 
  symbol(fsig(name,paras),  module ,  rt, 0x0)
     

Function symbol4(module:mytype, name:word,namePara:mytype,paras:seq.mytype,rt:mytype) symbol
  symbol(fsig([name]+":"+print.namePara,paras),  module ,  rt, 0x0)
 
Function symbol3(module:seq.word,name:seq.word,p1:mytype,p2:mytype,p3:mytype,p4:mytype,rt:mytype) symbol
  symbol3(moduleref.module, name,[p1,p2,p3,p4],rt)
 



Function symbol3(module:seq.word,name:seq.word,p1:mytype,p2:mytype,p3:mytype,rt:mytype) symbol
symbol3(moduleref.module, name,[p1,p2,p3],rt)

Function symbol3(module:seq.word,name:seq.word,p1:mytype,p2:mytype,rt:mytype) symbol
symbol3(moduleref.module, name,[p1,p2],rt)

Function symbol3(module:seq.word,name:seq.word,p1:mytype,rt:mytype) symbol
symbol3(moduleref.module, name,[p1],rt)
 
Function symbol3(module:seq.word,name:seq.word, rt:mytype) symbol
symbol3(moduleref.module, name,empty:seq.mytype,rt)
 
Function symbol3(module:mytype,name:seq.word,p1:mytype,p2:mytype,p3:mytype,rt:mytype) symbol
  symbol3( module, name,[p1,p2,p3],rt)

 
Function symbol3(module:mytype,name:seq.word,p1:mytype,rt:mytype) symbol
 symbol3( module, name,[p1],rt)

 
 Function symbol3(module:mytype,name:seq.word, rt:mytype) symbol
   symbol3( module, name,empty:seq.mytype,rt)





Function inmodule(sym:symbol,module:seq.word) boolean last.module.sym= first.module


Function symboladdword symbol symbol("add(char seq encodingstate, char seq encodingpair)","char seq encoding","char seq encodingstate",0x0)

Function abortedsymbol symbol symbol("aborted(T process)","builtin","boolean",0x0)

Function isseq(a:mytype) boolean   abstracttypeof.a = typeref(moduleref."seq", "seq")

Function isencoding(a:mytype) boolean abstracttypeof.a = typeref(moduleref."encoding", "encoding")

Function fldname(a:mytype) word   abstracttype.a

Function fldtype(a:mytype) mytype parameter.a 

Export  abstracttypeof(a:mytype)  mytype  


use words



Function typeinname(a:seq.word) seq.mytype
if length.a = 1 then empty:seq.mytype
else 
 assert a_2 /in ":" report "typeiname format problem"
 for   r=""  , w =a << 2  while w /nin "("  do
    if w /in "." then r else [w]+ r
 /for ( [mytype.r])

use encoding.symbol

use mangle

function assignencoding(a:seq.encodingpair.symbol, symbol) int length.a+1

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

