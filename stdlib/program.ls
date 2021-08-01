Module program

    
use pro2gram

use symbol 

use seq.symbol

use set.symbol

use words

use seq.mytype
 
use standard

use seq.myinternaltype

use set.word


use set.symdef

Export type:program

Function getCode(p:program, s:symbol) seq.symbol 
let t = findelement(s, toset.p)
 if isempty.t then  empty:seq.symbol else  zcode.t_1 << 1



Function  pro2gram(p:program) pro2gram  pro2gramB.p
 
Function pro2gramB(p:program) pro2gram  
 for acc = empty:set.symdef , sym=toseq.toset.p do acc+symdef(sym, zcode.sym << 1) /for(pro2gram.acc)



Function emptyprogram program program2.empty:set.symbol

type program is toset:set.symbol

Function ∪(p:program, a:program)program program(toset.p ∪ toset.a)

Function toseq(p:program)seq.symbol toseq.toset.p

Function ∈(s:symbol, p:program)boolean s ∈ toset.p

Function program2(a:set.symbol)program program.a

Function map(p:program, s:symbol, code:seq.symbol)program  
 program.replace(toset.p, addzcode (s, [ s] + code))


   
  
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

Function  firstpass(module:modref, uses:seq.mytype, defines:set.symbol, exports:set.symbol  , types:seq.myinternaltype )firstpass
firstpass(module , uses , defines , exports , empty:seq.symbol, empty:set.symbol, types, emptyprogram) 


use standard

use symbol

use seq.myinternaltype

use mytype

use seq.mytype

use pro2gram

type typedict is data:seq.myinternaltype

Export data(typedict) seq.myinternaltype

Function type2dict(dict:typedict) type2dict   
for acc=emptytypedict, t=data.dict do
add(acc,newtype(module.t,name.t) ,  subflds.t)  
/for(acc)

Function +(a:typedict, b:seq.myinternaltype)typedict typedict(data.a + b)


Function findtype(d:typedict, type:mytype)seq.myinternaltype
 findelement(myinternaltype("?"_1, abstracttype.type,    moduleref("?", parameter.type) , empty:seq.mytype), data.d)

Export typedict(seq.myinternaltype)typedict

Export type:typedict



Function typesym(d:typedict, type:mytype)symbol
 if type = typeint then symbol(moduleref."tausupport", "deepcopy ",typeint,typeint)
 else if type = typereal then symbol(moduleref."tausupport", "deepcopy ",typereal,typereal)
 else
  let e = findtype(d, type)
   assert length.e = 1 report"type not found" + print.type + stacktrace
   let it = e_1
   let t = addabstract(typeref3(module.it, name.it ), para.module.it)
        symbol4(module.it,"type"_1 ,t  ,   [ t], t)
        
        

type myinternaltype is kind:word, name:word, module:modref, subflds:seq.mytype

Export type:myinternaltype

Export name(myinternaltype)word

Export kind(myinternaltype) word

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

Function typesym(it:myinternaltype)symbol
let t = addabstract(typeref3(module.it, name.it ), para.module.it)
       symbol4(module.it,"type"_1 ,t  ,   [ t], t)


