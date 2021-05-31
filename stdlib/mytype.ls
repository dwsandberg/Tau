Module mytype

use standard

Export type:mytype

type mytype is towords:seq.word

Export mytype(seq.word)mytype

Export towords(mytype)seq.word

Function print(p:mytype)seq.word prt(towords.p, length.towords.p)

function prt(s:seq.word, i:int)seq.word
 if length.s = 0 then"?"
 else if i = 1 then [ s_1]
 else [ s_i] + "." + prt(s, i - 1)

Function =(t:mytype, b:mytype)boolean towords.t = towords.b

Function abstracttype(m:mytype)word(towords.m)_(length.towords.m)

Function parameter(m:mytype)mytype mytype.subseq(towords.m, 1, length.towords.m - 1)

Function isabstract(a:mytype)boolean(towords.a)_1 = "T"_1

/Function isinstance(a:mytype)boolean length.towords.a > 1 ∧ not(parameter.a = mytype."T")

Function iscomplex(a:mytype)boolean length.towords.a > 1

Function replaceT(with:mytype, m:mytype)mytype
 if(towords.m)_1 = "T"_1 then
  mytype(towords.with + subseq(towords.m, 2, length.towords.m))
 else m

Function typeint mytype mytype."int"

Function typeptr mytype mytype."ptr"

Function typeboolean mytype mytype."boolean"

Function typereal   mytype mytype."real"

function typeT mytype typeref(moduleref."internal", "T")


function addabstract2(a:word, b:mytype)mytype mytype(towords.b + a)

Function abstracttypeof(a:mytype)  mytype typeref(moduleref."?",[abstracttype.a] )


Function typeref(modname:mytype,typ:seq.word) mytype mytype.typ

Function moduleref(modname:seq.word,para:mytype) mytype
  addabstract2(modname_1,para)
  
  Function moduleref(modname:seq.word) mytype
 { assert length.modname=1 report "problem moduleref"+modname+stacktrace}
  mytype.[modname_1] 
  
  Function addabstract(a:mytype,t:mytype) mytype  addabstract2(abstracttype.a,t)
