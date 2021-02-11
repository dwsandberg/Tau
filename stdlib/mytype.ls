Module mytype

use standard

Export type:mytype

type mytype is record towords:seq.word

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

Function isinstance(a:mytype)boolean length.towords.a > 1 ∧ not(parameter.a = mytype."T")

Function iscomplex(a:mytype)boolean length.towords.a > 1

Function replaceT(with:mytype, m:mytype)mytype
 if(towords.m)_1 = "T"_1 then
 mytype(towords.with + subseq(towords.m, 2, length.towords.m))
 else m

Function typeint mytype mytype."int"

Function typeptr mytype mytype."ptr"

Function addabstract(a:word, b:mytype)mytype mytype(towords.b + a)