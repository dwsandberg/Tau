Module mytype

use standard

use otherseq.word

use seq.mytype

use xxhash


Export type:mytype

Function print(s:mytype)seq.word  
  for acc ="", t = typerep.s do acc + "." + name.t /for(acc << 1)
  
Function print(s:modref) seq.word
  if issimple.s then [name.s] else 
  [name.s,"."_1]+print.para.s

Function =(t:mytype, b:mytype)boolean typerep.t = typerep.b

Function abstracttypeof(a:mytype)mytype typeref.[ abstracttype.a,"?"_1,"."_1]

Function parameter(m:mytype)mytype mytype(typerep.m << 1)

Function isabstract(a:mytype)boolean last.typerep.a  = first.typerep.typeT

function =(a:typedef,b:typedef) boolean name.a=name.b

Function replaceT(with:mytype, m:mytype)mytype
 if isabstract.m   then
     mytype( typerep.m >> 1  +typerep.with)
  else m

Function replaceT(with:mytype, m:modref)modref
 if issimple.m /or not.isabstract.para.m then m
 else  
 modref(library.m,name.m,mytype( typerep.para.m >> 1  +typerep.with))

Function typeint mytype   typeref."int internal ."

Function typeptr mytype   typeref."ptr tausupport ." 

Function typeboolean mytype typeref."boolean internal ."

Function typereal mytype typeref."real internal ."

Function typeT mytype typeref."T internal."

Function ?(a:mytype, b:mytype)ordering typerep.a ? typerep.b

Function ?(a:typedef,b:typedef)ordering  name.a ? name.b

Function isseq(a:mytype)boolean abstracttypeof.a = typeref."seq seq ."

Function isencoding(a:mytype)boolean abstracttypeof.a = typeref."encoding encoding ."

Function internalmod modref moduleref."internal"


type mytype is typerep:seq.typedef

Export typerep(mytype) seq.typedef

Function iscomplex(a:mytype)boolean length.typerep.a > 1

Function issimple(m:modref)boolean  isempty.typerep.para.m  


Function abstracttype(m:mytype)word       name.first.typerep.m 

Function addabstract(a:mytype, t:mytype)mytype mytype( [first.typerep.a] +typerep.t  )

Function typeref(s:seq.word)mytype
 assert length.s = 3 report"typereferror" + s
  mytype.[ typedef(first.s,s_2,s_3)]

type modref is library:word, name:word, para:mytype

Export type:modref

Export para(modref) mytype

Export name(modref) word

Export library(modref) word


Function isabstract(m:modref) boolean  not.isempty.typerep.para.m /and  isabstract.para.m

Function tomodref(m:mytype)modref modref("."_1, abstracttype.m , parameter.m)

Function moduleref(modname:seq.word, para:mytype)modref modref("."_1, modname_1, para)

Function moduleref(modname:seq.word)modref moduleref(modname, mytype.empty:seq.typedef)

Function typeref3(modname:modref, typname: word)mytype 
  typeref([typname,name.modname,library.modname] ) 

Function TypeFromOldTyperep(m:seq.word) mytype   mytype(B.m)

Function oldTypeRep(m:mytype) seq.word A.typerep.m

Function parsetype(s:seq.word) mytype
     for   acc="",   w=s do
       if w="."_1 then acc else [w]+acc
    /for(TypeFromOldTyperep(acc))
    
Function hash(b:seq.mytype,name:word) int
for acc = hashstart, a = b >> 1 do  
for acc2 = acc, e = typerep.a do hash(acc2, hash.name.e)/for(acc2)
/for ( finalmix.hash(acc,hash.name) )
     
type typedef is name:word,module:word,library:word

Export  name(typedef) word

Export  module(typedef) word

Export  library(typedef) word



use otherseq.typedef

function A(b:seq.typedef) seq.word for acc="",e=b do  [name.e]+acc  /for(acc)

function B(b:seq.word) seq.typedef  for acc=empty:seq.typedef,e=b do  [typedef(e,"?"_1,"?"_1)]+acc  /for(acc)



     
     
      