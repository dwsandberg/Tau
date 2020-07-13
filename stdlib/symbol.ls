Module symbol

use mytype

use seq.seq.char

use seq.char

use seq.mytype

use stacktrace

use stdlib

use seq.symbol

use set.symbol


use set.word

use seq.seq.word


 




Function type:symbol internaltype export


Function =(a:symbol, b:symbol)boolean fsighash.a=fsighash.b &and fsig.a = fsig.b  ∧ modname.a = modname.b



type symbol is record  fsig:seq.word,module:seq.word,
returntype:seq.word, zcode:seq.symbol ,fsighash:int

Function fsighash(symbol) int export 




Function symbol(fsig:seq.word,module:seq.word,returntype:seq.word) symbol 
 symbol(fsig,module,returntype,empty:seq.symbol)
 
 Function symbol(fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol) symbol 
   symbol(fsig,module,returntype,zcode,if length.fsig=0 then 0 else hash.fsig)

 
 Function fsig(symbol) seq.word export

Function newsymbol(namein:seq.word,modname:mytype, paratypes:seq.mytype,  resulttype:mytype) symbol
 let name=if changeit then namein else [merge(namein)]
let b= (length.towords.modname > 1)  &and  not((towords.modname)_1="T"_1) &and not(ispara.modname) 
  let paratyps= if b then @(+,replaceT(parameter.modname),empty:seq.mytype,paratypes)  else paratypes
  let sym=symbol(if length.paratyps = 0 then name else  name + "(" + @(seperator.",", towords,"", paratyps)  + ")"
  ,towords.modname,
  towords.if b then    replaceT(parameter.modname,resulttype) else resulttype
  ,empty:seq.symbol)
 sym


Function name(s:symbol) seq.word  
let j=findindex("("_1, fsig.s)  
let n=if j > length.fsig.s then fsig.s
 else
subseq(fsig.s, 1, j - 1)
n





Function paratypes(s:symbol)seq.mytype 
 @(+, mytype, empty:seq.mytype, paratypesastext.s)

function paratypesastext(s:symbol) seq.seq.word
let a= fsig.s 
  if length.a < 4 then empty:seq.seq.word
  else 
  break(","_1, subseq(a, 1, length.a - 1), findindex("("_1, a) + 1 )

function break(w:word, a:seq.word, j:int)seq.seq.word
 let i = findindex(w, a, j)
  if i > length.a then
  if j > length.a then empty:seq.seq.word else [ subseq(a, j, i)]
  else [ subseq(a, j, i - 1)] + break(w, a, i + 1)
  
Function mangledname(s:symbol)word 
mangle2( name.s ,  module.s, @(+,towords,empty:seq.seq.word,paratypes.s))


Function modname(s:symbol)mytype mytype.module.s

Function resulttype(s:symbol)mytype mytype.returntype.s

Function nopara(s:symbol)int 
 if module.s="$" then 
  if  (fsig.s)_1= "DEFINE"_1 then 1 else 
  toint((fsig.s)_2)  else 
 if last.module.s in  "$constant $fref $words $word  local"  then 0  
    else
 @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

function counttrue(i:int, b:boolean)int if b then i + 1 else i

use otherseq.word

Function ?(a:symbol, b:symbol)ordering   fsighash.a ? fsighash.b &and   fsig.a ? fsig.b ∧  module.a ? module.b

Function ?2(a:symbol, b:symbol)ordering   fsighash.a ? fsighash.b &and   fsig.a ? fsig.b 


Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
 findelement2(dict, newsymbol( name , mytype."?", types, mytype."?" ))
 
Function lookupfsig(dict:set.symbol, fsig:seq.word)set.symbol
 findelement2(dict,  symbol( fsig ,  "?",  "?" ))


Function printdict(s:set.symbol)seq.word @(+, print,"", toseq.s)

Function print(s:symbol)seq.word
 let t = module.s
  if t = "local"then [ merge("%" + fsig.s)]
  else if t = "$words"then '"' + fsig.s + '"'
  else if t = "$constant" then   let tmp="CONSTANT{"+ @(+,print,"",zcode.s) +"}" 
     if tmp="CONSTANT{ 0 0 } " then "emptyseq"  else tmp
  else if last.t in " $ "then
  if(fsig.s)_1 in "EXITBLOCK LOOPBLOCK CONTINUE BR"then fsig.s + " &br"else fsig.s
  else fsig.s + "[" + t + "]"


function replaceTinname(with:mytype, name:word)word
 let x = decodeword.name
  if subseq(x, length.x - 1, length.x)
  in [ //.T // [ char.46, char.84], //:T // [ char.58, char.84]]then
  encodeword(subseq(x, 1, length.x - 1) + @(+, decodeword, empty:seq.char, print.with))
  else name




type mapele is record   s:symbol,target:symbol  

Function type:mapele internaltype export

Function s(mapele) symbol export

Function key(a:mapele) symbol   s.a

Function target(a:mapele) symbol  export


function replaceT(with:seq.word,s:word) seq.word if "T"_1=s then with else [s]

function replaceT(with:seq.word,s:seq.word) seq.word @(+,replaceT.with,"",s)

Function replateTfsig(with:seq.word,fsig:seq.word) seq.word
if changeit then [fsig_1]+replaceT(  with,subseq(fsig,2,length.fsig)) else
[replaceTinname(mytype.with, fsig_1)]+replaceT( with,subseq(fsig,2,length.fsig))

Function replaceTsymbol2(with:mytype, s:symbol) mapele
  if with=mytype."T" then mapele(s,s )
 else
   let x=replaceTsymbol(with, s)
  mapele(x,s )
  
Function replaceTsymbol(with:mytype, s:symbol) symbol
  if with=mytype."T" then s
 else
   symbol(replateTfsig(towords.with,fsig.s), replaceT(towords.with,module.s), replaceT(towords.with, returntype.s),zcode.s)
  


Function ?(a:mytype, b:mytype)ordering towords.a ? towords.b




Function type:mytype internaltype export

Function towords(mytype)seq.word export

Function mytype(seq.word)mytype export

Function abstracttype(m:mytype)word export

Function isabstract(a:mytype)boolean export


Function parameter(m:mytype)mytype export

Function print(p:mytype)seq.word export

Function =(t:mytype, b:mytype)boolean export

Function replaceT(with:mytype, m:mytype)mytype export

Function iscomplex(a:mytype)boolean export

use seq.myinternaltype


Function type:firstpass internaltype export

type firstpass is record modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, 
unbound:set.symbol,types:seq.myinternaltype

Function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, 
unboundx:set.symbol,types:seq.myinternaltype) firstpass
 export
 

Function exportmodule(firstpass)boolean false

Function modname(firstpass)mytype export

Function defines(firstpass)set.symbol export

Function exports(firstpass)set.symbol export

Function uses(firstpass)seq.mytype export

Function unboundexports(firstpass)seq.symbol export

Function unbound(firstpass)set.symbol export

Function types(firstpass) seq.myinternaltype export

_______________________________      
     
Function program(s:set.symbol) program export
    
---------------

Function Parameter(name:word,type:mytype,parano:int) symbol
newsymbol([name], mytype.[ "para"_1,toword.parano,"$"_1], empty:seq.mytype, type)

function ispara(s:mytype) boolean  ( towords.s)_1="para"_1 &and last.towords.s="$"_1  

Function deepcopysym (type:mytype) symbol
newsymbol("deepcopy"  ,mytype(towords.type + "process"), [type], type)

Function IDXUC symbol  symbol("IDXUC(int,int)","builtin", "?")

Function Emptyseq seq.symbol [Lit0,Lit0,Record.2]

Function pseqidxsym(type:mytype) symbol
    newsymbol("_" , mytype(towords.type + "seq"_1),[ mytype(towords.type + "pseq"_1), mytype."int"],type)
    
Function Record(i:int) symbol symbol([ "RECORD"_1,toword.i],    "$",  "?",empty:seq.symbol)

Function Apply(i:int) symbol symbol([ "APPLY"_1,toword.i],    "$",  "?",empty:seq.symbol)

Function Block(i:int) symbol symbol([ "BLOCK"_1,toword.i],    "$",  "?",empty:seq.symbol)

Function constant(args:seq.symbol) symbol
  let txt=     toword.valueofencoding.encode(constante,args)  
    // @(+,sigandmodule,"",args)    //
   symbol("CONSTANT" + txt, "$constant",  "?",args )
   

function hash(s:seq.symbol) int hash.@(+,sigandmodule,"",s) 

type constante is encoding seq.symbol
 
Function isconst(s:symbol)boolean
module.s in ["$words", "int $", "$word","$constant","$fref" ] 

function  sigandmodule(s:symbol) seq.word   fsig.s+module.s

function assignencoding(a:int, b:seq.symbol ) int assignrandom(a,b)

Function Exit  symbol symbol(  "EXITBLOCK 1",    "$",  "?",empty:seq.symbol)

Function Br    symbol symbol( "BR 3", "$",  "?",empty:seq.symbol)


Function Local(i:int)  symbol symbol(  [toword.i],    "local",  "?",empty:seq.symbol)

Function Local(w:word)  symbol symbol(  [w] ,    "local",  "?",empty:seq.symbol)

Function Local(name:seq.word,type:mytype) symbol  symbol( name ,"local", towords.type,empty:seq.symbol)

Function islocal(s:symbol) boolean module.s="local"

Function Lit(i:int)  symbol symbol(  [toword.i],    "int $",  "int",empty:seq.symbol)

Function Lit0 symbol symbol(  "0",    "int $",  "int",empty:seq.symbol)

Function Lit2 symbol symbol(  "2",    "int $",  "int",empty:seq.symbol)

Function Lit3 symbol symbol(  "3",    "int $",  "int",empty:seq.symbol)

Function Words(s:seq.word) symbol  symbol(  s,    "$words",  "word seq",empty:seq.symbol)

Function Word(s:word) symbol  symbol(  [s],    "$word",  "word",empty:seq.symbol)

Function Define(s:seq.word) symbol symbol("DEFINE"+s,"$","?")

Function Define(w:word)symbol  symbol([ "DEFINE"_1,w],"$" ,"?")


Function Fref(s:symbol) symbol symbol("FREF"+fsig.s+module.s,"$fref","?",[s])

Function Optionsym symbol symbol("option(T,word seq)","builtin","?") 

Function EqOp symbol symbol("=(int,int)" ,"builtin","boolean") 

Function PlusOp symbol symbol("+(int,int)" ,"builtin","int") 

Function isnocall(sym:symbol) boolean 
module.sym in ["local","$word","$words","builtin","$constant"] &or last.module.sym ="$"_1   

Function isinOp(s:symbol) boolean
       (fsig.s) in ["in(int, int seq)","in(word, word seq)","=(int,int)","=(word,word)"]


Function value(s:symbol)int toint.(fsig.s)_1


use mangle

Function constantcode(s:symbol) seq.symbol
 if module.s in ["$fref" ,"$constant"] then   zcode.s else empty:seq.symbol

Function options( code:seq.symbol) seq.word  
  if  length.code=0 &or not(last.code=Optionsym) then "" else fsig.(code)_(length.code-1)


------

type program is  record toset:set.symbol

function toset(p:program) set.symbol export

function type:program internaltype export

type programele is record data:seq.symbol

Function target(a:programele) symbol (data.a)_1

Function code(a:programele) seq.symbol subseq(data.a,2,length.data.a)

Function isdefined(a:programele) boolean not.isempty.data.a

Function emptyprogram program program.empty:set.symbol

Function lookupcode(p:program,s:symbol) programele
     let t=findelement(s,toset.p) 
     if isempty.t then  programele.empty:seq.symbol else programele.zcode.t_1

Function  map(p:program,s:symbol,target:symbol,code:seq.symbol) program
    program.replace(toset.p,symbol(fsig.s,module.s,returntype.s,[target]+code))
 
 Function  map(p:program,s:symbol ,code:seq.symbol) program
    map(p,s,s,code)

Function addoption(p:program,s:symbol,option:seq.word) program
  let code=code.lookupcode(p,s)
  let current=asset.getoption.code
  if  current=asset.option then p
  else 
   let newcode=code+Words.toseq(current &cup asset.option)+Optionsym
   map(p,s,newcode)

Function getoption(code:seq.symbol) seq.word
  if not(last.code=Optionsym) then empty:seq.word
  else fsig.code_(length.code-1)


 Function processOption(p:program,t:seq.word) program
  if length.t < 4 &or not(t_1="*"_1) &or  not (t_2 in "PROFILE INLINE STATE NOINLINE") then p
   else
    let modend=findindex(":"_1,t,3)
   let nameend=  findindex("("_1,t,modend+1)
   let paraend= findindex( ")"_1,t,nameend+1)
   let modname=(gettypelist.subseq(t,3,modend-1))_1
   let name= ((gettypelist.subseq(t,modend+1,nameend-1))_1) _1
   let b=subseq(t,nameend+1,paraend-1)
   let args=if b="" then empty:seq.seq.word else gettypelist.subseq(t,nameend+1,paraend-1)
   let ret=(gettypelist.subseq(t,paraend+1,length.t))_1
  let sym= symbol( [name]+"("+@(seperator.",",identity,"",args)+")",modname,  ret) 
    let r=lookupcode(p,sym)
    if modname="builtin"then
     map(p,sym,[Words.[t_2],Optionsym])
    else  
    assert isdefined.r report "Option problem"+t
    addoption(p,sym,[t_2])
    
function printastype(s:seq.word) seq.word
  if length.s=1 then s else [last.s,"."_1]+printastype.subseq(s,1,length.s-1)

function gettypelist(s:seq.word) seq.seq.word  gettype(s,1,"",empty:seq.seq.word)

function  gettype( s:seq.word,i:int,result:seq.word,l:seq.seq.word) seq.seq.word
if i > length.s then  l+result
else 
if s_i=","_1 then gettype(s,i+1,"",l+result ) 
else  
   let j=if  i < length.s &and s_(i+1)="."_1 then  i+2 else i+1 
  gettype(s,j,[s_i]+result,  l)
 
type myinternaltype is record size:int,kind:word,name:word,modname:mytype,subflds:seq.mytype


Function type:myinternaltype internaltype export

Function size(myinternaltype)int export

Function kind(myinternaltype)word export

Function name(myinternaltype)word export

Function modname(myinternaltype)mytype export

Function subflds(myinternaltype)seq.mytype export
  
function myinternaltype(size:int,kind:word,name:word,modname:mytype,subflds:seq.mytype) myinternaltype
export

Function print2(i:myinternaltype) seq.word
  [name.i]+"module:"+print.modname.i+"fld"+@(+,print,"",subflds.i)

Function fsig(symbol)seq.word export

Function module(symbol)seq.word export

Function returntype(symbol)seq.word export

Function type:symbol internaltype export

Function zcode(symbol)seq.symbol export
