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


Function type:programele internaltype export



Function type:symbol internaltype export


Function =(a:symbol, b:symbol)boolean flags.a=flags.b &and fsig.a = fsig.b  ∧ modname.a = modname.b



type symbol is record  fsig:seq.word,module:seq.word,
returntype:seq.word, zcode:seq.symbol ,flags:bits


Function extrabits(s:symbol) int toint.flags.s

Function fsighash(s:symbol) int  toint(flags.s >> 4)

Function extrabits(fsig:seq.word,flags:bits) bits 
   bits.hash(fsig) << 4 &or flags
 

Function symbol(fsig:seq.word,module:seq.word,returntype:seq.word) symbol 
 symbol(fsig,module,returntype,empty:seq.symbol)
 
 Function symbol(fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol) symbol 
    symbol(fsig,module,returntype,zcode,  extrabits(fsig,bits.0))

Function symbol(fsig:seq.word,module:seq.word,returntype:seq.word, flag:bits) symbol 
    symbol(fsig,module,returntype,empty:seq.symbol, extrabits(fsig,flag))
 
 
 
 Function fsig(symbol) seq.word export

Function newsymbol(name:seq.word,modname:mytype, paratypes:seq.mytype,  resulttype:mytype) symbol
  let b= (length.towords.modname > 1)  &and  not((towords.modname)_1="T"_1) &and not(ispara.modname) 
  let paratyps= if b then @(+,replaceT(parameter.modname),empty:seq.mytype,paratypes)  else paratypes
  let sym=symbol(if length.paratyps = 0 then name else  name + "(" + @(seperator.",", towords,"", paratyps)  + ")"
  ,towords.modname,
  towords.if b then    replaceT(parameter.modname,resulttype) else resulttype
  ,empty:seq.symbol)
 sym


Function name(s:symbol) seq.word  
let j=findindex("("_1, fsig.s)  
if j > length.fsig.s then fsig.s
 else
subseq(fsig.s, 1, j - 1)






Function paratypes(s:symbol)seq.mytype 
 @(+, mytype, empty:seq.mytype, paratypesastext.s)

function paratypesastext(s:symbol) seq.seq.word
let a= fsig.s 
  if length.a < 4 then empty:seq.seq.word
  else 
  break(","_1, subseq(a, 1, length.a - 1), findindex("("_1, a) + 1 )


  



Function modname(s:symbol)mytype mytype.module.s

Function resulttype(s:symbol)mytype mytype.returntype.s

Function nopara(s:symbol)int 
 if isconst.s &or islocal.s then 0 else
 if isspecial.s then 
  if  (fsig.s)_1= "DEFINE"_1 then 1 
  else if (fsig.s)_1 in "RECORD"   then
     @(counttrue, =(","_1), 1, fsig.s)
  else  toint((fsig.s)_2)  
 else 
 @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

function counttrue(i:int, b:boolean)int if b then i + 1 else i

use otherseq.word

Function ?(a:symbol, b:symbol)ordering     fsighash.a ? fsighash.b   
&and    fsig.a ? fsig.b ∧  module.a ? module.b

Function ?2(a:symbol, b:symbol)ordering   fsighash.a ? fsighash.b   &and    fsig.a ? fsig.b 


Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
 findelement2(dict, newsymbol( name , mytype."?", types, mytype."?" ))
 
Function lookupfsig(dict:set.symbol, fsig:seq.word)set.symbol
 findelement2(dict,  symbol( fsig ,  "?",  "?" ))

Function printdict(s:set.symbol)seq.word @(+, print,"", toseq.s)



type mapele is record   s:symbol,target:symbol  

Function type:mapele internaltype export

Function s(mapele) symbol export

Function key(a:mapele) symbol   s.a

Function target(a:mapele) symbol  export


function replaceT(with:seq.word,s:word) seq.word if "T"_1=s then with else [s]

function replaceT(with:seq.word,s:seq.word) seq.word @(+,replaceT.with,"",s)


Function replaceTsymbol2(with:mytype, s:symbol) mapele  mapele(replaceTsymbol(with, s),s )
  
Function replaceTsymbol(with:mytype, s:symbol) symbol
  if with=mytype."T" then s
 else
let newfsig=    
    let j=findindex("("_1, fsig.s) 
   replaceT (if towords.with="" then "" else print.with,  subseq(fsig.s,1,j-1)) +replaceT( towords.with,subseq(fsig.s,j,length.fsig.s))
   symbol(newfsig, replaceT(towords.with,module.s), replaceT(towords.with, returntype.s),zcode.s)
  

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
symbol([name],[ "para"_1,toword.parano,"$"_1],towords.type,specialbit)

function ispara(s:mytype) boolean  ( towords.s)_1="para"_1 &and last.towords.s="$"_1  

Function deepcopysym (type:mytype) symbol
newsymbol("deepcopy"  ,mytype(towords.type + "builtin"), [type], type)


Function IDXR symbol  symbol("IDXR(int,int)","builtin", "real")

Function IDXI symbol  symbol("IDXI(int,int)","builtin", "int")

Function IDXP symbol  symbol("IDXP(int,int)","builtin", "ptr")

Function  CALLIDXI  symbol symbol("callidxI( T seq,int)","builtin", "int")

Function  CALLIDXR  symbol symbol("callidxR( T seq,int)","builtin", "real")

Function  CALLIDXP  symbol symbol("callidxP( T seq,int)","builtin", "ptr")


Function Emptyseq seq.symbol [Lit0,Lit0,symbol( "RECORD(int,int)",    "$record",  "ptr",specialbit)
]

Function pseqidxsym(type:mytype) symbol
    newsymbol("_" , mytype(towords.type + "seq"_1),[ mytype(towords.type + "pseq"_1), mytype."int"],type)
    
use otherseq.mytype

 
Function  Sequence(len:int,typ:seq.word) symbol
  Record([mytype."int",mytype."int"]+constantseq(len,mytype.typ))

Function Record(types:seq.mytype) symbol
symbol( "RECORD("+@(seperator.",",towords,"",types)+")",    "$record",  "ptr",specialbit)

Function Apply(i:int) symbol     symbol([ "APPLY"_1,toword.i],    "? $apply",  "?",specialbit)

Function ApplyI(i:int) symbol     symbol([ "APPLYI"_1,toword.i],    "int $apply",  "int",specialbit)

Function ApplyR(i:int) symbol     symbol([ "APPLYR"_1,toword.i],    "real $apply",  "real",specialbit)

Function ApplyP(i:int) symbol     symbol([ "APPLYP"_1,toword.i],    "ptr $apply",  "ptr",specialbit)



Function Block(type:mytype ,i:int) symbol symbol( "BLOCK"+toword.i, towords.type+"$block",  towords.type,specialbit)



function bpara(i:int,result:seq.word) seq.word
  if i=1 then result else bpara(i-1,result+",?")


Function loopblock(i:int)symbol  symbol([ "LOOPBLOCK"_1,toword.i],   "$loopblock",  "?",specialbit)

Function continue(i:int)symbol   symbol([ "CONTINUE"_1,toword.i],    "$continue",   "?",specialbit)

use otherseq.seq.word

   
Function Constant2(args:seq.symbol) symbol
//  let args=subseq(argsin,1,length.argsin-1) //
  let fsig="CONSTANT" +     toword.valueofencoding.encode(symbolconstant(args))  
   symbol(fsig , "$constant",  "ptr",args,extrabits(fsig,constbit) )

   
Function isrecordconstant(s:symbol) boolean module.s= "$constant"
   

function hash(s:seq.symbol) int hash.@(+,sigandmodule,"",s) 

function assignencoding(a:int, symbolconstant) int a+1


type symbolconstant is record toseq:seq.symbol

use encoding.symbolconstant

function =(a:symbolconstant,b:symbolconstant) boolean  toseq.a=toseq.b

function hash(a:symbolconstant) int hash(toseq.a)
 

Function isconstantorspecial(s:symbol)boolean isconst.s &or isspecial.s

Function isnocall(sym:symbol) boolean 
isconst.sym &or isspecial.sym &or    module.sym="builtin"   

function specialbit bits bits.4

function constbit bits bits(1)

function =(a:bits,b:bits) boolean toint.a=toint.b

Function isspecial(s:symbol) boolean (flags.s &and specialbit) = specialbit

Function isconst(s:symbol)boolean (flags.s &and constbit) = constbit


Function islit(s:symbol) boolean   module.s ="$int" &or module.s ="$real"

Function isFref(s:symbol) boolean   module.s ="$fref"

function  sigandmodule(s:symbol) seq.word   fsig.s+module.s

Function Exit  symbol symbol(  "EXITBLOCK 1",    "$exitblock",  "?",specialbit)

Function Br    symbol symbol( "BR 3", "$br",  "?",specialbit)

use bits

Function Local(i:int)  symbol Local.toword.i 

Function Local(w:word)  symbol symbol(  [w] ,    "local $",  "?",specialbit)

Function Local(name:seq.word,type:mytype) symbol  symbol( name ,"local $", towords.type,specialbit)

Function islocal(s:symbol) boolean module.s="local $"

Function Reallit(i:int)  symbol symbol(  [toword.i],    "$real",  "real",constbit)


Function Lit(i:int)  symbol symbol(  [toword.i],    "$int",  "int",constbit)

Function Lit0 symbol symbol(  "0",    "$int",  "int",constbit)

Function Lit2 symbol symbol(  "2",    "$int",  "int",constbit)

Function Lit3 symbol symbol(  "3",    "$int",  "int",constbit)

Function Words(s:seq.word) symbol  symbol(  s,    "$words",  "word seq",constbit)

Function Word(s:word) symbol  symbol(  [s],    "$word",  "word",constbit)

Function Define(s:seq.word) symbol symbol("DEFINE"+s,"$define","?",specialbit)

Function Define(w:word)symbol  symbol([ "DEFINE"_1,w],"$define" ,"?",specialbit)


Function Fref(s:symbol) symbol 
let fsig="FREF"+fsig.s+module.s
symbol(fsig,"$fref","?",[s],extrabits(fsig,constbit))

Function Optionsym symbol symbol("option(T,word seq)","builtin","?") 

Function EqOp symbol symbol("=(int,int)" ,"builtin","boolean") 

Function PlusOp symbol symbol("+(int,int)" ,"builtin","int") 

Function isinOp(s:symbol) boolean
       (fsig.s) in ["in(int, int seq)","in(word, word seq)","=(int,int)","=(word,word)"]

Function isblock(s:symbol)boolean  last.module.s="$block"_1  

Function isrecord(s:symbol)boolean  module.s  = " $record"  

Function isapply(s:symbol)boolean  last.module.s="$apply"_1  

Function isloopblock(s:symbol)boolean  module.s  = "$loopblock"  

Function iscontinue(s:symbol)boolean  module.s  = "$continue" 

Function isdefine(s:symbol)boolean   module.s  ="$define"  

Function isexit(s:symbol)boolean  module.s = "$exitblock" 

Function isbr(s:symbol)boolean   module.s =  "$br"  

Function value(s:symbol)int toint.(fsig.s)_1


use mangle

Function constantcode(s:symbol) seq.symbol
 if isFref.s   then   zcode.s 
else if isrecordconstant.s then   subseq(zcode.s ,1,length.zcode.s-1)
 else empty:seq.symbol
 
Function basesym(s:symbol) symbol
   if  module.s="$fref" then  
    (zcode.s)_1  else s

Function options( code:seq.symbol) seq.word  
  if  length.code=0 &or not(last.code=Optionsym) then "" else fsig.(code)_(length.code-1)


------

type program is  record toset:set.symbol

Function &cap(p:program,a:set.symbol) program   program(toset.p &cap a)

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

Function isbuiltin(a:seq.word) boolean   a="builtin" 

Function isbuiltin(a:mytype) boolean isbuiltin.towords.a 

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
    if isbuiltin.modname then
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
  
  Function  lookuptype(defined:seq.myinternaltype,typ:mytype) seq.myinternaltype
   if typ =mytype."int" &or typ=mytype."real"      then 
   [ myinternaltype(1,abstracttype.typ,abstracttype.typ,mytype."builtin",empty:seq.mytype)]
else
     findelement(    myinternaltype(0,"?"_1,abstracttype.typ,mytype(towords.parameter.typ+"?") ,empty:seq.mytype), defined)


Function fsig(symbol)seq.word export

Function module(symbol)seq.word export

Function returntype(symbol)seq.word export

Function type:symbol internaltype export

Function zcode(symbol)seq.symbol export

Function print(f:symbol)seq.word
 let module=module.f 
let fsig=fsig.f
if  islocal.f &or ispara.mytype.module.f then [ merge.(["%"_1]+fsig)]
   else if  islit.f then fsig
   else if module="$words" then if '"'_1 in fsig then "'" + fsig + "'" else '"' + fsig + '"'
   else if module="$word" then "WORD"+fsig
    else if isspecial.f then 
   if fsig_1 in "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then fsig + " &br"else fsig
   else if module=" $constant"  then fsig 
   else if isFref.f then "FREF"+print.(constantcode.f)_1
    else   (if last.fsig=")"_1 then  fsig  else  fsig+"()")+print.mytype.module
    
   / Function print2(f:symbol)seq.word
 let module=module.f 
let fsig=fsig.f
if  islocal.f &or ispara.mytype.module.f then [ merge.(["%"_1]+fsig)]
   else if  islit.f then fsig
   else if module="$words" then if '"'_1 in fsig then "'" + fsig + "'" else '"' + fsig + '"'
   else if module="$word" then "WORD"+fsig
    else if isspecial.f then 
    if fsig_1 in "BLOCK" then fsig + module+ " &br"
    else   if fsig_1 in "BLOCK EXITBLOCK BR LOOPBLOCK FINISHLOOP CONTINUE"then fsig + " &br"else fsig
   else if module=" $constant"  then fsig+@(+,print,"",constantcode.f) 
   else if isFref.f then "FREF"+print.(constantcode.f)_1
    else   (if last.fsig=")"_1 then  fsig  else  fsig+"()")+print.mytype.module
 
Function print(p:program, i:symbol)seq.word
 let d=lookupcode(p,i) if not.isdefined.d then print(i) else print(i)+ @(+, print,"",code.d ) 


    Function parakind(alltypes:seq.myinternaltype,type:mytype) word
      if  abstracttype.type in  "none int ptr real" then abstracttype.type
      else if  abstracttype.type in " encoding " then "int"_1
      else if abstracttype.type in "seq erecord internaltype process encodingstate encodingrep"  then "ptr"_1
      else 
      let k=lookuptype(alltypes,type) 
      assert not.isempty.k report "TYPE LOOKUP parakind"+print.type 
      let kind=kind.k_1
       assert kind in "int real ptr seq" 
       report "unknown type parakind "+print.type +"place" 
       if kind in "seq" then "ptr"_1 else    kind
