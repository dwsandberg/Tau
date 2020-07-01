Module symbol

use seq.seq.char

use seq.char

use libscope

use seq.mytype

use stacktrace

use stdlib

use seq.symbol

use set.symbol

use worddict.symbol

use set.word

use seq.seq.word

Function ?(a:mytype, b:mytype)ordering
 let y =(towords.a)_(length.towords.a) ? (towords.b)_(length.towords.b)
  if y = EQ then
  let x = length.towords.a ? length.towords.b
    if x = EQ then
    if length.towords.a = 2 ∧ (towords.a)_1 = "T"_1
     ∧ not((towords.b)_1 = "T"_1)then
     LT
     else if length.towords.a = 2 ∧ (towords.b)_1 = "T"_1
     ∧ not((towords.a)_1 = "T"_1)then
     GT
     else orderm(towords.a, towords.b, length.towords.a)
    else x
  else y

function orderm(a:seq.word, b:seq.word, i:int)ordering
 if i = 1 then a_1 ? b_1
 else
  let x = a_i ? b_i
   if x = EQ then orderm(a, b, i - 1)else x

Function ?(a:seq.mytype, b:seq.mytype, i:int)ordering
 let o1 = length.a ? length.b
  if o1 = EQ ∧ length.a ≥ i then
  let o2 = a_i ? b_i
    if o2 = EQ then ?(a, b, i + 1)else o2
  else o1

Function ?(a:seq.mytype, b:seq.mytype)ordering ?(a, b, 1)





Function type:symbol internaltype export


Function =(a:symbol, b:symbol)boolean fsig.a = fsig.b  ∧ modname.a = modname.b


/type symbol is record  fsig:seq.word,module:seq.word,returntype:seq.word, zcode:seq.symbol

Function symbol(fsig:seq.word,module:seq.word,returntype:seq.word) symbol 
 symbol(fsig,module,returntype,empty:seq.symbol)
 
 Function fsig(symbol) seq.word export

Function newsymbol(namein:seq.word,modname:mytype, paratypes:seq.mytype,  resulttype:mytype) symbol
 let name=if changeit then namein else [merge(namein)]
let b= (length.towords.modname > 1)  &and  not((towords.modname)_1="T"_1) &and not(abstracttype.modname="para"_1) 
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
 if module.s="$" then toint((fsig.s)_2)  else 
 @(counttrue, =(","_1), if last.fsig.s = ")"_1 then 1 else 0, fsig.s)

function counttrue(i:int, b:boolean)int if b then i + 1 else i

use otherseq.word

Function ?(a:symbol, b:symbol)ordering
 fsig.a ? fsig.b ∧  modname.a ? modname.b

Function ?2(a:symbol, b:symbol)ordering fsig.a ? fsig.b 


Function lookup(dict:set.symbol, name:seq.word, types:seq.mytype)set.symbol
 findelement2(dict, newsymbol( name , mytype."?", types, mytype."?" ))
 
Function lookupfsig(dict:set.symbol, fsig:seq.word)set.symbol
 findelement2(dict,  symbol( fsig ,  "?",  "?" ))


Function printdict(s:set.symbol)seq.word @(+, print,"", toseq.s)

Function print(s:symbol)seq.word
   name.s  + "(" + @(seperator.",", print,"", paratypes.s)
 + ")"
 + print.resulttype.s
 + "module:"
 + print.modname.s

function replaceTinname(with:mytype, name:word)word
 let x = decodeword.name
  if subseq(x, length.x - 1, length.x)
  in [ //.T // [ char.46, char.84], //:T // [ char.58, char.84]]then
  encodeword(subseq(x, 1, length.x - 1) + @(+, decodeword, empty:seq.char, print.with))
  else name

Function toplaceholders(  s:seq.symbol) seq.sig @(+,toplaceholder,empty:seq.sig,s)
    
Function toplaceholder( s:symbol) sig   
 if module.s="$fref" then   FREFsig.toplaceholder.(zcode.s)_1 else 
placeholder(fsig.s,module.s,returntype.s)


use funcsig

use seq.sig

type mapele is record   s:symbol, pair:seq.sig  

Function type:mapele internaltype export

Function s(mapele) symbol export

Function pair(mapele) seq.sig export

function replaceT(with:seq.word,s:word) seq.word if "T"_1=s then with else [s]

function replaceT(with:seq.word,s:seq.word) seq.word @(+,replaceT.with,"",s)

Function replateTfsig(with:seq.word,fsig:seq.word) seq.word
if changeit then [fsig_1]+replaceT(  with,subseq(fsig,2,length.fsig)) else
[replaceTinname(mytype.with, fsig_1)]+replaceT( with,subseq(fsig,2,length.fsig))

Function replaceTsymbol2(with:mytype, s:symbol) mapele
  if with=mytype."T" then mapele(s,[toplaceholder.s,toplaceholder.s ])
 else
   let x=symbol(replateTfsig(towords.with,fsig.s), replaceT(towords.with,module.s), replaceT(towords.with, returntype.s))
  mapele(x,[toplaceholder.x,toplaceholder.s ])
  
Function replaceTsymbol(with:mytype, s:symbol) symbol
  if with=mytype."T" then s
 else
   symbol(replateTfsig(towords.with,fsig.s), replaceT(towords.with,module.s), replaceT(towords.with, returntype.s))
  

type myinternaltype is record size:int,kind:word,name:word,modname:mytype,subflds:seq.mytype

Function myinternaltype(size:int,kind:word,name:word,modname:mytype,subflds:seq.mytype) myinternaltype export

Function size(myinternaltype) int export

Function kind(myinternaltype) word export

Function name(myinternaltype) word export

Function modname(myinternaltype) mytype  export

Function subflds(myinternaltype) seq.mytype export

Function type:myinternaltype internaltype export 

use seq.libsym

use seq.firstpass

use seq.libmod

Function type:mytype internaltype export

Function towords(mytype)seq.word export

Function mytype(seq.word)mytype export

Function abstracttype(m:mytype)word export

Function parameter(m:mytype)mytype export

Function print(p:mytype)seq.word export

Function =(t:mytype, b:mytype)boolean export


Function replaceT(with:mytype, m:mytype)mytype export

Function iscomplex(a:mytype)boolean export

Function type:firstpass internaltype export

type firstpass is record modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, 
unbound:set.symbol,types:seq.myinternaltype

Function firstpass(modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, 
unboundx:set.symbol,types:seq.myinternaltype) firstpass
 export
 
use seq.myinternaltype

Function exportmodule(firstpass)boolean false

Function modname(firstpass)mytype export

Function defines(firstpass)set.symbol export

Function exports(firstpass)set.symbol export

Function uses(firstpass)seq.mytype export


Function unboundexports(firstpass)seq.symbol export

Function unbound(firstpass)set.symbol export

Function types(firstpass) seq.myinternaltype export

_______________________________      
     
   
function tosymbol(ls:libsym)symbol
    symbol(fsig.ls,module.ls,returntype.ls)
    
  
function  addlibsym(p:prg,ls:libsym) prg
    map(p,toplaceholder.tosymbol.ls,
   scannew(instruction.ls,1,empty:seq.sig))

 
function tofirstpass(m:libmod)  seq.firstpass
 [ firstpass(mytype.if parameterized.m then"T" + modname.m else [ modname.m], uses.m, 
 @(+, tosymbol, empty:set.symbol, defines.m), 
 @(+, tosymbol, empty:set.symbol, exports.m), empty:seq.symbol, empty:set.symbol,
 @(+,libtypes,empty:seq.myinternaltype,defines.m))]
 
 
 
  function alllibsym(l:liblib) seq.libsym    @(+,defines, empty:seq.libsym,mods.l)+@(+,exports, empty:seq.libsym,mods.l)

 Function otherlibsyms(l:seq.liblib) prg    
       @(addlibsym,identity,emptyprg,toseq(asset.@(+,alllibsym, empty:seq.libsym,l)-knownlibsyms.l))
 
        function knownlibsyms(l:liblib) seq.libsym   defines.last.mods.l
        
        function knownlibsyms(l:seq.liblib) set.libsym asset.@(+,knownlibsyms, empty:seq.libsym,l)

use set.libsym




function addfirstpass(s:seq.firstpass,l:seq.liblib) seq.firstpass  
  if isempty.l then s else  s+@(+, tofirstpass, empty:seq.firstpass, mods.l_1)

function addfirstpass(l: liblib) seq.firstpass  
 @(+, tofirstpass, empty:seq.firstpass, mods.l)

  
Function dependentlibs(dependentlibs:seq.word)   seq.liblib @(+,filter(dependentlibs),empty:seq.liblib   , loadedlibs)


Function libsymbols(l:seq.liblib) prg  @(addknown,identity,emptyprg,l)


function addknown(p:prg,l:liblib) prg  @(addlibsym,  identity, p, defines.last.mods.l)


use seq.liblib

function  libtypes(l:libsym)  seq.myinternaltype
  if returntype.l="internaltype" &and  subseq(instruction.l,length.instruction.l-1,length.instruction.l)="RECORD 5" 
  then 
    [asmyinternaltype(scannew(instruction.l,1,empty:seq.sig))]
   else empty:seq.myinternaltype

     use seq.fsignrep


Function libfirstpass(l:seq.liblib) seq.firstpass
  @(+,addfirstpass, empty:seq.firstpass   , l)


function filter(s:seq.word,l:liblib)  seq.liblib   if (libname.l)_1 in s then [l] else empty:seq.liblib

   Function asmyinternaltype(     s:seq.sig) myinternaltype
     let l=length.s
     assert s_l =RECORD.5 report "internaltype"+print.s+stacktrace
     let rep1=decode.s_(l-1)
     assert (fsig.rep1)_1="RECORD"_1 report "internaltype"+print.s
     let noflds=toint.(fsig.rep1)_2-2
      let t1=@(+,decode,empty:seq.fsignrep,subseq(s,l-noflds-1,l-2))
      let subflds=@(+,mytype,empty:seq.mytype,@(+,fsig,empty:seq.seq.word,t1))
      let size=value.s_1
      let kind=fsig.decode.s_2
      let name=fsig.decode.s_3
      let modname=fsig.decode.s_4
      myinternaltype(size,kind_1,name_1,mytype.modname,subflds)


Function scannew(s:seq.word,i:int,result:seq.sig) seq.sig
  if i > length.s then  result 
  else 
   let this = s_i 
   if this ="LOCAL"_1  then          scannew(s,i+2,result+sig( [ s_(i+1)],  "local" ,"?"))
      else if this = "LIT"_1 then    scannew(s,i+2,result+ lit.toint.s_(i+1))
      else if this = "WORD"_1 then   scannew(s,i+2,result+wordsig.s_(i+1))
      else if this = "RECORD"_1 then scannew(s,i+2,result+ RECORD.toint.s_(i+1))
      else if this = "APPLY"_1 then  scannew(s,i+2,result+ apply.toint.s_(i+1))
      else if this = "BLOCK"_1 then  scannew(s,i+2,result+ block.toint.s_(i+1))
      else if this = "EXITBLOCK"_1 then scannew(s,i+2,result+ exit)
      else if this = "BR"_1 then     scannew(s,i+2,result+ br)
      else if this = "DEFINE"_1 then scannew(s,i+2,result+ define.s_(i+1) )
      else if this = "COMMENT"_1 then scannew(s, i + 2 + toint.s_(i + 1), result)
      else if this = "IDXUC"_1 then   scannew( s, i + 1,  result + IDXUC)
      else if this = "SET"_1 then scannew( s, i + 2,  result)
      else if this = "WORDS"_1 then
         let l = toint.s_(i + 1)
         scannew( s, i + 2 + l,   result + wordssig.subseq(s, i + 2, i + 1 + l))
    else   if this="builtinZinternal1Zwordzseq"_1 then 
   // comment keeps this from being striped off //   scannew(s, i + 1,   result)
    else      let newfref=this = "FREF"_1
      let q=if newfref then s_(i+1) else this
      let f=findencode(e2cached, cached( q ,eqOp))  
      if not.isempty.f then  
          scannew(s, i + if newfref then 2 else 1,  result + if newfref then FREFsig.s.(f_1)  else s.(f_1))
       else  
        let d = codedown.q
         assert length.d > 1 report"BBB 3" + q+s
       if d_2=" local" then 
              scannew(s, i + 1,  result + sig(d_1, "local","?"))
          else if last.d_2 = "para"_1 then
                 scannew( s, i + 1, result +sig([ d_2_1], "local", "?"))
         else if  d_2="builtin" &and 
          q in "assertZbuiltinZwordzseq  IDXUCZbuiltinZintZint 
         callidxZbuiltinZintZTzseqZint abortedZbuiltinZTzprocess optionZbuiltinZTZwordzseq 
         addZbuiltinZTzerecordZTzencodingrep castZbuiltinZTzseqZintZint 
         allocatespaceZbuiltinZint 
         setfld2ZbuiltinZTzseqZintZT getinstanceZbuiltinZTzerecord " then
          let newsig=
sig( if length.d=2 then d_1 else d_1+"("+@(seperator.",", identity, "", subseq(d, 3, length.d))+")", d_2,"?")
            let discard= encode(e2cached,cached( q ,newsig))
                 scannew( s, i + if newfref then 2 else 1,  result + 
                   if newfref then FREFsig.newsig  else newsig)
         else if s_i = "FREF"_1 then  scannew( s, i+2, result+FREFsig.toPH.s_(i+1) )
  else  scannew( s, i+1, result+toPH.s_(i) )

   type cached is record      key: word,s:sig
  
 function assignencoding(l:int, s:cached)int assignrandom(l,s)
 
 function =(a:cached,b:cached) boolean key.a=key.b
 
 function hash(a:cached) int hash.key.a
 
 type  e2cached is encoding cached

use seq.cached 

  
  function toPH(w:word) sig
let d= codedown.w
toplaceholder.newsymbol(  d_1, mytype.d_2 ,@(+, mytype, empty:seq.mytype, subseq(d, 3, length.d)),mytype."?")
  
---------------

Function deepcopysym (type:mytype) symbol
newsymbol("deepcopy"  ,mytype(towords.type + "process"), [type], type)

Function Idxuc symbol  symbol("IDXUC(int,int)","builtin", "?")

Function Emptyseq seq.symbol [Lit0,Lit0,Record.2]

Function pseqidxsym(type:mytype) symbol
    newsymbol("_" , mytype(towords.type + "seq"_1),[ mytype(towords.type + "pseq"_1), mytype."int"],type)
    
Function Record(i:int) symbol symbol([ "RECORD"_1,toword.i],    "$",  "?",empty:seq.symbol)

Function Apply(i:int) symbol symbol([ "APPLY"_1,toword.i],    "$",  "?",empty:seq.symbol)

Function Block(i:int) symbol symbol([ "BLOCK"_1,toword.i],    "$",  "?",empty:seq.symbol)


Function Exit  symbol symbol(  "EXITBLOCK 1",    "$",  "?",empty:seq.symbol)

Function Br    symbol symbol( "BR 3", "$",  "?",empty:seq.symbol)

Function Lit(i:int)  symbol symbol(  [toword.i],    "$int",  "int",empty:seq.symbol)

Function Local(i:int)  symbol symbol(  [toword.i],    "local",  "?",empty:seq.symbol)


Function Words(s:seq.word) symbol  symbol(  s,    "$words",  "word seq",empty:seq.symbol)

Function Word(s:word) symbol  symbol(  [s],    "$word",  "word",empty:seq.symbol)

Function Define(s:seq.word) symbol symbol("DEFINE"+s,"$","?")

Function Fref(s:symbol) symbol symbol("FREF"+fsig.s+module.s,"$fref","?",[s])

Function Lit0 symbol symbol(  "0",    "$int",  "int",empty:seq.symbol)


Function Lit2 symbol symbol(  "2",    "$int",  "int",empty:seq.symbol)

Function Lit3 symbol symbol(  "3",    "$int",  "int",empty:seq.symbol)

Function astext(s:seq.symbol) seq.word @(+,astext,"",s)

Function astext(s:symbol) seq.word 
if module.s = "$" then fsig.s
else if module.s ="$int" then "LIT"+fsig.s
else if module.s ="$words" then "WORDS"+toword.length.fsig.s+fsig.s
else if module.s ="$word" then "WORD"+fsig.s
else if module.s="$fref" then "FREF"+astext.(zcode.s)_1
else if module.s="local" then "LOCAL"+fsig.s
else [mangledname.s]



use mangle

------

type program is  record toset:set.symbol

type programele is record data:seq.symbol

function target(a:programele) symbol (data.a)_1

function code(a:programele) seq.symbol subseq(data.a,2,length.data.a)

functiom isdefined(a:programele) boolean not.isempty.data.a


function lookupcode(p:program,s:symbol) programele
     let t=findelement(s,toset.p) 
     if isempty.t then  programele.empty:seq.symbol else programele.zcode.t_1

function  map(p:program,s:symbol,target:symbol,code:seq.symbol) program
    program.replace(toset.p,symbol(fsig.s,module.s,returntype.s,[target]+code))




 
