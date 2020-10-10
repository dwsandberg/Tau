#!/usr/local/bin/tau

run mylib testnew 

Module codetemplates

use seq.myinternaltype

use bitpackedseq.bit

use seq.bit

use bits

use fileio


use seq.seq.int

use internalbc

use persistant

use llvm

use llvmconstants

use otherseq.llvmtype

use seq.llvmtype


use encoding.match5

use seq.match5

use stdlib

use blockseq.templatepart

use blockseq.seq.templatepart

use seq.templatepart

use textio

use blockseq.word

use seq.symbol

use seq.seq.symbol

use seq.mytype

Function tollvmtype(alltypes:seq.myinternaltype,s:symbol) llvmtype
   if fsig.s="option(T, word seq)" &or not.check then    function.constantseq(nopara.s + 2, i64) else 
 // assert not( modname.s=mytype."builtin") report "llvmtype error "+print.s //
  function.@(+,tollvmtype.alltypes, [tollvmtype(alltypes,resulttype.s),i64],paratypes.s)
  
   assert not(mangledname.s="printZUTF8ZintZreal"_1 )report "here"+print.a
   a
 
    
     function tollvmtype(alltypes:seq.myinternaltype,s:mytype) llvmtype
        let kind=parakind(alltypes,s)
          if  kind="int"_1 then i64
          else if kind="real"_1 then   double   
        else   // ptr. // i64

function wordstype llvmtype array(-1, i64)

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Function type:match5 internaltype export

Function length(match5)int // no of instruction that return results // export

Function action(match5)word export

Function arg(match5)int export


type match5 is record fullinst:seq.word, length:int, parts:seq.templatepart, action:word, arg:int,code:seq.symbol
,functype:llvmtype

function match5 ( fullinst:seq.word, length:int, parts:seq.templatepart, action:word, arg:int) match5
 match5(fullinst,length,parts,action,arg,empty:seq.symbol,i64)

Function code(match5) seq.symbol export

Function functype(match5) llvmtype export

Function type:symbol internaltype export

Function fullinst(match5) seq.word export

 
Function type:program internaltype export

use symbol

Function _(m:seq.match5,d:symbol) match5  
let full=if isconstantorspecial.d then
    fsig.d+module.d else [mangledname.d,toword.nopara.d]
 let e=  findencode(match5(full, 0, empty:seq.templatepart,"NOTFOUND"_1, 0))
 assert not.isempty.e report "LL"+fsig.d+module.d
e_1

Function mangledname(m:match5)word    (fullinst.m)_1
 
function =(a:match5, b:match5)boolean fullinst.a = fullinst.b

function hash(a:match5)int hash.fullinst.a

function assignencoding(l:int, a:match5) int l+1

Function options(match5map:seq.match5,m:match5) seq.word
options.code.m

use encoding.match5


Function check boolean false

function table seq.match5
 let z=if check then
  [ match5(2,"IDXRZbuiltinZintZint"_1, 4, CAST(1, ibcsub1, typ.ptr.i64, CASTINTTOPTR) + GEP(2, 1, typ.i64, -1, ibcsub2)
  + LOAD(3, -2, typ.i64, align8, 0)+CAST(4, -3, typ.double, 11))
  ,  match5(1,"sqrtZbuiltinZreal"_1, 1, CALL(1, 0, 32768, typ.function.[ double, double], symboltableentry(merge."llvm.sqrt.f64",function.[ double, double]),ibcsub1))
  ,  match5(1,"sinZbuiltinZreal"_1, 1, CALL(1, 0, 32768, typ.function.[ double, double], symboltableentry(merge."llvm.sin.f64",function.[ double, double]),ibcsub1))
  ,  match5(1,"cosZbuiltinZreal"_1, 1, CALL(1, 0, 32768, typ.function.[ double, double], symboltableentry(merge."llvm.cos.f64",function.[ double, double]),ibcsub1))
,match5(1,"intpartZbuiltinZreal"_1, 1,   CAST(2, -1, typ.i64, // fptosi double // 4))
,match5(1,"torealZbuiltinZint"_1, 1, // sitofp // CAST(1, ibcsub1, typ.double, 6) )
,  match5(2,"Q2DZbuiltinZrealZreal"_1, 1,   BINOP(1, ibcsub1, ibcsub2, 1))
,  match5(2,// + //"Q2BZbuiltinZrealZreal"_1, 1,   BINOP(1, ibcsub1, ibcsub2, 0))
,  match5(2,// * //"Q2AZbuiltinZrealZreal"_1, 1,   BINOP(1, ibcsub1, ibcsub2, 2))
,  match5(2,// / op //"Q2FZbuiltinZrealZreal"_1, 1,   BINOP(1, ibcsub1, ibcsub2, 4))
 , match5(1,"casttorealZbuiltinZint"_1, 0, CAST(1, ibcsub1, typ.double, 11))
 ,match5(1,"representationZbuiltinZreal"_1, 1, CAST(2, -1, typ.i64, 11)) 
]
 else 
   [match5(2,"IDXRZbuiltinZintZint"_1, 3, CAST(1, ibcsub1, typ.ptr.i64, CASTINTTOPTR) + GEP(2, 1, typ.i64, -1, ibcsub2)+ LOAD(3, -2, typ.i64, align8, 0))
   ,  match5(1,"sqrtZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)
+ CALL(2, 0, 32768, typ.function.[ double, double], symboltableentry(merge."llvm.sqrt.f64",function.[ double, double]),-1)
+ CAST(3, -2, typ.i64, 11))
, match5(1,"sinZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)
+ CALL(2, 0, 32768, typ.function.[ double, double], symboltableentry(merge."llvm.sin.f64",function.[ double, double]), -1)
+ CAST(3, -2, typ.i64, 11))
, match5(1,"cosZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)
+ CALL(2, 0, 32768, typ.function.[ double, double], symboltableentry(merge."llvm.cos.f64",function.[ double, double]), -1)
+ CAST(3, -2, typ.i64, 11))
,match5(1,"intpartZbuiltinZreal"_1, 2, CAST(1, ibcsub1, typ.double, 11) + CAST(2, -1, typ.i64, // fptosi double // 4))
,match5(1,"torealZbuiltinZint"_1, 2, // sitofp // CAST(1, ibcsub1, typ.double, 6) + CAST(2, -1, typ.i64, 11))
,match5(2,          "Q2DZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + BINOP(3, -1, -2, 1)+ CAST(4, -3, typ.i64, 11))
,match5(2,// + //   "Q2BZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + BINOP(3, -1, -2, 0)+ CAST(4, -3, typ.i64, 11))
,match5(2,// * //   "Q2AZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + BINOP(3, -1, -2, 2)+ CAST(4, -3, typ.i64, 11))
,match5(2,// / op //"Q2FZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + BINOP(3, -1, -2, 4)+ CAST(4, -3, typ.i64, 11))
 , match5(1,"casttorealZbuiltinZint"_1, 0, emptyinternalbc)
 ,match5(1,"representationZbuiltinZreal"_1, 0, emptyinternalbc)
]
let t = z+ [  match5(1,"getseqtypeZbuiltinZTzseq"_1, 2, CAST(1, ibcsub1, typ.ptr.i64, CASTINTTOPTR)  
+ LOAD(2, -1, typ.i64, align8, 0))
, match5(2,"IDXIZbuiltinZintZint"_1, 3, CAST(1, ibcsub1, typ.ptr.i64, CASTINTTOPTR) + GEP(2, 1, typ.i64, -1, ibcsub2)
+ LOAD(3, -2, typ.i64, align8, 0))
, match5(2,"IDXPZbuiltinZintZint"_1, 3, CAST(1, ibcsub1, typ.ptr.i64, CASTINTTOPTR) + GEP(2, 1, typ.i64, -1, ibcsub2)
+ LOAD(3, -2, typ.i64, align8, 0))
, match5(2,// ? //"Q3FZbuiltinZintZint"_1, 5, CMP2(1, ibcsub1, ibcsub2, 39) + CAST(2, -1, typ.i64, CASTZEXT) + CMP2(3, ibcsub1, ibcsub2, 38)
+ CAST(4, -3, typ.i64, CASTZEXT)
+ BINOP(5, -2, -4, 0))
, match5(3,"castZbuiltinZTzseqZintZint"_1, 2, 
    BINOP(1, ibcsub2, C64.3, // shift left // 7) 
    + BINOP(2, ibcsub1, -1, 0))
, match5(2,"Q3EZbuiltinZintZint "_1, 2, CMP2(1, ibcsub1, ibcsub2, 38) + CAST(2, -1, typ.i64, CASTZEXT))
, match5(1,"notZbuiltinZboolean"_1, 1, BINOP(1, ibcsub1, C64.1, 12))
, // include aborted here so does not show up in profile results match5("abortedZbuiltinZTzprocess"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64, i64], C."abortedZbuiltinZTzprocess", -1, ibcsub1)), Including this as a template causes subtle compile errors //
match5(2,// = // "Q3DZbuiltinZintZint"_1, 2, CMP2(1, ibcsub1, ibcsub2, 32) + CAST(2, -1, typ.i64, CASTZEXT))
, match5(2, "Q2DZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 1 ))
, match5(2,// + // "Q2BZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 0 ))
, match5(2,// * // "Q2AZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 2 ))
, match5(2,// / op //"Q2FZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 4 ))
, match5(2,// ? //"Q3FZbuiltinZrealZreal"_1, 7, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + CMP2(3, -1, -2, 3)
+ CAST(4, -3, typ.i64, CASTZEXT)
+ CMP2(5, -1, -2, 2)
+ CAST(6, -5, typ.i64, CASTZEXT)
+ BINOP(7, -4, -6, 0 ))
, match5(2,"Q3CQ3CZbuiltinZbitsZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, // SHL // 7 ))
, match5(2,"Q3EQ3EZbuiltinZbitsZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, // LSHR // 8 ))
, match5(2,"Q02227ZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // AND // 10 ))
, match5(2,"Q02228ZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // OR // 11 ))
, match5(2,"xorZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // XOR // 12 ))
, match5(3,"setfldZbuiltinZTzseqZintZptr"_1, 5, 
  CAST(1, ibcsub1, typ.ptr.i64, CASTINTTOPTR) 
+ BINOP(2, ibcsub2, C64.0, 0)
+ GEP(3, 1, typ.i64, -1, -2)
+ GEP(4, 1, typ.i64, -3, C64.0)
+ STORE(5, -4, ibcsub3, align8, 0)
+  BINOP(5, ibcsub2, C64.1, 0)
)
, match5(3,"setfldZbuiltinZTzseqZintZint"_1, 5, 
  CAST(1, ibcsub1, typ.ptr.i64, CASTINTTOPTR) 
+ BINOP(2, ibcsub2, C64.0, 0)
+ GEP(3, 1, typ.i64, -1, -2)
+ GEP(4, 1, typ.i64, -3, C64.0)
+ STORE(5, -4, ibcsub3, align8, 0)
+  BINOP(5, ibcsub2, C64.1, 0)
)
, match5(3,"setfldZbuiltinZTzseqZintZreal"_1, 5, 
  CAST(1, ibcsub1, typ.ptr.i64, CASTINTTOPTR) 
+ BINOP(2, ibcsub2, C64.0, 0)
+ GEP(3, 1, typ.i64, -1, -2)
+ GEP(4, 1, typ.i64, -3, C64.0)
+ STORE(5, -4, ibcsub3, align8, 0)
+  BINOP(5, ibcsub2, C64.1, 0)
)
, match5(2,"STKRECORDZbuiltinZintZint"_1, 3, ALLOCA(1, typ.ptr.i64, typ.i64, C64.2, 0) + STORE(2, -1, ibcsub1, align8, 0)
+ GEP(2, 1, typ.i64, -1, C64.1)
+ STORE(3, -2, ibcsub2, align8, 0)
+ CAST(3, -1, typ.i64, CASTPTRTOINT))
, // match5(3,"allocateseqQ3AseqQ2ETZbuiltinZintZintZint"_1,5, 
 BINOP(1, ibcsub1, C64.2, 0, typ.i64)
+CALL(2, 0, 32768, typ.function.[ i64, i64, i64], symboltableentry("allocatespaceQ3AseqQ2ETZbuiltinZint",function.[ i64, i64, i64]), ibcfirstpara2, -1)
 + CAST(3, -2, typ.ptr.i64, CASTINTTOPTR)
 + STORE(4, -3, ibcsub2, align8, 0)
+ GEP(4, 1, typ.i64, -3, C64.1)
+ STORE(5, -4, ibcsub3, align8, 0)
+CAST(5, -3, typ.i64, CASTPTRTOINT)
  ) //
  match5(3,"allocateseqQ3AseqQ2ETZbuiltinZintZintZint"_1,5, 
BINOP(1, ibcsub1, C64.2, 0)
+CALL(2, 0, 32768, typ.function.[ ptr.i64, i64, i64], symboltableentry("allocatespaceQ3AseqQ2ETZbuiltinZint",function.[ ptr.i64, i64, i64]), ibcfirstpara2, -1)
 + GEP(3, 1, typ.i64, -2, C64.0)
 + STORE(4, -3, ibcsub2, align8, 0)
+ GEP(4, 1, typ.i64, -2, C64.1)
+ STORE(5, -4, ibcsub3, align8, 0)
+CAST(5, -2, typ.i64, CASTPTRTOINT)
  )
 ]
let discard = @(+, addit, 0, t)
 t




function addit(m:match5)int valueofencoding.encode(m) 


   
function match5(nopara:int,inst:word, length:int, b:internalbc)match5
  match5([ inst, toword.nopara], length, getparts.b,"TEMPLATE"_1, nopara)

Function funcdec(alltypes:seq.myinternaltype,i:symbol) int
   modulerecord([mangledname.i],[ MODULECODEFUNCTION, typ.tollvmtype(alltypes,i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

   
 
Function match5map( theprg:program, uses:set.symbol,alltypes:seq.myinternaltype) seq.match5
  let discard3 = table
  buildtemplates(toseq.uses,1,theprg,empty:seq.symbol,alltypes)
  
  function symboltableentry(name:word) int
    symboltableentry(name,i64)
    
Function symboltableentry(name:word,type:llvmtype) int
 symboltableentry([name],type)

Function symboltableentry(name:seq.word,type:llvmtype) int 
  modulerecord( name , [ MODULECODEFUNCTION, typ.type, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] )
        
Function global(name:seq.word,type:llvmtype,init:int) int
modulerecord( name ,[ MODULECODEGLOBALVAR, typ.type, 2, 1+init, 0, align8 + 1, 0])


 
 use set.symbol
 
 use symbol
 
  use set.int
 
 
 use seq.int
 
 
 
 function   processconstargs( arglist:seq.symbol,i:int,args:seq.int) seq.int
    if i > length.arglist then   args
    else 
    let xx= arglist_i
    let e=    findencode(match5(fsig.xx+module.xx, 0, empty:seq.templatepart,"NOTFOUND"_1, 0))
      if isempty.e then empty:seq.int
      else
         processconstargs( arglist,i+1,args+arg.e_1)
   
 function processconst(  toprocess:seq.symbol,i:int, notprocessed:seq.symbol) seq.match5
   if i > length.toprocess then
    if isempty.notprocessed then empty:seq.match5
    else processconst( notprocessed,1,empty:seq.symbol)
 else let xx=toprocess_i
     let args=processconstargs(constantcode.xx,1,empty:seq.int)
     if isempty.args then processconst(toprocess,i+1,notprocessed+toprocess_i)
     else 
      let discard= addit.match5(fsig.xx+module.xx, 0, empty:seq.templatepart,"ACTARG"_1, addobject.args)
      processconst(toprocess,i+1,notprocessed)
     
 function  buildtemplates( used:seq.symbol,i:int,theprg:program,const:seq.symbol,alltypes:seq.myinternaltype) seq.match5 
   if i > length.used then 
     processconst(const,1,empty:seq.symbol) 
   else
    let xx= used_i
    let pkg=module.xx
     if pkg="$constant" then
       buildtemplates(used,i+1,theprg,const+used_i,alltypes)
     else 
     let b =  if     pkg ="builtin"  then
         findencode( match5([mangledname.xx,toword.nopara.xx], 0, empty:seq.templatepart,"NOTFOUND"_1, 0))
       else empty:seq.match5
    if length.b > 0 then 
       buildtemplates( used,i+1,theprg,const,alltypes)
    else 
     let m =  if isFref.xx then
              let mn=  mangledname((constantcode.xx)_1)
                           let functyp=ptr.tollvmtype(alltypes,(constantcode.xx)_1)   
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, C(i64, 
       [ CONSTCECAST, 9,  typ.functyp, symboltableentry( mn,functyp) ])) 
      else if islit.xx then
           if check then
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, if pkg="$real" then 
       C(double,[CONSTCECAST, 11,typ.i64,C64.toint.(fsig.xx)_1])
        else C64.toint.(fsig.xx)_1)
       else 
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, C64.toint.(fsig.xx)_1)
      else if islocal.xx then
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"LOCAL"_1, toint.(fsig.xx)_1)
      else if isdefine.xx then
        match5(fsig.xx+pkg, 0, empty:seq.templatepart,(fsig.xx)_1, toint.(fsig.xx)_2)
      else if isspecial.xx then
        match5(fsig.xx+pkg, 0, empty:seq.templatepart,(fsig.xx)_1, nopara.xx )
      else  if pkg="$words"then
         // let ctype=array(length.fsig.xx+2,i64)
          let c=   C(ctype,@(+,wordref,[CONSTDATA,0,length.fsig.xx],fsig.xx))
           let d= modulerecord([ MODULECODEGLOBALVAR, typ.ctype, 2, c + 1, 3, align8 + 1, 0])  
            let f=C(i64,[ CONSTCECAST, 9, typ.ptr.ctype,d])   //
            match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1,      addwordseq2.fsig.xx     )
      else if pkg="$word"then
         match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, wordref.(fsig.xx)_1)
      else if fsig.xx in ["callidxI( T seq , int) ","callidxR( T seq , int)","callidxP( T seq , int)"] then
           match5([mangledname.xx,"2"_1], 0, empty:seq.templatepart,"CALLIDX"_1, 0)
    else   if (fsig.xx)_1="global"_1 &and  pkg = "builtin" then
        match5(0,mangledname.xx, 2, GEP(1, 1, typ.i64, global([mangledname.xx],i64,C64.0))+CAST(2, -1, typ.i64, CASTPTRTOINT))
     else 
        let noargs = nopara.xx
        let name=mangledname.xx
        let functype= tollvmtype(alltypes,xx)
        let newcode = CALLSTART(1, 0, 32768, typ.functype, symboltableentry(name ,functype), noargs + 1)
         let code=code.lookupcode(theprg, used_i)
        match5([name,toword.noargs], 1, getparts.newcode,"CALL"_1, noargs,code,functype)
       let discard4=addit.m
    buildtemplates( used,i+1,theprg,const,alltypes)





Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
 let args = if  action.t = "CALL"_1 then empty:seq.int
 else 
 subseq(argstack, length.argstack - arg.t + 1, length.argstack)
  processtemplate(parts.t, deltaoffset, args)

Function CASTZEXT int 1

Function CASTTRUNC int 0

Function CASTPTRTOINT int 9

Function CASTINTTOPTR int 10

  
