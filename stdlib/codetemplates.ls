
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

use seq.templatepart

use textio


use seq.symbol

use seq.seq.symbol

use seq.mytype

use mangle


Function constdata seq.slot export

Function wordref(w:word) int  export 

Function addliblib( libname:seq.word,mods:int,profiledata:int) int export


Function mangledname(s:symbol)word mangle(fsig.s,module.s)


Function tollvmtype(alltypes:seq.myinternaltype,s:symbol) llvmtype
   if fsig.s="option(T, word seq)" then    function.constantseq(nopara.s + 2, i64) else 
 // assert not( modname.s=mytype."builtin") report "llvmtype error "+print.s //
  function.@(+,tollvmtype.alltypes, [tollvmtype(alltypes,resulttype.s),i64],paratypes.s)
  
function tollvmtype(alltypes:seq.myinternaltype,s:mytype) llvmtype
        let kind=parakind(alltypes,s)
          if  kind="int"_1 then i64
          else if kind="real"_1 then   double   
        else  ptr.i64  


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
 
 function match5 ( fullinst:seq.word, length:int, parts:seq.templatepart, action:word, arg:slot) match5
 match5(fullinst,length,parts,action,toint.arg,empty:seq.symbol,i64)


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


function table seq.match5
let t=[match5(1, "bitcastZbuiltinZintzseqzseq"_1, 0, emptyinternalbc)
,match5(1, "isnullZbuiltinZptr"_1, 3, 
  CAST(r.1, slot.ibcsub1,   i64, ptrtoint)   +CMP2(r.2, r.1, C64.0, 32) + CAST(r.3,r.2,  i64, zext))
, match5(0,"nullptrZbuiltin"_1, 1,   CAST(r.1, C64.0,  ptr.i64, inttoptr))
, match5(2,"IDXZbuiltinZintzseqZint"_1, 2, GEP(r.1,  i64, slot.ibcsub1, slot.ibcsub2)+ LOAD(r.2, r.1,  i64 ))
, match5(2,"IDXZbuiltinZintzseqzseqZint"_1,  3, GEP(r.1,  i64, slot.ibcsub1, slot.ibcsub2)+ LOAD(r.2, r.1,  i64 )
 +CAST(r.3, r.2,  ptr.i64, inttoptr))
 , match5(2,"IDXZbuiltinZptrzseqZint"_1, 3, GEP(r.1,  i64, slot.ibcsub1, slot.ibcsub2)+ LOAD(r.2, r.1,  i64 )
 +CAST(r.3, r.2,  ptr.i64, inttoptr))
, match5(2,"IDXZbuiltinZrealzseqZint"_1, 3,  GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2)
  + LOAD(r.2, r.1,  i64 )+CAST(r.3, r.2,  double, bitcast))
, match5(1,"getseqtypeZbuiltinZTzseq"_1, 1,  LOAD(r.1, slot.ibcsub1,  i64 ))
, match5(2,"STKRECORDZbuiltinZptrZptr"_1,3, ALLOCA(r.1,  ptr.ptr.i64,  i64, C64.2, 0) 
+ STORE(r.2, r.1, slot.ibcsub1)
+ GEP(r.2,  ptr.i64, r.1, C64.1)
+ STORE(r.3, r.2, slot.ibcsub2)
+ GEP(r.3,  ptr.i64, r.1, C64.0))
,match5(1,"sqrtZbuiltinZreal"_1, 1, CALL(r.1, 0, 32768,  function.[ double, double], symboltableentry(merge."llvm.sqrt.f64",function.[ double, double]),slot.ibcsub1))
  ,  match5(1,"sinZbuiltinZreal"_1, 1, CALL(r.1, 0, 32768,  function.[ double, double], symboltableentry(merge."llvm.sin.f64",function.[ double, double]),slot.ibcsub1))
  ,  match5(1,"cosZbuiltinZreal"_1, 1, CALL(r.1, 0, 32768,  function.[ double, double], symboltableentry(merge."llvm.cos.f64",function.[ double, double]),slot.ibcsub1))
  ,  match5(1,"tanZbuiltinZreal"_1, 1, CALL(r.1, 0, 32768,  function.[ double, double], symboltableentry("tan",function.[ double, double]),slot.ibcsub1))
  ,  match5(1,"arcsinZbuiltinZreal"_1, 1, CALL(r.1, 0, 32768,  function.[ double, double], symboltableentry("asin",function.[ double, double]),slot.ibcsub1))
  ,  match5(1,"arccosZbuiltinZreal"_1, 1, CALL(r.1, 0, 32768,  function.[ double, double], symboltableentry("acos",function.[ double, double]),slot.ibcsub1))
,match5(1,"intpartZbuiltinZreal"_1, 1,   CAST(r.1, slot.ibcsub1,  i64,   fptosi   ))
,match5(1,"torealZbuiltinZint"_1, 1, CAST(r.1, slot.ibcsub1,  double, sitofp) )
,  match5(2,"Q2DZbuiltinZrealZreal"_1, 1,   BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sub))
,  match5(2,// + //"Q2BZbuiltinZrealZreal"_1, 1,   BINOP(r.1, slot.ibcsub1, slot.ibcsub2, add))
,  match5(2,// * //"Q2AZbuiltinZrealZreal"_1, 1,   BINOP(r.1, slot.ibcsub1, slot.ibcsub2, mul))
,  match5(2,// / op //"Q2FZbuiltinZrealZreal"_1, 1,   BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sdiv))
 , match5(1,"casttorealZbuiltinZint"_1, 1, CAST(r.1, slot.ibcsub1, double, bitcast))
 ,match5(1,"representationZbuiltinZreal"_1, 1, CAST(r.1, slot.ibcsub1, i64, bitcast)) 
 , match5(2,// ? //"Q3FZbuiltinZrealZreal"_1, 5,     CMP2(r.1,slot.ibcsub1, slot.ibcsub2, 3)
 + CAST(r.2, r.1, i64, zext)
+ CMP2(r.3 ,slot.ibcsub1, slot.ibcsub2, 2)
+ CAST(r.4, r.3,  i64, zext)
+ BINOP(r.5, r.2, r.4, add ))
 , match5(2,// ? //"Q3FZbuiltinZintZint"_1, 5, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 39) + CAST(r.2, r.1, i64, zext) + CMP2(r.3, slot.ibcsub1, slot.ibcsub2, 38)
+ CAST(r.4, r.3, i64, zext)
+ BINOP(r.5, r.2, r.4, add))
, match5(3,"castZbuiltinZTzseqZintZint"_1, 1,  GEP(r.1, i64, slot.ibcsub1, slot.ibcsub2))
, match5(2,"Q3EZbuiltinZintZint "_1, 2, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 38) + CAST(r.2, r.1,  i64, zext))
, match5(1,"notZbuiltinZboolean"_1, 1, BINOP(r.1, slot.ibcsub1, C64.1, xor))
, // include aborted here so does not show up in profile results match5("abortedZbuiltinZTzprocess"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64, i64], C."abortedZbuiltinZTzprocess", -1, ibcsub1)), Including this as a template causes subtle compile errors //
match5(2,// = // "Q3DZbuiltinZintZint"_1, 2, CMP2(r.1, slot.ibcsub1, slot.ibcsub2, 32) + CAST(r.2,r.1,  i64, zext))
, match5(2, "Q2DZbuiltinZintZint"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sub ))
, match5(2,// + // "Q2BZbuiltinZintZint"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, add ))
, match5(2,// * // "Q2AZbuiltinZintZint"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2,mul ))
, match5(2,// / op //"Q2FZbuiltinZintZint"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, sdiv ))
, match5(2,"Q3CQ3CZbuiltinZbitsZint"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, shl ))
, match5(2,"Q3EQ3EZbuiltinZbitsZint"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2,  lshr  ))
, match5(2,"Q02227ZbuiltinZbitsZbits"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, and  ))
, match5(2,"Q02228ZbuiltinZbitsZbits"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, or   ))
, match5(2,"xorZbuiltinZbitsZbits"_1, 1, BINOP(r.1, slot.ibcsub1, slot.ibcsub2, xor ))
, match5(3,"setfldZbuiltinZintzseqZintZint"_1, 2, 
  GEP(r.1,  i64, slot.ibcsub1, slot.ibcsub2)
+ STORE(r.2, r.1, slot.ibcsub3)
+  BINOP(r.2, slot.ibcsub2, C64.1, add)
)
 ]
let discard = @(+, addit, 0, t)
 t




function addit(m:match5)int valueofencoding.encode(m) 


   
function match5(nopara:int,inst:word, length:int, b:internalbc)match5
  match5([ inst, toword.nopara], length, getparts.b,"TEMPLATE"_1, nopara)

Function funcdec(alltypes:seq.myinternaltype,i:symbol) int
   toint.modulerecord([mangledname.i],[ toint.FUNCTIONDEC, typ.tollvmtype(alltypes,i), 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])
 
Function match5map( theprg:program, uses:set.symbol,alltypes:seq.myinternaltype) seq.match5
  let discard3 = table
  buildtemplates(toseq.uses,1,theprg,empty:seq.symbol,alltypes)
  
  function symboltableentry(name:word) slot
    symboltableentry(name,i64)
    
Function symboltableentry(name:word,type:llvmtype) slot
 symboltableentry([name],type)

Function symboltableentry(name:seq.word,type:llvmtype) slot 
   modulerecord( name , [ toint.FUNCTIONDEC, typ.type, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] )
        
Function global(name:seq.word,type:llvmtype,init:slot) int
toint.modulerecord( name ,[ toint.GLOBALVAR, typ.type, 2, 1+toint.init, 0, toint.align8 + 1, 0])


 
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
     let b =  if     isbuiltin.pkg   then
         findencode( match5([mangledname.xx,toword.nopara.xx], 0, empty:seq.templatepart,"NOTFOUND"_1, 0))
       else empty:seq.match5
    if length.b > 0 then 
       buildtemplates( used,i+1,theprg,const,alltypes)
    else 
     let m =  if isFref.xx then
              let mn=  mangledname((constantcode.xx)_1)
                           let functyp=ptr.tollvmtype(alltypes,(constantcode.xx)_1)   
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, ptrtoint(functyp, symboltableentry( mn,functyp) )) 
      else if islit.xx then
        match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, if pkg="$real" then  Creal.toint.(fsig.xx)_1  else C64.toint.(fsig.xx)_1)
       else if islocal.xx then
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"LOCAL"_1, toint.(fsig.xx)_1)
      else if isdefine.xx then
        match5(fsig.xx+pkg, 0, empty:seq.templatepart,(fsig.xx)_1, toint.(fsig.xx)_2)
      else if isblock.xx then
         let typ=tollvmtype(alltypes,resulttype.xx) 
              match5(fsig.xx+pkg, 0, empty:seq.templatepart,(fsig.xx)_1,  nopara.xx,empty:seq.symbol,typ)
        else if isspecial.xx then
        match5(fsig.xx+pkg, 0, empty:seq.templatepart,(fsig.xx)_1, nopara.xx )
      else  if pkg="$words"then
         //  let ctype=array(length.fsig.xx+2,i64)
          let c=   DATA(ctype,@(+,wordref,[0,length.fsig.xx],fsig.xx))
           let d= modulerecord("",[ toint.GLOBALVAR, typ.ctype, 2, c + 1, 3, toint.align8 + 1, 0])  
            let f=ptrtoint(ptr.ctype,d)    //
            match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1,      addwordseq2.fsig.xx       )
      else if pkg="$word"then
         match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, wordref.(fsig.xx)_1)
      else if (fsig.xx)_1="callidx"_1 &and isbuiltin.pkg  then 
         match5([mangledname.xx,"2"_1], 0, empty:seq.templatepart,"CALLIDX"_1, 0,empty:seq.symbol,tollvmtype(alltypes,resulttype.xx))    
       else   if (fsig.xx)_1="global"_1 &and isbuiltin.pkg  then
        match5(0,mangledname.xx, 1, GEP(r.1,   i64, slot.global([mangledname.xx],i64,C64.0))
        )
        else if (fsig.xx)_1="blockindexfunc"_1 &and isbuiltin.pkg  then
         let functype=ptr.function.[ i64, i64, ptr.i64, i64]
         match5([mangledname.xx,"0"_1], 0, empty:seq.templatepart,"ACTARG"_1, 
         ptrtoint(functype,symboltableentry("indexblocksZassignencodingnumberZintzseqzseqZint"_1, functype)))
        else
        let noargs = nopara.xx
        let name=mangledname.xx
        let functype= tollvmtype(alltypes,xx)
        let newcode = CALLSTART(1, 0, 32768, typ.functype, toint.symboltableentry(name ,functype), noargs + 1)
         let code=code.lookupcode(theprg, used_i)
        match5([name,toword.noargs], 1, getparts.newcode,"CALL"_1, noargs,code,functype)
       let discard4=addit.m
    buildtemplates( used,i+1,theprg,const,alltypes)




Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
 let args = if  action.t = "CALL"_1 then empty:seq.int
 else 
 subseq(argstack, length.argstack - arg.t + 1, length.argstack)
  processtemplate(parts.t, deltaoffset, args)




  
