#!/usr/local/bin/tau

run mylib testnew 

Module codetemplates

use bitpackedseq.bit

use seq.bit

use bits

use fileio


use seq.seq.int

use internalbc

use persistant

use llvm

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


function wordstype llvmtype array(-1, i64)

Function conststype llvmtype array(-2, i64)

Function profiletype llvmtype array(-3, i64)

Function type:match5 internaltype export

Function length(match5)int // no of instruction that return results // export

Function action(match5)word export

Function arg(match5)int export


type match5 is record fullinst:seq.word, length:int, parts:seq.templatepart, action:word, arg:int,code:seq.symbol

function match5 ( fullinst:seq.word, length:int, parts:seq.templatepart, action:word, arg:int) match5
 match5(fullinst,length,parts,action,arg,empty:seq.symbol)

Function code(match5) seq.symbol export

Function type:symbol internaltype export

 
Function type:program internaltype export

use symbol

Function _(m:seq.match5,d:symbol) match5  
let full=if module.d in ["$fref" ,  "int $" , "local", "$" ,"$constant" , "$words" ,"$word"] then
    fsig.d+module.d else [mangledname.d,toword.nopara.d]
 let e=  findencode(ematch5, match5(full, 0, empty:seq.templatepart,"NOTFOUND"_1, 0))
 assert not.isempty.e report "LL"+fsig.d+module.d
e_1

Function mangledname(m:match5)word    (fullinst.m)_1
 
function =(a:match5, b:match5)boolean fullinst.a = fullinst.b

function hash(a:match5)int hash.fullinst.a

function assignencoding(l:int, a:match5) int l+1

Function options(match5map:seq.match5,m:match5) seq.word
options.code.m

if  last.code.m=optiona.code.m then 
fullinst.match5map_((code.m)_(length.code.m-1)) else empty:seq.word


type ematch5 is encoding match5

function table seq.match5
let t = [ 
 match5("IDXUCZbuiltinZintZint 2", 3, CAST(1, ibcsub1, typ.ptr.i64, 10) + GEP(2, 1, typ.i64, -1, ibcsub2)
+ LOAD(3, -2, typ.i64, align8, 0))
, match5(// ? //"Q3FZbuiltinZintZint 2", 5, CMP2(1, ibcsub1, ibcsub2, 39) + CAST(2, -1, typ.i64, CASTZEXT) + CMP2(3, ibcsub1, ibcsub2, 38)
+ CAST(4, -3, typ.i64, CASTZEXT)
+ BINOP(5, -2, -4, 0, typ.i64))
, match5("castZbuiltinZTzseqZintZint 3", 3, 
    BINOP(1, ibcsub2, C64.3, // shift left // 7, typ.i64) 
    +BINOP(2, ibcsub3, -1, 0, typ.i64)
    + BINOP(3, ibcsub1, -1, 0, typ.i64))
, match5("Q3EZbuiltinZintZint 2", 2, CMP2(1, ibcsub1, ibcsub2, 38) + CAST(2, -1, typ.i64, CASTZEXT))
, match5("notZbuiltinZboolean 1", 1, BINOP(1, ibcsub1, C64.1, 12, typ.i64))
, // include aborted here so does not show up in profile results match5("abortedZbuiltinZTzprocess"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64, i64], C."abortedZbuiltinZTzprocess", -1, ibcsub1)), Including this as a template causes subtle compile errors //
match5(// = // "Q3DZbuiltinZintZint 2", 2, CMP2(1, ibcsub1, ibcsub2, 32) + CAST(2, -1, typ.i64, CASTZEXT))
, match5("EQL"_1, 2,               CMP2(1, ibcsub1, ibcsub2, 32) + CAST(2, -1, typ.i64, CASTZEXT))
, match5("Q2DZbuiltinZintZint 2", 1, BINOP(1, ibcsub1, ibcsub2, 1, typ.i64))
, match5(// + // "Q2BZbuiltinZintZint 2", 1, BINOP(1, ibcsub1, ibcsub2, 0, typ.i64))
, match5(// * // "Q2AZbuiltinZintZint 2", 1, BINOP(1, ibcsub1, ibcsub2, 2, typ.i64))
, match5(// / op //"Q2FZbuiltinZintZint 2", 1, BINOP(1, ibcsub1, ibcsub2, 4, typ.i64))
, match5("Q2DZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + BINOP(3, -1, -2, 1)
+ CAST(4, -3, typ.i64, 11))
, match5(// + //"Q2BZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + BINOP(3, -1, -2, 0)
+ CAST(4, -3, typ.i64, 11))
, match5(// * //"Q2AZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + BINOP(3, -1, -2, 2)
+ CAST(4, -3, typ.i64, 11))
, match5(// / op //"Q2FZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + BINOP(3, -1, -2, 4)
+ CAST(4, -3, typ.i64, 11))
, match5(// ? //"Q3FZbuiltinZrealZreal"_1, 7, CAST(1, ibcsub1, typ.double, 11) + CAST(2, ibcsub2, typ.double, 11) + CMP2(3, -1, -2, 3)
+ CAST(4, -3, typ.i64, CASTZEXT)
+ CMP2(5, -1, -2, 2)
+ CAST(6, -5, typ.i64, CASTZEXT)
+ BINOP(7, -4, -6, 0, typ.i64))
, match5("intpartZbuiltinZreal"_1, 2, CAST(1, ibcsub1, typ.double, 11) + CAST(2, -1, typ.i64, // fptosi double // 4))
, match5("torealZbuiltinZint"_1, 2, // sitofp // CAST(1, ibcsub1, typ.double, 6) + CAST(2, -1, typ.i64, 11))
, match5("sqrtZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)
+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.sqrt.f64", -1)
+ CAST(3, -2, typ.i64, 11))
, match5("sinZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)
+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.sin.f64", -1)
+ CAST(3, -2, typ.i64, 11))
, match5("cosZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)
+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.cos.f64", -1)
+ CAST(3, -2, typ.i64, 11))
, match5("Q3CQ3CZbuiltinZbitsZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, // SHL // 7, typ.i64))
, match5("Q3EQ3EZbuiltinZbitsZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, // LSHR // 8, typ.i64))
, match5("Q02227ZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // AND // 10, typ.i64))
, match5("Q02228ZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // OR // 11, typ.i64))
, match5("xorZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // XOR // 12, typ.i64))
, match5("setfld2ZbuiltinZTzseqZintZT 3", 4, CAST(1, ibcsub1, typ.ptr.i64, 10) + GEP(2, 1, typ.i64, -1, ibcsub2)
+ GEP(3, 1, typ.i64, -2, C64.0)
+ STORE(4, -3, ibcsub3, align8, 0)
+ CAST(4, -1, typ.i64, 9))
, match5("STKRECORDZbuiltinZintZint"_1, 3, ALLOCA(1, typ.ptr.i64, typ.i64, C64.2, 0) + STORE(2, -1, ibcsub1, align8, 0)
+ GEP(2, 1, typ.i64, -1, C64.1)
+ STORE(3, -2, ibcsub2, align8, 0)
+ CAST(3, -1, typ.i64, CASTPTRTOINT))
,match5("callidxZbuiltinZintZTzseqZint"_1, 2, CAST(1, ibcsub1, typ.ptr.function.[ i64, i64, i64, i64], CASTINTTOPTR)
+ CALL(2, 0, 32768, typ.function.[ i64, i64, i64, i64], -1, ibcfirstpara2, ibcsub2, ibcsub3))
 ]
let discard = @(+, addit, 0, t)
 t



function addit(m:match5)int valueofencoding.encode(ematch5,m) 


function match5(inst:word, length:int, b:internalbc)match5
 let parts = getparts.b
 let nopara = @(max, parano, 0, parts)
  match5([ inst, toword.nopara], length, parts,"TEMPLATE"_1, nopara)

function match5(fullinst:seq.word, length:int, b:internalbc)match5
 let parts = getparts.b
 let nopara = @(max, parano, 0, parts)
  match5(fullinst, length, parts,"TEMPLATE"_1, nopara)
  
 
Function match5map( theprg:program, defines:seq.symbol, uses:set.symbol,symlist:seq.word) seq.match5
  let declist=@(+, mangledname,"", defines)
   let discard = conststype
  let discard1 = profiletype
  let discard2 = @(+, C, 0, symlist+ declist)
  let discard3 = table
  buildtemplates(toseq.uses,1,theprg,empty:seq.symbol)
  
  
 use set.symbol
 
 use symbol
 
  use set.int
 
 
 use seq.int
 
 
 
 function   processconstargs( arglist:seq.symbol,i:int,args:seq.int) seq.int
    if i > length.arglist then   args
    else 
    let xx= arglist_i
    let e=    findencode(ematch5, match5(fsig.xx+module.xx, 0, empty:seq.templatepart,"NOTFOUND"_1, 0))
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
     
 function  buildtemplates( used:seq.symbol,i:int,theprg:program,const:seq.symbol) seq.match5 
   if i > length.used then 
     processconst(const,1,empty:seq.symbol) 
   else
    let xx= used_i
    let pkg=module.xx
     if pkg="$constant" then
       buildtemplates(used,i+1,theprg,const+used_i)
     else 
     let b =  if     pkg ="builtin"  then
         findencode(ematch5, match5([mangledname.xx,toword.nopara.xx], 0, empty:seq.templatepart,"NOTFOUND"_1, 0))
       else empty:seq.match5
    if length.b > 0 then 
       buildtemplates( used,i+1,theprg,const)
    else 
     let m =  if pkg = "$fref" then
              let mn=  mangledname((constantcode.xx)_1)
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, C(i64, [ CONSTCECAST, 9, typ.ptr.getftype.mn, C.mn]))
      else if pkg = "int $" then
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, C64.toint.(fsig.xx)_1)
      else if pkg="local" then
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,"LOCAL"_1, toint.(fsig.xx)_1)
      else if pkg="$" then
       match5(fsig.xx+pkg, 0, empty:seq.templatepart,(fsig.xx)_1, toint.(fsig.xx)_2)
      else  if pkg="$words"then
        match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, addwordseq2.fsig.xx)
      else if pkg="$word"then
         match5(fsig.xx+pkg, 0, empty:seq.templatepart,"ACTARG"_1, wordref.(fsig.xx)_1)
      else
        let noargs = nopara.xx
        let name=mangledname.xx
        let newcode = CALLSTART(1, 0, 32768, typ.function.constantseq(noargs + 2, i64), C.[ name], noargs + 1)
         let code=code.lookupcode(theprg, used_i)
        match5([name,toword.noargs], 1, getparts.newcode,"CALL"_1, noargs,code)
       let discard4=addit.m
    buildtemplates( used,i+1,theprg,const)




function ematch5 erecord.match5 export

Function usetemplate(t:match5, deltaoffset:int, argstack:seq.int)internalbc
 let args = if  action.t = "CALL"_1 then empty:seq.int
 else 
 subseq(argstack, length.argstack - arg.t + 1, length.argstack)
  processtemplate(parts.t, deltaoffset, args)

Function CASTZEXT int 1

Function CASTTRUNC int 0

Function CASTPTRTOINT int 9

Function CASTINTTOPTR int 10

type pp is record idx:int, val:int

function getvbr(a:seq.bit, idx:int, size:int)pp getvbr(a, size, bits.0, 0, idx, 0)

function getvbr(a:seq.bit, size:int, val:bits, nobits:int, idx:int, i:int)pp
 let b = toint.a_(idx + i)
  if i = size - 1 then
  if b = 0 then pp(idx + size, toint.val)else getvbr(a, size, val, nobits, idx + size, 0)
  else getvbr(a, size, bits.b << nobits ∨ val, nobits + 1, idx, i + 1)

function getinfo(b:seq.bit, noargs:int, r:seq.int, idx:int, recs:seq.seq.int, abbrvlen:int)seq.seq.int
 if length.r > 0 then
 // working on record //
  if noargs = 0 then getinfo(b, 0, empty:seq.int, idx, recs + r, abbrvlen)
  else
   let next = getvbr(b, idx, 6)
    getinfo(b, noargs - 1, r + val.next, idx.next, recs, abbrvlen)
 else
  let t = getvbr(b, abbrvlen, bits.0, 0, idx, 0)
   if val.t = 3 then
   // record //
    let inst = getvbr(b, idx.t, 6)
    let args = getvbr(b, idx.inst, 6)
     getinfo(b, val.args, [ val.inst], idx.args, recs, abbrvlen)
   else recs

function astext2(a:seq.int)seq.word"[" + @(+, toword,"", a) + "]"

Function astext(a:bitpackedseq.bit)seq.word
 // @(+, toword,"", @(+, toint, empty:seq.int, toseq.a))+"
&br"+ //
 let recs = getinfo(toseq.a, 0, empty:seq.int, 1, empty:seq.seq.int, 4)
  @(seperator." &br", astext2,"", recs)
  
