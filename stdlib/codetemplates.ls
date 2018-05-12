Module codetemplates

use internalbc

use llvm

use oseq.match5

use process.seq.match5

use seq.match5

use seq.seq.int

use stdlib

function wordstype encoding.llvmtype array(-1, i64)

Function conststype encoding.llvmtype array(-2, i64)


Function length(match5)int export

/Function template(match5)internalbc export

function ?(a:match5, b:match5)ordering encoding.inst.a ? encoding.inst.b

function =(a:match5, b:match5)boolean encoding.inst.a = encoding.inst.b

Function table seq.match5 result.process.subtable




function subtable seq.match5 
 sort.[ match5("IDXUC"_1, 3, CAST(1, ibcsub1, typ.ptr.i64, 10)+ GEP(2, 1, typ.i64, -1, ibcsub2)+ LOAD(3, -2, typ.i64, align8, 0)), 
 match5(// ? //"Q3FZbuiltinZintZint"_1, 5, CMP2(1, ibcsub1, ibcsub2, 39)+ CAST(2, -1, typ.i64, CASTZEXT)+ CMP2(3, ibcsub1, ibcsub2, 38)+ CAST(4, -3, typ.i64, CASTZEXT)+ BINOP(5, -2, -4, 0, typ.i64)), 
  match5("getaddressZbuiltinZTzseqZint"_1, 2,  
  BINOP(1, ibcsub2, C64.3, // shift left // 7)+ BINOP(2, ibcsub1, -1, 0, typ.i64)), 
 match5("Q3EZbuiltinZintZint"_1, 2, CMP2(1, ibcsub1, ibcsub2, 38)+ CAST(2, -1, typ.i64, CASTZEXT)), 
 match5("notZbuiltinZboolean"_1, 1, BINOP(1, ibcsub1, C64.1, 12, typ.i64)), 
 match5("hashZbuiltinZint"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64], C."HASH", ibcsub1)), 
 // include aborted here so does not show up in profile results match5("abortedZbuiltinZTzprocess"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64, i64], C."abortedZbuiltinZTzprocess",-1, ibcsub1)), Including this as a template causes subtle compile errors // 
  match5("Q3DZbuiltinZintZint"_1, 2, CMP2(1, ibcsub1, ibcsub2, 32)+ CAST(2, -1, typ.i64, CASTZEXT)), 
 match5("EQL"_1, 2, CMP2(1, ibcsub1, ibcsub2, 32)+ CAST(2, -1, typ.i64, CASTZEXT)), 
 match5("Q2DZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 1, typ.i64)), 
 match5("Q2BZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 0, typ.i64)), 
  match5("Q2AZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 2, typ.i64)), 
 match5("Q2FZbuiltinZintZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, 4, typ.i64)), 
 match5("Q2DZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ BINOP(3, -1, -2, 1)+ CAST(4, -3, typ.i64, 11)), 
 match5(// + //"Q2BZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ BINOP(3, -1, -2, 0)+ CAST(4, -3, typ.i64, 11)), 
 match5(// * //"Q2AZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ BINOP(3, -1, -2, 2)+ CAST(4, -3, typ.i64, 11)), 
 match5(// / //"Q2FZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ BINOP(3, -1, -2, 4)+ CAST(4, -3, typ.i64, 11)), 
 match5(// ? //"Q3FZbuiltinZrealZreal"_1, 7, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, ibcsub2, typ.double, 11)+ CMP2(3, -1, -2, 3)+ CAST(4, -3, typ.i64, CASTZEXT)+ CMP2(5, -1, -2, 2)+ CAST(6, -5, typ.i64, CASTZEXT)+ BINOP(7, -4, -6, 0, typ.i64)), 
 match5("intpartZbuiltinZreal"_1, 2, CAST(1, ibcsub1, typ.double, 11)+ CAST(2, -1, typ.i64, // fptosi double // 4)), 
 match5("int2realZbuiltinZint"_1, 2, // sitofp // CAST(1, ibcsub1, typ.double, 6)+ CAST(2, -1, typ.i64, 11)), 
 match5("sqrtZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.sqrt.f64", -1)+ CAST(3, -2, typ.i64, 11)), 
 match5("sinZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.sin.f64", -1)+ CAST(3, -2, typ.i64, 11)), 
 match5("cosZbuiltinZreal"_1, 3, CAST(1, ibcsub1, typ.double, 11)+ CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.cos.f64", -1)+ CAST(3, -2, typ.i64, 11)), 
 match5("Q3CQ3CZbuiltinZbitsZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, // SHL // 7, typ.i64)), 
 match5("Q3EQ3EZbuiltinZbitsZint"_1, 1, BINOP(1, ibcsub1, ibcsub2, // LSHR // 8, typ.i64)), 
 match5("Q02227ZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // AND // 10, typ.i64)), 
 match5("Q02228ZbuiltinZbitsZbits"_1, 1, BINOP(1, ibcsub1, ibcsub2, // OR // 11, typ.i64)),
 match5("setfldZbuiltinZTzaddressZT"_1,3, CAST( 1, ibcsub1, typ.ptr.i64, 10)+ 
 STORE(2, -1, ibcsub2,align8,0)+
 GEP(2,1,typ.i64,-1,C64.1)+
  CAST(3, -2, typ.i64, 9) )]
 

Function usetemplate(tab:seq.match5, inst:word,deltaoffset:int,inargs:seq.int) templateresult
   let noargs=length.inargs
   if noargs > 2 then templateresult( 0,emptyinternalbc)
  else 
    let a = match5(inst, 0, false,empty:seq.templatepart,empty:seq.int)
    let i = binarysearch(tab, a)
    if i < 0 then templateresult( 0,emptyinternalbc)
    else 
     let t = tab_i
       let args = if switchargs.t then [inargs_2,inargs_1] else 
       if length.parts.t > 3 then inargs+inargs      else inargs 
     let b = if noargs=0 then part0.t
    else  
      ggh(deltaoffset, args,parts.t,1,part0.t)
     templateresult(length.t,internalbc(0,0,[setsub, deltaoffset]+ b+[setsub, -deltaoffset]  ))
         
     
 type  templatepart is record        part:seq.int,loc:int
 
 use seq.templatepart
 
 type match5 is record inst:word, length:int, switchargs:boolean,parts:seq.templatepart,part0:seq.int

     
function match5 (  inst:word, length:int, b:internalbc) match5
let a = finish.b
   let i =findindex(sub11,a)
    let j=  findindex(sub22,a) 
     let  jj=max(i,j)
    let  ii=min(i,j)
     let rest=subseq(a,jj+2,length.a)
    let k = findindex(sub11,a,jj+1)
    let l= findindex(sub22,a,jj+1) 
    let parts = if ii < length.a then [ templatepart(subseq(a,ii+2,jj-1),a_(ii+1))]
     +   if jj < length.a then [ templatepart(subseq(a,jj+2,k-1),a_(jj+1))]
     +   if k < length.a then [ templatepart(subseq(a,k+2,l-1),a_(k+1))]
     +   if l < length.a then [ templatepart(subseq(a,l+2,length.a),a_(l+1))]
        else empty:seq.templatepart
        else empty:seq.templatepart
        else empty:seq.templatepart
      else empty:seq.templatepart
    let part0=subseq(a,1,ii-1)
          let swithargs= i > j 
  match5(inst,length,swithargs,parts,part0)
     

     
function ggh(deltaoffset:int,args:seq.int,parts:seq.templatepart,i:int,result:seq.int) seq.int
     if i > length.args then result
     else 
     let arg= args_i 
       let newpart =  
          if arg < 0 then [ vbr6 ,deltaoffset+loc(parts_i)+ arg ] else [reloc,arg-loc(parts_i)+1]
      ggh(deltaoffset,args,parts,i+1,result+newpart+  part.(parts_i))
     
     
     
          
use seq.int
     
type templateresult is record   length:int,code:internalbc


Function length(templateresult) int export

Function code(templateresult) internalbc export


Function CASTZEXT int 1

Function CASTTRUNC int 0

Function CASTPTRTOINT int 9

Function CASTINTTOPTR int 10

use bitpackedseq.bit


use seq.bit

use bits

type pp is record idx:int, val:int

function getvbr(a:seq.bit, idx:int, size:int)pp getvbr(a, size, bits.0, 0, idx, 0)

function getvbr(a:seq.bit, size:int, val:bits, nobits:int, idx:int, i:int)pp 
 let b = toint(a_(idx + i))
  if i = size - 1 
  then if b = 0 then pp(idx + size, toint.val)else getvbr(a, size, val, nobits, idx + size, 0)
  else getvbr(a, size, bits.b << nobits ∨ val, nobits + 1, idx, i + 1)
  
function getinfo(b:seq.bit, noargs:int, r:seq.int, idx:int, recs:seq.seq.int, abbrvlen:int) seq.seq.int 
 if length.r > 0 
  then // working on record // 
   if noargs = 0 
   then getinfo(b, 0, empty:seq.int, idx, recs + r, abbrvlen)
   else let next = getvbr(b, idx, 6)
   getinfo(b, noargs - 1, r + val.next, idx.next, recs, abbrvlen)
  else let t = getvbr(b, abbrvlen, bits.0, 0, idx, 0)
  if val.t = 3 
  then // record // 
   let inst = getvbr(b, idx.t, 6)
   let args = getvbr(b, idx.inst, 6)
   getinfo(b, val.args, [ val.inst], idx.args, recs, abbrvlen)
  else  recs 

function astext2(a:seq.int) seq.word "["+@(+,toword,"",a)+"]"

function astext(a:bitpackedseq.bit) seq.word
  // @(+,toword,"",@(+,toint,empty:seq.int,toseq.a))
+"&br"+ //
 let recs=getinfo( toseq.a, 0, empty:seq.int, 1, empty:seq.seq.int, 4)
@(seperator("&br"),astext2,"",recs)
