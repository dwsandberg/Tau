#!/usr/local/bin/tau

Module codetemplates2

use llvm

use oseq.match5

use process.seq.match5

use seq.match5

use seq.seq.int

use stdlib

use internalbc

function wordstype encoding.llvmtype array(-1, i64)

function  conststype encoding.llvmtype  array(-2, i64)

type match5 is record inst:word, length:int,template:internalbc

Function length(match5) int export

Function template(match5) internalbc export

function ?(a:match5, b:match5)ordering encoding.inst.a ? encoding.inst.b

function =(a:match5, b:match5)boolean encoding.inst.a = encoding.inst.b

Function table seq.match5 result.process.subtable

Function CONSTtemplate  internalbc
     GEP(1, 1, typ.conststype, C."list", C64.0,ibcsub1)
        + CAST(2,-1, typ.i64, 9) 
        
Function WORDtemplate internalbc LOAD(1, ibcsub1, typ.i64, align8, 0)

Function RECORDtemplate internalbc
  CALL(1, 0, 32768, typ.function.[ i64, i64, i64], C."allocatespaceZbuiltinZint", ibcsub2, ibcsub1)
   +CAST(2,-1, typ.ptr.i64, CASTINTTOPTR)
   

function subtable seq.match5 
 sort.[ match5("IDXUC"_1,3,  
   CAST(1, ibcsub1, typ.ptr.i64, 10)
   +GEP(2, 1, typ.i64, - 1, ibcsub2)
   +LOAD(3, - 2, typ.i64, align8, 0)) 
 ,match5(// ? //"Q3FZbuiltinZintZint"_1,5,  
  CMP2(1, ibcsub1, ibcsub2, 39)+
 CAST(2, - 1, typ.i64, CASTZEXT)+ 
 CMP2(3, ibcsub1, ibcsub2, 38)+ 
 CAST(4, - 3, typ.i64, CASTZEXT)+ 
 BINOP(5, - 2, - 4, 0, typ.i64)),
 match5("Q2BZbuiltinZTzaddressZint"_1, 2,// Q2BZbuiltinZTzaddressZint(a, b)((a)+((b)<<3))// 
  BINOP(1, ibcsub2, C64.3, // shift left // 7)
     +BINOP(2, ibcsub1, - 1, 0, typ.i64)), 
 match5("Q3EZbuiltinZintZint"_1, 2,
 CMP2(1, ibcsub1, ibcsub2, 38)
   +CAST(2,  - 1, typ.i64, CASTZEXT) ), 
 match5("notZbuiltinZboolean"_1,1,   BINOP(1, ibcsub1, C64.1, 12, typ.i64)), 
 match5("hashZbuiltinZint"_1, 1, CALL(1, 0, 32768, typ.function.[ i64, i64], C."HASH", ibcsub1)), 
 // include aborted here so does not show up in profile results   
 match5("abortedZbuiltinZTzprocess"_1,1, CALL(1, 0, 32768, typ.function.[ i64, i64,i64], C."abortedZbuiltinZTzprocess", -1,ibcsub1)), 
Including this as a template causes subtle compile errors
// match5("Q3DZbuiltinZintZint"_1,2,
  CMP2(1, ibcsub1, ibcsub2, 32) 
 + CAST(2, - 1, typ.i64, CASTZEXT)), 
 match5("EQL"_1, 2,CMP2(1, ibcsub1, ibcsub2, 32)+CAST(2, - 1, typ.i64, CASTZEXT)), 
 match5("Q2DZbuiltinZintZint"_1,1, BINOP(1, ibcsub1, ibcsub2, 1, typ.i64)), 
 match5("Q2BZbuiltinZintZint"_1,1, BINOP(1, ibcsub1, ibcsub2, 0, typ.i64)), 
 match5("ADD"_1, 1,BINOP(1, ibcsub1, ibcsub2, 0, typ.i64)), 
 match5("Q2AZbuiltinZintZint"_1, 1,BINOP(1, ibcsub1, ibcsub2, 2, typ.i64)), 
 match5("Q2FZbuiltinZintZint"_1, 1,BINOP(1, ibcsub1, ibcsub2, 4, typ.i64)), 
 match5("Q2DZbuiltinZrealZreal"_1, 4, CAST(1, ibcsub1, typ.double, 11) 
 +CAST(2, ibcsub2, typ.double, 11) 
 +BINOP(3, - 1,  - 2, 1) 
 +CAST(4, - 3, typ.i64, 11)),
 match5(// + //"Q2BZbuiltinZrealZreal"_1,4, CAST(1, ibcsub1, typ.double, 11) 
 +CAST(2, ibcsub2, typ.double, 11) 
 +BINOP(3,  - 1,  - 2, 0) 
 +CAST(4,  - 3, typ.i64, 11)), 
 match5(// * //"Q2AZbuiltinZrealZreal"_1,4, 
  CAST(1, ibcsub1, typ.double, 11) 
 +CAST(2, ibcsub2, typ.double, 11) 
 +BINOP(3, - 1, - 2, 2) 
 +CAST(4, - 3, typ.i64, 11)), 
 match5(// / //"Q2FZbuiltinZrealZreal"_1,4, 
 CAST(1, ibcsub1, typ.double, 11) 
 +CAST(2, ibcsub2, typ.double, 11) 
 +BINOP(3,   - 1,   - 2, 4) 
 +CAST(4,   - 3, typ.i64, 11)), 
 match5(// ? //"Q3FZbuiltinZrealZreal"_1,7, 
 CAST(1, ibcsub1, typ.double, 11) 
 +CAST(2, ibcsub2, typ.double, 11) 
 +CMP2(3,  - 1,  - 2, 3) 
 +CAST(4,  - 3, typ.i64, CASTZEXT) 
 +CMP2(5,  - 1,  - 2, 2) 
 +CAST(6,  - 5, typ.i64, CASTZEXT) 
 +BINOP(7,  - 4,  - 6, 0, typ.i64))
 , match5("intpartZbuiltinZreal"_1,2, 
   CAST(1, ibcsub1, typ.double, 11) 
   +CAST(2,  - 1, typ.i64, // fptosi double // 4)), 
 match5("int2realZbuiltinZint"_1,2,  // sitofp // 
 CAST(1, ibcsub1, typ.double, 6) 
 +CAST(2,  - 1, typ.i64, 11)), 
 match5("sqrtZbuiltinZreal"_1, 3,
 CAST(1, ibcsub1, typ.double, 11) 
 +CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.sqrt.f64",  - 1) 
 +CAST(3,- 2, typ.i64, 11)), 
 match5("sinZbuiltinZreal"_1, 3,
 CAST(1, ibcsub1, typ.double, 11) 
 +CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.sin.f64",  - 1) 
 +CAST(3, - 2, typ.i64, 11)), 
 match5("cosZbuiltinZreal"_1, 3,
 CAST(1, ibcsub1, typ.double, 11) 
 +CALL(2, 0, 32768, typ.function.[ double, double], C.merge."llvm.cos.f64",  - 1) 
 +CAST(3,  - 2, typ.i64, 11)),
 // match5("Q2BZbuiltinZbitsZint"_1,1, BINOP(1, ibcsub1, ibcsub2,  7, typ.i64)), 
 match5("Q2DZbuiltinZbitsZint"_1,1, BINOP(1, ibcsub1, ibcsub2,  8, typ.i64)), // 
  match5("Q3CQ3CZbuiltinZbitsZint"_1,1, BINOP(1, ibcsub1, ibcsub2, // SHL // 7, typ.i64)), 
 match5("Q3EQ3EZbuiltinZbitsZint"_1,1, BINOP(1, ibcsub1, ibcsub2, // LSHR // 8, typ.i64)), 
match5("QE2Q88QA7ZbuiltinZbitsZbits"_1,1, BINOP(1, ibcsub1, ibcsub2, // AND // 10, typ.i64)), 
match5("QE2Q88QA8ZbuiltinZbitsZbits"_1,1, BINOP(1, ibcsub1, ibcsub2, // OR // 11, typ.i64))]


 

Function lookup(t:seq.match5, inst:word) match5 
 let a =match5(inst,0, emptyinternalbc)
 let i = binarysearch(t, a)
  if i < 0 then a else (t_i)


Function CASTZEXT int 1

Function CASTTRUNC int 0

Function CASTPTRTOINT int 9

Function CASTINTTOPTR int 10


Function idxmacro internalbc 
 BLOCKCOUNT(1, 6) 
 +CAST(4, -2, typ.ptr.i64, CASTINTTOPTR) 
 +LOAD(5, -4, typ.i64, align8, 0) 
 +CMP2(6, -5, C64.0, 32) 
 +BR(7, 1, 2, -6) 
 +GEP(7, 1, typ.i64, -4, C64.1) 
 +GEP(8, 1, typ.i64, -7, -3) 
 +LOAD(9, -8, typ.i64, align8, 0) 
 +BR(10, 5) 
 +CMP2(10, -5, C64.1, 32) 
 +BR(11, 3, 4, -10) 
 +BINOP(11, -2, C64.15, 0, typ.i64) 
 +BINOP(12, -11, -3, 0, typ.i64) 
 +CAST(13, -12, typ.ptr.i8, CASTINTTOPTR) 
 +LOAD(14, -13, typ.i8, align8, 0) 
 +CAST(15, -14, typ.i64, 1) 
 +BR(16, 5) 
 +CAST(16, -5, typ.ptr.function.[ i64, i64, i64, i64], CASTINTTOPTR) 
 +CALL(17, 0, 32768, typ.function.[ i64, i64, i64, i64], -16, -1, -2, -3) 
 +BR(18, 5) 
 +PHI(18, typ.i64, -9, 1, -15, 3, -17, 4) 
 +RET(19, -18)

