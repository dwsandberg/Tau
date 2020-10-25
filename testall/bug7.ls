#!/usr/local/bin/tau


run bug7 testbug7

module bug7

use stdlib

use seq.slot2

use encoding.slot2

use seq.llvmtypeele2

use encoding.llvmtypeele2

use seq.seq.int

type  slot2 is record type:int,rec:seq.int,name:seq.word

function =(a:slot2,b:slot2) boolean rec.a=rec.b &and  type.a= type.b &and name.a=name.b

function hash(a:slot2) int hash(rec.a)

function assignencoding(a:int, slot2) int a+1

Function c32(i:int) encoding.slot2  encode(  slot2(i32, [ 45, i] ,""))

Function testbug7 seq.word 
 // since encodings have side effects it is not safe to use simple inline expansion of functions
  since the order of evaluation becomes important. Function c32 is the candiate for inline expansion. //
let discard0=[i64,i32]
  let z=c32.0  
if [ i64, i32] =[1,2] then "PASS bug7 " else "FAIL bug 7"

type llvmtypeele2 is record toseq:seq.int

function hash(a:llvmtypeele2)int hash.toseq.a

Function assignencoding(l:int, a:llvmtypeele2) int l+1

function =(a:llvmtypeele2, b:llvmtypeele2)boolean toseq.a = toseq.b 

Function i64 int valueofencoding.encode(llvmtypeele2.[ 7, 64])

Function i32 int valueofencoding.encode(llvmtypeele2.[ 7, 32])




 

  