Module persistant

use UTF8

use bits

use encoding.seq.char


use seq.encodingpair.seq.char

use set.encodingpair.seq.char

use encoding.const3

use seq.const3


use libdesc


use seq.liblib

use llvm

use llvmconstants

use stdlib


use encoding.word3

use seq.encodingpair.word3

use seq.word3

use words
 
type word3 is record toword:word



function assignencoding(l:int, a:word3) int valueofencoding.asencoding.toword.a

 if toword.a in "//" then valueofencoding.asencoding.toword.a else  
toint(bits.assignrandom(l,a) &and  bits(toint( bits.1 << 31)-1))

valueofencoding.asencoding.toword.a

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

function eword2(ww:encodingpair.word3)encodingpair.seq.char
  let w=data.ww
  let a = decodeword.toword.w
  encodingpair(to:encoding.seq.char(valueofencoding.encode( w))
    , a
    )
  
  
  
use seq.encodingpair.const3

Function constdata seq.int @(+,flds,empty:seq.int,encoding:seq.encodingpair.const3)

type const3 is record place:int, flds:seq.int

function flds(p:encodingpair.const3) seq.int  flds.data.p


function =(a:const3, b:const3)boolean flds.a = flds.b

function hash(a:const3)int hash.flds.a  

function assignencoding(l:int, a:const3) int assignrandom(l,a)

  
Function wordref(w:word) int  
let d = encode(  word3.w)
 C64.valueofencoding.d
 
 Function addliblib( libname:seq.word,mods:int) int
 // assert libname.t ="stdlib"report libname.t //
 let  name=addwordseq2(libname)
  let have = if libname = "stdlib"then empty:seq.encodingpair.seq.char else words.loadedlibs_1
 let used = @(+, eword2, empty:seq.encodingpair.seq.char, encoding:seq.encodingpair.word3 )
 let k=@(+,addrecord2,empty:seq.int,toseq(asset.used - asset.have))
 let wordreps= addobject([C64.0 , C64.length.k]+k) 
// let wordreps=addobject("wordreps",[C64.0 , C64.length.k]+k) //
 addobject("liblib",[ name,wordreps,mods,C64.0,C64.0])
  

function addobject(name:seq.word,data:seq.int) int
let objtype=array(length.data,i64)
let ll= global( "liblib",   objtype , C( objtype, [ AGGREGATE]  + data) )
    C(i64,[ CONSTCECAST, 9, typ.ptr.i64, CGEP2(ll,0)]) 

   
 function global(name:seq.word,type:llvmtype,init:int) int
modulerecord( name ,[ MODULECODEGLOBALVAR, typ.type, 2, 1+init, 0, align8 + 1, 0])

 
function CGEP2( p:int ,b:int) int
let t1 = consttype.p
// assert typ.consttype.p=typ.t1 &or (b in [1280,1278,1303,1302])report "diff"+toword.b+toword.typ.consttype.p+toword.p //
 C(ptr.i64, [ CONSTGEP, typ.t1, typ.ptr.t1, p, typ.i32, C32.0,typ.i64, C64.b] )
  
 
Function addobject(flds:seq.int) int
  let t=encoding:seq.encodingpair.const3
  let place=if length.t=0 then 0 else place.data.last.t+length.flds.data.last.t
  let x = decode(encode(const3(place , flds )))
 let idx=if place.x ≠ place  then place.x else   place
  C(i64,[ CONSTCECAST, 9, typ.ptr.i64, CGEP(modulerecord("list", [0]),C32.0,C64.idx)])   

function CGEP( p:int,a:int,b:int) int
let t1 = array(-2, i64)
// assert typ.consttype.p=typ.t1 &or (b in [1280,1278,1303,1302])report "diff"+toword.b+toword.typ.consttype.p+toword.p //
 C(ptr.i64, [ CONSTGEP, 1, typ.ptr.t1, p, typ.consttype.a, a, typ.consttype.b, b] )
 
 


function addrecord2( e:encodingpair.seq.char) int
 let s= tointseq.data.e
  let k=addobject(@(+, C64, [ C64.0, C64.length.s], s))
  addobject([C64.valueofencoding.code.e,k,C64.hash.e])
 
 
Function addwordseq2( a:seq.word) int
  addobject.@(+, wordref, [ C64.0, C64.length.a], a)
 

use seq.llvmconst

use encoding.llvmconst

use seq.encodingpair.llvmconst

/Function dump seq.word
  let c=constdata
  let t=    (encoding:seq.encodingpair.llvmconst)
  bb(c,t,length.c-1000,empty:seq.word)
  
  @(seperator."&br",print.t,"",subseq(c,length.c-1000,length.c))
   
 / function bb(c:seq.int,t:seq.encodingpair.llvmconst,i:int,result:seq.word) seq.word
    if i > length.c then result else 
     bb(c,t,i+1,result+"&br"+toword.(i-1)+print(t,c_i))
   
/   function print(s:seq.encodingpair.llvmconst,i:int) seq.word let t=data.s_(i+1) 
    let recargs=subseq(toseq.t,2,length.toseq.t)
    let rectype=(toseq.t)_1
      if typ.t=typ.i64 &and  rectype=CONSTINTEGER then "C64."+toword.(toseq.t)_2
    else
   (if typ.t=typ.i64 then "i64" else [toword.typ.t])
    +if  rectype=CONSTINTEGER then "INTEGER" +toword.(toseq.t)_2
     else if rectype=CONSTCECAST then "CECAST"+@(+,toword,"", subseq(recargs,1,length.recargs-1) )
      +"("+ print(s,last.recargs) +")"
       else if rectype=CONSTGEP then "GEP"+@(+,toword,"", subseq(recargs,1,length.recargs-1) )
      +"("+ print(s,last.recargs) +")"
     else 
       @(+,toword,"", toseq.t )
      
      
     
  
 
     