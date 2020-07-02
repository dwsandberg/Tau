Module persistant

use UTF8

use bits

use encoding.seq.char


use seq.encodingrep.seq.char

use set.encodingrep.seq.char

use encoding.const3

use seq.const3


use seq.liblib


use seq.libmod

use libscope




use llvm


use seq.mytype

use stdlib


use encoding.word3

use seq.encodingrep.word3

use seq.word3

use words
 
type word3 is record toword:word


type word3encoding is encoding word3

function assignencoding(l:int, a:word3) int valueofencoding.asencoding.toword.a

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

function eword2(w:word3)encodingrep.seq.char
 let a = decodeword.toword.w
  encodingrep(asencoding.toword.w, a, hash.a)


Function constdata seq.int @(+,flds,empty:seq.int,orderadded.const3e)

type const3 is record place:int, flds:seq.int


type const3e is encoding const3


function =(a:const3, b:const3)boolean flds.a = flds.b

function hash(a:const3)int hash.flds.a  

function assignencoding(l:int, a:const3) int assignrandom(l,a)

  
Function wordref(w:word) int  
let d = encode(word3encoding, word3.w)
 C64.hash.w
 
 Function addliblib( libname:seq.word,c:int) int
 // assert libname.t ="stdlib"report libname.t //
 let  a=addwordseq2(libname)
  let have = if libname = "stdlib"then empty:seq.encodingrep.seq.char else words.loadedlibs_1
 let used = @(+, eword2, empty:seq.encodingrep.seq.char, orderadded.word3encoding)
 let k=@(+,addrecord2,empty:seq.int,toseq(asset.used - asset.have))
 let d= addobject([C64.0 , C64.length.k]+k)
  addobject( [ a,d,c,C64.0,C64.0])
 
Function addobject(flds:seq.int) int
  let t=orderadded.const3e
  let place=if length.t=0 then 0 else place.last.t+length.flds.last.t
  let x = decode(const3e, encode(const3e, const3(place , flds )))
 let idx=if place.x ≠ place  then place.x else   place
 let conststype = array(-2, i64)
    C(i64,[ CONSTCECAST, 9, typ.ptr.i64,getelementptr(conststype,"list", idx)])   


function addrecord2( e:encodingrep.seq.char) int
 let s= tointseq.data.e
  let k=addobject(@(+, C64, [ C64.0, C64.length.s], s))
  addobject([C64.valueofencoding.code.e,k,C64.hash.e])
 
 
Function addwordseq2( a:seq.word) int
  addobject.@(+, wordref, [ C64.0, C64.length.a], a)
 

use seq.llvmconst

use encoding.llvmconst

Function dump seq.word
  let c=constdata
  let t=    (orderadded.llvmconsts)
  bb(c,t,length.c-1000,empty:seq.word)
  
  @(seperator."&br",print.t,"",subseq(c,length.c-1000,length.c))
   
  function bb(c:seq.int,t:seq.llvmconst,i:int,result:seq.word) seq.word
    if i > length.c then result else 
     bb(c,t,i+1,result+"&br"+toword.(i-1)+print(t,c_i))
   
   function print(s:seq.llvmconst,i:int) seq.word let t=s_(i+1) 
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
      
      
     
  
 
     