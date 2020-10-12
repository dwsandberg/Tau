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
 toint.C64.valueofencoding.d
 
 Function addliblib( libname:seq.word,mods:int) int
 // assert libname.t ="stdlib"report libname.t //
 let  name=addwordseq2(libname)
  let have = if libname = "stdlib"then empty:seq.encodingpair.seq.char else words.loadedlibs_1
 let used = @(+, eword2, empty:seq.encodingpair.seq.char, encoding:seq.encodingpair.word3 )
 let wordstoadd=toseq(asset.used - asset.have)
 // build packed seq of word encodings //
 let data=@(+,fldsofwordencoding,[toint.C64.3 , toint.C64.length.wordstoadd],wordstoadd) 
   let wordreps= addobject.data
 addobject("liblib",[ name,wordreps,mods,toint.C64.0,toint.C64.0])

 Function addliblib( libname:seq.word,mods:int,profiledata:int) int
 // assert libname.t ="stdlib"report libname.t //
 let  name=addwordseq2(libname)
  let have = if libname = "stdlib"then empty:seq.encodingpair.seq.char else words.loadedlibs_1
 let used = @(+, eword2, empty:seq.encodingpair.seq.char, encoding:seq.encodingpair.word3 )
 let wordstoadd=toseq(asset.used - asset.have)
 // build packed seq of word encodings //
 let data=@(+,fldsofwordencoding,[toint.C64.3 , toint.C64.length.wordstoadd],wordstoadd) 
   let wordreps= addobject.data
 addobject("liblib",[ name,wordreps,mods,toint.C64.0,profiledata])

use seq.slot

function addobject(name:seq.word,data:seq.int) int
let objtype=array(length.data,i64)
let ll= global( "liblib",   objtype ,  toint.AGGREGATE.@(+,slot,empty:seq.slot,data)  )
   toint.ptrtoint( ptr.i64, CGEP(slot.ll,0)) 

   
 function global(name:seq.word,type:llvmtype,init:int) int
toint.modulerecord( name ,[ toint.GLOBALVAR, typ.type, 2, 1+init, 0, toint.align8 + 1, 0])

 
  
 
Function addobject(flds:seq.int) int
  let t=encoding:seq.encodingpair.const3
  let place=if length.t=0 then 0 else place.data.last.t+length.flds.data.last.t
  let x = decode(encode(const3(place , flds )))
 let idx=if place.x ≠ place  then place.x else   place
  toint.ptrtoint(ptr.i64, CGEP(modulerecord("list", [0]),idx))   

 
 


function fldsofwordencoding( e:encodingpair.seq.char) seq.int
 let s= tointseq.data.e
  let k=addobject(@(+,toint,empty:seq.int,@(+, C64, [ C64.0, C64.length.s], s)))
    ([toint.C64.valueofencoding.code.e,k,toint.C64.hash.e]) 
 
 
Function addwordseq2( a:seq.word) int
  addobject.@(+, wordref, [ toint.C64.0, toint.C64.length.a], a)
 

/use seq.llvmconst

/use encoding.llvmconst

/use seq.encodingpair.llvmconst

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
      
      
     
  
 
     