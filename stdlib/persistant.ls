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


use seq.libsym


use llvm


use seq.mytype

use stdlib


use encoding.word3

use seq.encodingrep.word3

use seq.word3

use words
 


type word3encoding is encoding word3

function assignencoding(l:int, a:word3) int assignrandom(l,a)

_________________

encode Functions




Function constdata seq.int @(+,flds,empty:seq.int,orderadded.const3e)



type word3 is record toword:word

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a


Function registerword(a:word)int
 let d = encode(word3encoding, word3.a)
  0

function eword(w:word3)seq.int
 let a = tointseq.decodeword.toword.w
  @(+, C64, [ C64.0, C64.length.a], a)

function eword2(w:word3)encodingrep.seq.char
 let a = decodeword.toword.w
  encodingrep(asencoding.toword.w, a, hash.a)



type const3 is record place:int, flds:seq.int


type const3e is encoding const3


function =(a:const3, b:const3)boolean flds.a = flds.b

function hash(a:const3)int hash.flds.a  

function assignencoding(l:int, a:const3) int assignrandom(l,a)




function addrecord2( s:mytype)int addwordseq2(towords.s) 

function addrecord2( sym:libsym)int
 let a = addwordseq2(returntype.sym)
 let b = addwordseq2(instruction.sym)
   addobject([ wordref.fsig.sym, a, b])
  
  
Function wordref(w:word) int
let discard = registerword.w
 C64.hash.w

  

function ?(a:encodingrep.seq.char, b:encodingrep.seq.char)ordering valueofencoding.code.a ? valueofencoding.code.b

Function addliblib( t:liblib) int
 // assert libname.t ="stdlib"report libname.t //
 let  a=addwordseq2(libname.t)
 let c = addseq.@(+,addrecord2,empty:seq.int,mods.t)
 let used = @(+, eword2, empty:seq.encodingrep.seq.char, orderadded.word3encoding)
 let have = if libname.t = "stdlib"then empty:seq.encodingrep.seq.char else words.loadedlibs_1
 let d = addseq.@(+,addrecord2,empty:seq.int,toseq(asset.used - asset.have))
 addobject( [ a,d,c,C64.timestamp.t,C64.toint.readonly.t])
 
Function addobject(flds:seq.int) int
  let t=orderadded.const3e
  let place=if length.t=0 then 0 else place.last.t+length.flds.last.t
  let x = decode(const3e, encode(const3e, const3(place , flds )))
  objectref.if place.x ≠ place  then place.x else   place

Function addrecord2( e:encodingrep.seq.char) int
 let k = addintseq(tointseq.data.e)
 addobject([C64.valueofencoding.code.e,k,C64.hash.e])
 
 
function addrecord2(modx:libmod)int
 let a = addseq.@(+,addrecord2,empty:seq.int, defines.modx)
 let b = addseq.@(+,addrecord2,empty:seq.int, exports.modx)
 let c = addseq.@(+,addrecord2,empty:seq.int, uses.modx)
 addobject( [C64.toint.parameterized.modx , wordref.modname.modx ,a   ,b ,c])
 
Function addwordseq2( a:seq.word) int
 let discard = @(+, registerword, 0, a)
  addintseq(@(+, hash, empty:seq.int, a))

function addintseq( s:seq.int) int
 addobject(@(+, C64, [ C64.0, C64.length.s], s))
 
function objectref(idx:int) int
let conststype = array(-2, i64)
    C(i64,[ CONSTCECAST, 9, typ.ptr.i64,getelementptr(conststype,"list", idx)])   

Function    addseq(k:seq.int) int  
  addobject([C64.0 , C64.length.k]+k)
    
 
     