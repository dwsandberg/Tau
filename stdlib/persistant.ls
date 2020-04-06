Module persistant

use UTF8

use bits

use encoding.seq.char

use persistantseq.encodingrep.seq.char

use seq.encodingrep.seq.char

use set.encodingrep.seq.char

use encoding.const3

use seq.const3


use seq.liblib

use persistantseq.libmod

use seq.libmod

use libscope

use persistantseq.libsym

use seq.libsym


use ipair.linklists2

use seq.linklists2

use llvm

use persistantseq.mytype

use seq.mytype

use stdlib


use encoding.word3

use seq.encodingrep.word3

use seq.word3

use words


Function type:linklists2 internaltype export

type linklists2 is record abc:seq.int 


function linklists2(seq.int) linklists2 export 
 

Function createlinkedlists linklists2 linklists2(empty:seq.int)

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


Function addconst( fullinst:seq.word)   int
buildconst (fullinst, 2, ipair(0,createlinkedlists),empty:stack.int) 
 

use stack.int

function buildconst (s:seq.word, i:int, last:ipair.linklists2,result:stack.int) int
 if i + 1 > length.s then 
 assert length.toseq.result=1 report "XXXX"
 index.last
 else
  let c = subseq(s, i, i + 1)
   if c_1 = "CRECORD"_1 then
   let nosons = toint.c_2
    let t=addobject(last,top(result,nosons))
     buildconst(s, i + 2, t,push(pop(result, nosons), objectref.t))
   else if c_1 = "WORDS"_1 then
   let len = toint.c_2
     // assert false report subseq(s, i, len + 1)//
     let   t=addwordseq(subseq(s, i+2, i + len + 1))
     buildconst(s, i + len + 2,ipair(t,value.last), push(result, objectref.t))
   else  if c_1 = "LIT"_1 then
  buildconst(s, i+2,last,push(result, C64.toint.s_(i+1)))
  else if c_1 = "WORD"_1 then
  let discard = registerword.s_(i+1)
    buildconst(s, i+2,last,push(result,  C64.hash.s_(i+1) ))
  else 
   assert c_1 = "FREF"_1 report "PROBLEM in persistant module"
  buildconst(s, i+2,last,
   push(result, C(i64, [ CONSTCECAST, 9, typ.ptr.getftype.s_(i+1), C.[s_(i+1)]]) ))


 


function addrecord(l:ipair.linklists2, s:mytype)ipair.linklists2 
ipair(addwordseq(towords.s),value.l)

function addrecord(l1:ipair.linklists2, sym:libsym)ipair.linklists2
 let a = addwordseq(returntype.sym)
 let b = addwordseq(instruction.sym)
   addobject(l1,[ wordref.fsig.sym,objectref.a,objectref.b])
  
  
Function wordref(w:word) int
let discard = registerword.w
 C64.hash.w

  

function ?(a:encodingrep.seq.char, b:encodingrep.seq.char)ordering valueofencoding.code.a ? valueofencoding.code.b

Function addliblib(lin:ipair.linklists2, t:liblib) int
 // assert libname.t ="stdlib"report libname.t //
 let a = addwordseq(libname.t)
 let c = addseq(lin, mods.t)
 let used = @(+, eword2, empty:seq.encodingrep.seq.char, orderadded.word3encoding)
 let have = if libname.t = "stdlib"then empty:seq.encodingrep.seq.char else words.loadedlibs_1
 let d = addseq(c, toseq(asset.used - asset.have))
 objectref.addobject( [ objectref.a,objectref.d,objectref.c,C64.timestamp.t,C64.toint.readonly.t])
 
 
function addobject(d:ipair.linklists2,flds:seq.int) ipair.linklists2
   ipair( addobject(flds),value.d)
   
Function addobject(flds:seq.int) int
    let t=orderadded.const3e
 //     assert length.t =0 &or (place.last.t+length.flds.last.t)=place.l report "XX"+toword(place.last.t+length.flds.last.t)+toword.place.l
 // let place=if length.t=0 then 0 else place.last.t+length.flds.last.t
  let x = decode(const3e, encode(const3e, const3(place , flds )))
   if place.x ≠ place  then place.x
   else
    // have not  seen this CRECORD before so process it //
   place


 
 
Function addrecord(lin:ipair.linklists2, e:encodingrep.seq.char)ipair.linklists2
 let k = addintseq(tointseq.data.e)
 addobject(lin,[C64.valueofencoding.code.e,objectref.k,C64.hash.e])
 
 
function addrecord(lin:ipair.linklists2, modx:libmod)ipair.linklists2
 let a = addseq( lin, defines.modx)
 let b = addseq( a, exports.modx)
 let c = addseq( b, uses.modx)
 addobject(c,[C64.toint.parameterized.modx , wordref.modname.modx ,objectref.a   ,objectref.b ,objectref.c])
 
 
Function addwordseq( a:seq.word) int
 let discard = @(+, registerword, 0, a)
  addintseq(@(+, hash, empty:seq.int, a))

function addintseq( s:seq.int) int
 addobject(@(+, C64, [ C64.0, C64.length.s], s))
 
 
Function objectref(d:ipair.linklists2) int
 objectref(index.d)

    
Function objectref(idx:int) int
let conststype = array(-2, i64)
    C(i64,[ CONSTCECAST, 9, typ.ptr.i64,getelementptr(conststype,"list", idx)])   

    
 
     