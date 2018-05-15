module persistant

use bits

use internalbc

use ipair.linklists2

use libscope

use llvm

use oseq.word

use fileio

use process.int

use process.liblib

use processtypes



use seq.encoding.llvmtype

use seq.int

use seq.liblib

use seq.libmod

use seq.libsym

use seq.libtype

use seq.linklists2

use seq.mytype

use seq.word3

use set.libtype

use set.word

use stacktrace

use stdlib

type word3encoding is encoding word3

Function wordcount int length.mapping.word3encoding

Function worddata seq.int 
 let ws = mapping.word3encoding 
  @(+, eword, [ C64.0, C64.length.ws], ws)

_________________

encode Functions

The linklists2 type contains a seq of integers that represents the memory.
 Any memory locations that store the type word are linked into a linked list begining with wordthread. 
 Two values are packed into the integer is store in the seq. 
 One is the word3 encoding and the other the next value in the linked list. 
 Any memory locations that store an address of another memory are linked into a linked list beginning with offsetthread. 
 In this case the element in the seq is represents two interger values. 
 One is the next value in the linked list and the other is the index of the refrenced memory location.

type linklists2 is record a:seq.int, wordthread:int, offsetthread:int,  wordseqthread:int


          

Function createlinkedlists linklists2
linklists2(empty:seq.int, 0, 0,0)
 


Function a(linklists2)seq.int export

Function initializer(conststypex:encoding.llvmtype, data:linklists2)int 
 C(conststypex, [ AGGREGATE, C64.0, C64(length.a.data + 3), C64.wordthread.data, C64.offsetthread.data, C64.wordseqthread.data]+ 
 a.data)+ 1


type word3 is record toword:word

function =(a:word3, b:word3)boolean toword.a = toword.b

function hash(a:word3)int hash.toword.a

Function place(a:linklists2)int  length.a.a + 4

Function word33(a:word)int encoding.encode(word3.a, word3encoding)

function eword(w:word3)seq.int 
 let a = decode.toword.w 
  @(+, C64, [ C64.0, C64.length.a], a)





Function getftype(w:word)encoding.llvmtype 
 let a = @(+, count.90, 1, decode.w)
  function.constantseq(a, i64)

function count(val:int, i:int)int if val = i then 1 else 0

function cast2int(liblib)int builtin

function cast2intseq(int)seq.int builtin

function cast2word(int)word builtin

use seq.linklists2


  
Function prepareliblib2(alltypes:set.libtype,x:linklists2,mylib:liblib)ipair(linklists2 )
   addobject2(alltypes, mytype."liblib", x, cast2int( // result.process.identity.// mylib))
   

   

use ipair(mytype)

use tree.seq.word

use seq.tree.seq.word


use seq.flddesc

type  trackflds is record l:linklists2,flds:seq.flddesc,state:int

type  flddesc is record  index:int,kind:word

type const3 is record place:int,flds:seq.flddesc

function =(a:flddesc,b:flddesc) boolean index.a=index.b &and kind.a=kind.b

type const3e is encoding const3 

function =(a:const3,b:const3) boolean flds.a=flds.b

use seq.const3

function hash(a:const3) int length.flds.a+@(+,index,0,flds.a)

Function addconst(l:linklists2, fullinst:seq.word) ipair(linklists2)
   addconst(l,buildconsttree(fullinst ,2,empty:stack.tree.seq.word))
   
use stack.tree.seq.word

 function buildconsttree( s:seq.word,  i:int, result:stack.tree.seq.word) tree.seq.word 
   if i+1 > length.s then top(result)
   else let c=subseq(s,i,i+1) 
    if c_1="CRECORD"_1 then 
       let nosons=toint.c_2
        buildconsttree(s, i+2,push(pop(result,nosons),tree(c,top(result,nosons))))
    else
     buildconsttree(s, i+2,push(result, tree.c))

     
Function addconst(l:linklists2,t:tree.seq.word) ipair(linklists2)
// First build description of record. This may add other const records to l //
let y =@(getindex,identity,trackflds(l,empty:seq.flddesc,1),sons.t)
  // look up CRECORD to see if we have already used it. //
     let x=decode(encode(const3(place.l.y,flds.y),const3e),const3e)
     if  place.x &ne place.l.y then ipair(place.x,l.y)
     else   
     // have seen this CRECORD before so process it //
     // assert not( nosons.t > 4 &and state.y=3 ) &or isnumber.(label.t_1)_2 report "ZZZ"+@(+,label,"",sons.t)+label.t //
     let newlist= if  nosons.t > 4 &and state.y=3 &and toint.(label.t_1)_2=nosons.t-2 then
        // word seq //
          linklists2( @(+,index, a.l.y +
          C64.wordseqthread.l.y,subseq(flds.y,2,length.flds.y)),wordthread.l.y, offsetthread.l.y,place.l.y)
     else @(buildtheobject(place.l.y),identity,l.y,flds.x)
    ipair(place.l.y,newlist)
    
function getindex(f:trackflds,t:tree.seq.word) trackflds
  let typ=(label.t)_1
   if typ="LIT"_1 then
    trackflds(l.f,flds.f+flddesc(C64.toint.(label.t)_2,"LIT"_1),if state.f=1 &and  label.t="LIT 0" then 2 else 
     if state.f=2 then 3 else 0)
   else if typ="WORD"_1  then
      trackflds(l.f,flds.f+flddesc(word33.(label.t)_2,"WORD"_1),if state.f=3 then 3 else 0)
   else if typ="FREF"_1 then
     trackflds(l.f,flds.f+flddesc(C(i64, [ CONSTCECAST, 9, typ.ptr.getftype.(label.t)_2, C.[ (label.t)_2]]), "LIT"_1),0)
   else 
    assert (label.t)_1="CRECORD"_1 report "PROBLEM"
     let k = addconst(l.f,t)
     trackflds(value.k,flds.f+flddesc(index.k, "CRECORD"_1),0)

use seq.linklist2

function buildtheobject(objectstart:int,l:linklists2,d:flddesc) linklists2
FORCEINLINE.let typ=kind.d
      let newwordthread=if typ="WORD"_1 then place.l else wordthread.l
      let newoffsetthread=if typ="CRECORD"_1 then place.l else offsetthread.l
      linklists2(a.l+
      if typ="LIT"_1 then 
          index.d
      else  if typ="WORD"_1 then 
         C64.packit(wordthread.l, index.d) 
      else 
          C64.packit(offsetthread.l, index.d) 
 ,newwordthread,newoffsetthread, wordseqthread.l) 

 
function addobject2(alltypes:set.libtype,a:mytype,l:linklists2,data:int) ipair.linklists2
  // assert a in [ mytype."int", mytype."word", mytype."word seq", mytype."int seq seq", mytype."liblib", mytype."libtype seq", mytype."libtype", mytype."mytype seq", mytype."mytype"
  ,mytype."libmod seq"]report"??"+ towords.a //
 if a = mytype."word seq" &or  a= mytype."mytype" 
  then ipair(place.l,addwordseq(l , cast2wordseq.data ))
  else           
    if abstracttype.a ="seq"_1 then
      let s = cast2intseq.data
      if a = mytype."int seq" &or  a = mytype."real seq" then
         ipair(place.l,linklists2(@(+,  C64,a.l+C64.0+length.s,s),wordthread.l,offsetthread.l, wordseqthread.l))
      else
           let x=@(getindexseq(alltypes,parameter.a),identity,trackflds(l,empty:seq.flddesc,0),s)
       let t= linklists2( a.l.x+C64.0+C64.length.s,wordthread.l.x,offsetthread.l.x, wordseqthread.l.x)
       ipair(place.l.x,@(buildtheobject(place.l.x),identity,t,flds.x))
   else 
     let b = deepcopytypes2(alltypes, a)
     let x=@(getindex(alltypes,b,data),identity,trackflds(l,empty:seq.flddesc,1),arithseq(length.b,1,1))
  ipair(place.l.x,@(buildtheobject(place.l.x),identity,l.x,flds.x))


function getindexseq( alltypes:set.libtype,elementtype:mytype,f:trackflds,dataelement:int) trackflds
    // assert towords.elementtype in ["libtype", "mytype","libmod","libsym"] report towords.elementtype //
   let k= addobject2(alltypes,elementtype,l.f,dataelement)
    trackflds(value.k,flds.f+flddesc(index.k, "CRECORD"_1),0)
   
 
function getindex(alltypes:set.libtype,b:seq.mytype,data:int,f:trackflds,i:int) trackflds
 let elementtype=b_i
 let dataelement=IDXUC(data,i-1)
  if elementtype = mytype."int" &or elementtype = mytype."real" then
    trackflds(l.f,flds.f+flddesc(C64.dataelement,"LIT"_1),0) 
  else if elementtype = mytype."word" then
          trackflds(l.f,flds.f+flddesc(word33.cast2word.dataelement,"WORD"_1),  0)
  else 
   let k= addobject2(alltypes,elementtype,l.f,dataelement)
    trackflds(value.k,flds.f+flddesc(index.k, "CRECORD"_1),0)
    

Function addwordseq(t:linklists2, a:seq.word)linklists2 
    linklists2(a.t + @(+,C64word33,[ C64.wordseqthread.t, C64.length.a],a), wordthread.t, offsetthread.t,place.t)
 
 function C64word33(a:word) int C64.word33.a 

function cast2int(s:seq.int)int builtin

function interface(l:liblib, dependlibs:seq.word)seq.word 
 let a = createlib(cast2int.empty:seq.int,"int seq", l, dependlibs)
  {"OK"}

Function interface(name:seq.word, modlist:seq.word, deplibs:seq.word)seq.word 
 let mods = @(+, findmods.modlist, empty:seq.libmod, libs)
  let alltypes = asset.@(+, types, empty:seq.libtype, libs)
  let llplus = @(∪, libtypes("cannot find type", alltypes), empty:set.libtype, [ mytype."liblib", 
  mytype."libtype", 
  mytype."libmod", 
  mytype."offset", 
  mytype."mytype", 
  mytype."libsym"])
  let types = @(∪, libtypes.alltypes, llplus, mods)
  interface(liblib(name, toseq.types, mods, true), deplibs)+ @(seperator."&br", print,"", toseq.types)

function findmods(keep:seq.word, l:liblib)seq.libmod @(+, findmod.keep, empty:seq.libmod, mods.l)

function findmod(keep:seq.word, m:libmod)seq.libmod 
 if modname.m in keep then [ m]else empty:seq.libmod

function libtypes(s:set.libtype, a:libmod)set.libtype 
 @(∪, libtypes.s, empty:set.libtype, exports.a + defines.a)

Function createlib2(thedata:int, encodetype:seq.word, libname:word, dependlibs:seq.word)int 
 let mymod = libmod(false, libname, empty:seq.libsym, empty:seq.libsym, libname)
  let mylib = liblib([ libname], empty:seq.libtype, [ mymod])
  createlib(thedata, encodetype, mylib,"")

function createlib(thedata:int, thetype:seq.word, mylib:liblib, dependlibs:seq.word)int 
 // must call as process so that the encodings start out empty // 
  result.process.createlibp(thedata, thetype, mylib, dependlibs)


function createlibp(thedata:int, thetype:seq.word, mylib:liblib, dependlibs:seq.word)int 
 let libname = libname(mylib)_1 
  let symtab ="libname initlib5 words wordlist list  init22"
  let discard = @(+, C, 0, symtab)
  let alltypes = asset.@(+, types, empty:seq.libtype, libs)
  let data1 = addobject2(alltypes, mytype(thetype +"seq"), createlinkedlists, thedata)
  let liblib= prepareliblib2(alltypes, value.data1, mylib)
  let data =value.liblib
   let words = worddata 
  let worddatatype = array(length.words + 2, i64)
  let wordstype = array(2 + wordcount, i64)
  let conststype2 = array(length.a.data + 5, i64)
  let libnametype = array(length.decode.libname + 1, i8)
  let libnameptr = C(ptr.i8, [ CONSTGEP, typ.libnametype, typ.ptr.libnametype, C."libname", typ.i32, C32.0, typ.i32, C32.0])
  let deflist = [ // libname // 
   [ MODULECODEGLOBALVAR, 
   typ.libnametype, 
   2, 
   C(libnametype, [ CONSTDATA]+ decode.libname + 0)+ 1, 
   3, 
   align4, 
   0], 
  [ MODULECODEFUNCTION, 
  typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64, ptr.i64, ptr.i64], 
  0, 
  1, 
  0, 
  1, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0, 
  0], 
  [ MODULECODEGLOBALVAR, typ.wordstype, 2, C(i64, [ CONSTNULL])+ 1, 3, align8 + 1, 0], 
  [ MODULECODEGLOBALVAR, 
  typ.worddatatype, 
  2, 
  1 + C(worddatatype, [ AGGREGATE, C64.0, C64.length.words]+ words), 
  3, 
  align8 + 1, 
  0], 
  [ MODULECODEGLOBALVAR, 
  typ.conststype2, 
  2, 
  C(conststype2, [ AGGREGATE, C64.0, C64(length.a.data + 3), C64.wordthread.data, C64.offsetthread.data, C64.wordseqthread.data]+ a.data)+ 1, 
  3, 
  align8 + 1, 
  0], 
  // init22 // [ MODULECODEFUNCTION, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
  let bodytxts = [ BLOCKCOUNT(1, 1)+ 
  CALL(1, 0, 32768, typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64, ptr.i64, ptr.i64], 
  C."initlib5", 
  libnameptr,
   getelementptr(wordstype,"words",0), 
  getelementptr(worddatatype,"wordlist",0),
   getelementptr(conststype2,"list",0), 
  getelementptr(conststype2,"list",index.liblib+1),
  getelementptr(conststype2,"list",index.data1+1)
  )+ RET.3]
  createlib(llvm(deflist, bodytxts, typerecords), libname,"")

______________________________

Three Functions to pack two ints into 64 bits

function halfsize int // 2^31 // 2147483648


Function getlink(a:int)int  toint(bits(a) >> 31 )- halfsize

Function packit(link:int, b:int)int toint ( bits(halfsize + link) << 31 ∨ bits(b) ) 

Function getb(a:int)int toint(bits(a) ∧ bits( halfsize  - 1))

Function IDXUC(int, int)int builtin.IDXUC

Function cast2wordseq(int)seq.word builtin



  
