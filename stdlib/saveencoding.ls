module saveencoding

use bits

use fileio

use internalbc

use ipair.linklists2

use libscope

use llvm

use process.int

use processtypes

use seq.flddesc

use seq.int

use seq.liblib

use seq.mytype

use set.libtype

use stdlib

use persistant

use reconstruct

Function addobject2(alltypes:set.libtype, a:mytype, l:linklists2, data:int)ipair.linklists2 
 // assert a in [ mytype."int", mytype."word", mytype."word seq", mytype."int seq seq", mytype."liblib", mytype."libtype seq",
  mytype."libtype", mytype."mytype seq", mytype."mytype", mytype."libmod seq"]report"??"+ towords.a // 
  if a = mytype."word seq"∨ a = mytype."mytype"
  then addwordseq(l, cast2wordseq.data)
  else if abstracttype.a ="seq"_1 
  then let s = cast2intseq.data 
   if a = mytype."int seq"∨ a = mytype."real seq"
   then ipair(place.l, linklists2(@(+, C64, a.l + C64.0 + length.s, s), wordthread.l, offsetthread.l, wordseqthread.l))
   else   let x = @(getindexseq(alltypes, parameter.a), identity, trackflds(l, empty:seq.flddesc, 0), s)
   let t = linklists2(a.l.x + C64.0 + C64.length.s, wordthread.l.x, offsetthread.l.x, wordseqthread.l.x)
   ipair(place.l.x, @(buildtheobject.place.l.x, identity, t, flds.x))
   else 
  let b = deepcopytypes2(alltypes, a)
  let x = @(getindex(alltypes, b, data), identity, trackflds(l, empty:seq.flddesc, 1), arithseq(length.b, 1, 1))
  ipair(place.l.x, @(buildtheobject.place.l.x, identity, l.x, flds.x))

function getindexseq(alltypes:set.libtype, elementtype:mytype, f:trackflds, dataelement:int)trackflds 
 // assert towords.elementtype in ["libtype","mytype","libmod","libsym"]report towords.elementtype // 
  let k = addobject2(alltypes, elementtype, l.f, dataelement)
  trackflds(value.k, flds.f + flddesc(index.k,"CRECORD"_1), 0)

function getindex(alltypes:set.libtype, b:seq.mytype, data:int, f:trackflds, i:int)trackflds 
 let elementtype = b_i 
  let dataelement = IDXUC(data, i - 1)
  if elementtype = mytype."int"∨ elementtype = mytype."real"
  then trackflds(l.f, flds.f + flddesc(C64.dataelement,"LIT"_1), 0)
  else if elementtype = mytype."word"
  then trackflds(l.f, flds.f + flddesc(word33.cast2word.dataelement,"WORD"_1), 0)
  else let k = addobject2(alltypes, elementtype, l.f, dataelement)
  trackflds(value.k, flds.f + flddesc(index.k,"CRECORD"_1), 0)

Function createlib2(thedata:int, encodetype:seq.word, libname:word, dependlibs:seq.word)int 
result.process.createlibp(thedata, encodetype,  libname )

use convertlibtyp

function createlibp(thedata:int, thetype:seq.word, libname:word)int 
  let symtab ="libname initlib5 words wordlist list init22"
  let discard = @(+, C, 0, symtab)
    let alltypes = asset.getalllibtypes
  let data1 = addobject2(alltypes, mytype(thetype +"seq"), createlinkedlists, thedata)
  let liblib = addliblib( value.data1, emptyliblib.libname)
  let data = value.liblib 
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
  C(conststype2, [ AGGREGATE, 
  C64.0, 
  C64(length.a.data + 3), 
  C64.wordthread.data, 
  C64.offsetthread.data, 
  C64.wordseqthread.data]+ a.data)+ 1, 
  3, 
  align8 + 1, 
  0], 
  // init22 // [ MODULECODEFUNCTION, typ.function.[ VOID], 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
  let bodytxts = [ BLOCKCOUNT(1, 1)+ CALL(1, 0, 32768, typ.function.[ i64, ptr.i8, ptr.i64, ptr.i64, ptr.i64, ptr.i64, ptr.i64], C."initlib5", libnameptr, getelementptr(wordstype,"words", 0), getelementptr(worddatatype,"wordlist", 0), getelementptr(conststype2,"list", 0), getelementptr(conststype2,"list", index.liblib + 1), getelementptr(conststype2,"list", index.data1 + 1))+ RET.3]
  createlib(llvm(deflist, bodytxts, typerecords), libname,"")




Function IDXUC(int, int)int builtin.IDXUC

Function cast2wordseq(int)seq.word builtin.NOOP




