Module llvm

In addition to the llvm bitcode format documentation, an useful file for reference is LLVMBitCodes.h

use UTF8

use seq.seq.seq.int

use seq.seq.int

use seq.encoding.llvmconst

use encoding.llvmconst

use seq.llvmconst

use otherseq.llvmtype

use seq.llvmtype

use encoding.llvmtypeele

use seq.seq.llvmtypeele

use seq.llvmtypeele

use stdlib

use llvmconstants


Function type:llvmtypeele internaltype export

Function type:llvmtype internaltype export

type llvmtypeele is record toseq:seq.int


type llvmtype is record index:int


function hash(a:llvmtypeele)int hash.toseq.a

Function assignencoding(l:int, a:llvmtypeele) int l+1


function =(a:llvmtypeele, b:llvmtypeele)boolean toseq.a = toseq.b 



/Function print(t:llvmtype) seq.word
let a=toseq.decode(to:encoding.llvmtypeele(index.t))
let tp=a_1
let b=@(+,llvmtype,empty:seq.llvmtype,@(+,+.1,empty:seq.int,a))
if tp = TYPEINTEGER then [ merge.("i" + toword.a_2)]
  else if tp = TYPEARRAY then
  "[" + toword.a_2 + "x" + print(b_3) + "]"
  else if tp = TYPEPOINTER then print(b_2) + "*"
  else if tp = TYPEFUNCTION then
    print(b_3)+"(" + @(seperator(","), print,"", subseq(b, 4, length.a))
   + ")"
  else if tp = TYPEVOID then"VOID"
  else if tp = TYPEDOUBLE then "double"
  else"?"

function cvttorec( a:encodingpair.llvmtypeele ) seq.int  toseq.data.a

Function typerecords seq.seq.int @(+, cvttorec, empty:seq.seq.int, encoding:seq.encodingpair.llvmtypeele)


Function typ(a:llvmtype)int index.a - 1

Function llvmtype(s:seq.int)llvmtype 
llvmtype.valueofencoding.encode(llvmtypeele.s) 

Function double llvmtype llvmtype.[ toint.DOUBLE]

Function i64 llvmtype llvmtype.[ toint.INTEGER, 64]

Function i32 llvmtype llvmtype.[ toint.INTEGER, 32]

Function i8 llvmtype llvmtype.[ toint.INTEGER, 8]

Function i1 llvmtype llvmtype.[ toint.INTEGER, 1]

Function VOID llvmtype llvmtype.[ toint.TVOID]

Function array(size:int, base:llvmtype)llvmtype llvmtype.[  toint.ARRAY, size, typ.base]

Function ptr(base:llvmtype)llvmtype llvmtype.[  toint.POINTER, typ.base, 0]

Function function(para:seq.llvmtype)llvmtype llvmtype.@(+, typ, [  toint.FUNCTION, 0], para)

Function adjust(s:seq.seq.int, adj:seq.int, i:int)seq.seq.int
 // go back and adjust types to fillin the length of arrays that were not known at time of creation of type //
 if i > length.adj then subseq(s, i, length.s)
 else
  let r = s_i
   [ if length.r < 2 then r
   else [ r_1, r_2 + adj_i] + subseq(r, 3, length.r)]
   + adjust(s, adj, i + 1)


-------------------------

Function type:llvmconst internaltype export

type llvmconst is record typ:int, toseq:seq.int

use seq.encodingpair.llvmconst


function hash(a:llvmconst)int hash.symtabname.a

Function assignencoding(l:int, a:llvmconst) int l+1


Function =(a:llvmconst, b:llvmconst)boolean  symtabname.a =  symtabname.b ∧ typ.a = typ.b


Function symtabname(a:llvmconst)seq.int  
  if typ.a in [-1,-2] then 
    subseq(toseq.a,2 , 1+ (toseq.a)_1)
  else toseq.a

Function modulerecord(a:llvmconst) seq.int  
if typ.a in [-1,-2] then 
    subseq(toseq.a,  2+ (toseq.a)_1,length.toseq.a)
  else toseq.a

Function typ(a:llvmconst) int export

Function toseq(a:llvmconst) seq.int export
 


Function modulerecord(name:seq.word,rec:seq.int) int
let c=if name="" then
   llvmconst(-3, rec )  
else 
let chars=tointseq.@(+,decodeword,empty:seq.char,name)
  llvmconst(-1,  [length.chars]+ chars+rec)
valueofencoding.encode.c-1


use seq.encodingpair.llvmtypeele

Function C64(i:int)int valueofencoding.encode( llvmconst(typ.i64, [ CONSTINTEGER, i])) - 1

Function C32(i:int)int valueofencoding.encode( llvmconst(typ.i32, [ CONSTINTEGER, i])) - 1

Function C(t:llvmtype, s:seq.int)int valueofencoding.encode( llvmconst(typ.t, s)) - 1

Function Cprt(t:int, s:seq.int)int // used in print bitcodes tool // valueofencoding.encode( llvmconst(t, s)) - 1

Function constvalue(i:int) int    (toseq.decode(  to:encoding.llvmconst(i+1)))_2

Function ismoduleblock(l:llvmconst) boolean  typ.l < 0 


Function constantrecords seq.encodingpair.llvmconst   encoding:seq.encodingpair.llvmconst
 
Function typ(a:encodingpair.llvmconst)  int typ.data.a
 
Function record(a:encodingpair.llvmconst) seq.int modulerecord.data.a
   
   
Function symtablename(b:encodingpair.llvmconst) seq.char 
  let a=data.b 
  if typ.a in [-1,-2] then 
    tocharseq.subseq(toseq.a,2 , 1+ (toseq.a)_1)
  else empty:seq.char

Function consttype(i:int) llvmtype
       let l= decode.to:encoding.llvmconst(i+1)
       if typ.l < 0 then  llvmtype(1+(modulerecord.l)_2 )  else 
        llvmtype(typ.l+1)

