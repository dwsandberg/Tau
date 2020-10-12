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


type llvmconst is record typ:int, toseq:seq.int

use seq.encodingpair.llvmconst


function hash(a:llvmconst)int hash.symtabname.a

Function assignencoding(l:int, a:llvmconst) int l+1


Function =(a:llvmconst, b:llvmconst)boolean  symtabname.a =  symtabname.b ∧ typ.a = typ.b


function symtabname(a:llvmconst)seq.int  
  if typ.a in [-1,-2] then 
    subseq(toseq.a,2 , 1+ (toseq.a)_1)
  else toseq.a


 

Function modulerecord(name:seq.word,rec:seq.int) slot
let c=if name="" then llvmconst(-3, rec )  
else 
let chars=tointseq.@(+,decodeword,empty:seq.char,name)
  llvmconst(-1,  [length.chars]+ chars+rec)
slot(valueofencoding.encode.c-1)


use seq.encodingpair.llvmtypeele

Function C64(i:int)slot slot(valueofencoding.encode( llvmconst(typ.i64, [ toint.CINTEGER, i])) - 1)

Function C32(i:int)slot slot(valueofencoding.encode( llvmconst(typ.i32, [ toint.CINTEGER, i])) - 1)

function C(t:llvmtype, s:seq.int)int valueofencoding.encode( llvmconst(typ.t, s)) - 1

Function constantrecord(t:llvmtype, s:seq.int) slot slot(valueofencoding.encode( llvmconst(typ.t, s)) - 1)

Function DATA(t:llvmtype,data:seq.int) slot
slot(valueofencoding.encode( llvmconst(typ.t, [toint.CDATA]+data)) - 1)

Function AGGREGATE( data:seq.slot) slot
let t=array(length.data,i64)
slot(valueofencoding.encode.llvmconst(typ.t, [toint.CAGGREGATE]+@(+,toint,empty:seq.int,data))
   - 1)


Function ptrtoint(argtype:llvmtype,p:slot) slot
slot.C(i64,[ toint.CCAST, 9, typ.argtype, toint.p])

Function CGEP( p:slot,b:int ) slot
let t1 = // if p=0 then  array(-2, i64) else // consttype.p
  slot.C(ptr.i64, [ toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.i32, toint.C32.0,typ.i64, toint.C64.b] )

Function CGEPi8( p:slot,b:int ) slot
let t1 = // if p=0 then  array(-2, i64) else // consttype.p
  slot.C(ptr.i8, [ toint.CGEP, typ.t1, typ.ptr.t1, toint.p, typ.i32, toint.C32.0,typ.i64, toint.C64.b] )

/Function zeroinit(profiletype:llvmtype) int C(profiletype, [ toint,CNULL])

Function Creal(i:int) slot
slot.C(double,[toint.CCAST, 11,typ.i64,toint.C64.i])

use seq.slot


Function constvalue(i:slot) int    (toseq.decode(  to:encoding.llvmconst(toint.i+1)))_2

use seq.slotrecord

Function constantrecords seq.slotrecord 
@(+,slotrecord,empty:seq.slotrecord, encoding:seq.encodingpair.llvmconst)

type  slotrecord is record cvt:encodingpair.llvmconst 

Function type:slotrecord internaltype export

Function record(b:slotrecord) seq.int 
  let a=data.cvt.b
 if typ.a = -1 then // name comes before record //
    subseq(toseq.a,  2+ (toseq.a)_1,length.toseq.a)
  else toseq.a


Function symtablename(c:slotrecord) seq.char 
let b=cvt.c
  let a=data.b 
  if typ.a in [-1,-2] then 
    tocharseq.subseq(toseq.a,2 , 1+ (toseq.a)_1)
  else empty:seq.char

Function ismoduleblock(a:slotrecord) boolean  typ.data.cvt.a < 0 

Function typ(s:slotrecord) int  typ.data.cvt.s 

 
Function consttype(s:slot) llvmtype
       let l= decode.to:encoding.llvmconst(toint.s+1)
       llvmtype(1+if typ.l = -1 then  // must skip name to find record // 
            (toseq.l)_(3+ (toseq.l)_1)
        else if typ.l = -3 then (toseq.l)_2
        else  typ.l )
        
 

type slot is record toint:int 

function toint(slot) int export

function slot(int)  slot export

function type:slot internaltype export

Function r(a:int) slot   slot.-a