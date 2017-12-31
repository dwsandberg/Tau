Module prims



use stdlib

Function execute(name:word)seq.word executecode(toCformat2.[ name], empty:seq.int)

type argblock3 is record a:int, length:int, arg1:seq.word, arg2:word, arg3:word

type argblock4 is record a:int, length:int, state:seq.word, arg:seq.word, arg2:seq.word, b:seq.seq.word

function cvt(a:argblock3)seq.int builtin

function cvt(a:argblock4)seq.int builtin


Function execute(name:word, arg1:seq.word, arg2:word, arg3:word)seq.word 
 executecode(toCformat2.[ name], cvt.argblock3(0, 3, arg1, arg2, arg3))

Function execute(name:word, state:seq.word, arg:seq.word, arg2:seq.word, b:seq.seq.word)seq.word 
 executecode(toCformat2.[ name], cvt.argblock4(0, 4, state, arg, arg2, b))

function addsuffix(suffix:seq.word, a:word)seq.word [ a]+ suffix

Function createlib(b:seq.int, libname:word, dependlibs:seq.word)int 
 let z2 = createbytefile([ libname]+".bc", b)
  createlib3(toCformat2.[ libname], toCformat2.@(+, addsuffix.".dylib","", dependlibs))
  
Function createlib(b:seq.bits, libname:word, dependlibs:seq.word)int 
 let z2 = createfile(toCformat2([ libname]+".bc"), blockit.b)
  createlib3(toCformat2.[ libname], toCformat2.@(+, addsuffix.".dylib","", dependlibs))
  

function createlib3(name:seq.bits, libs:seq.bits)int builtin.createlib3ZbuiltinZUTF8ZUTF8

Function unloadlib(a:seq.word)int unloadlib.toCformat2.a

function unloadlib(seq.bits)int builtin.unloadlibZbuiltinZUTF8

Function loadlib(a:seq.word, timestamp:int)int loadlib.toCformat2.a

function loadlib(seq.bits)int builtin.loadlibZbuiltinZUTF8

function executecode(seq.bits, para:seq.int)seq.word builtin.executecodeZbuiltinZUTF8Zintzseq


Function getfile(f:seq.word)seq.int export


Function fileexists(f:seq.word)boolean export

 
   
Function createbytefile(a:seq.word, data:seq.int)int export


use fileio

use blockseq.bits


Module fileio

use stdlib

use bitstream

Function toCformat2(s:seq.word) seq.bits 
   packed.data2.add(@(add,byte,bitpackedseq(0,empty:seq.byte,bits(0)),toseqint.toUTF8.s),byte(0))

Function createbytefile(name:seq.word,a:seq.int) int
   createfile(toCformat2.name, blockit.data2.@(add,byte, empty:bitpackedseq.byte ,a))

Function createfile(name:seq.bits, data:seq.bits)int builtin.createfileZbuiltinZintzseqZintzseq

function getfile(f:seq.bits) fileresult2 builtin.getfileZbuiltinZUTF8.STATE

type fileresult2 is record size:int, word1:int, word2:int, data:seq.int

Function getfile(name:seq.word)seq.int 
 // as file byte // 
  let file = getfile.toCformat2.name
  assert size.file > -1 report"Error opening file"+ name
    tointseq.toseq.bitpackedseq(size.file,tobitpackedseq([word1.file,word2.file]+data.file),bits(0))

Function fileexists(f:seq.word)boolean 
 let file = getfile.toCformat2.f
  size.file > -1


use packedseq.bits


use UTF8


use blockseq.bits

use seq.byte

use byteseq.byte

type byte is record toint:int

function tobitpackedseq(s:seq.int) seq.byte @(+,byte,empty:seq.byte,s)

function tointseq(s:seq.byte) seq.int @(+,toint,empty:seq.int,s)

function sizeinbits(a:byte)  int   8

function tobits(a:byte ) bits bits.toint.a

function frombits(a:bits) byte byte.toint.a

use blockseq.int


Function blockit(seq.int)seq.int export

Blockit is exported so other deepcopy functions will compile



Module  byteseq.T

use stdlib

use bitstream

use seq.T

use seq.bits

type bitpackedseq is sequence length:int, data:seq.T,part:bits

function  frombits(a:bits) T unbound

function   tobits(T) bits unbound

function   sizeinbits(T)  int unbound

Function bitpackedseq(int,seq.T,bits) bitpackedseq.T export

Function toseq(a:bitpackedseq.T) seq.T  export

Function length(bitpackedseq.T) int export


Function empty bitpackedseq.T  bitpackedseq(0,empty:seq.T,bits(0))

Function bitpackedseq2(len:int,d:seq.T,part:bits)seq.T toseq.bitpackedseq(len, d,part)

Function  data2(a:bitpackedseq.T) seq.bits
    @(+,tobits,empty:seq.bits,data.align.a)
 

Function _(a:bitpackedseq.T, idx:int) T 
  let nobits=sizeinbits.frombits.bits(0)
  let slotsperword = 64 / nobits 
  let  dataidx = (idx - 1) / slotsperword +1
  let d =  if dataidx > length.data.a then part.a else  tobits((data.a)_ dataidx )         
    let slot = ( idx-1) mod  slotsperword    * nobits
       frombits( d >> slot &and bits(-1) >> 64-nobits )
       
Function add(a:bitpackedseq.T, b:T) bitpackedseq.T
     let nobits = sizeinbits.b   let slotsperword = 64 / nobits 
      let slot = ( length.a) mod  slotsperword  
      let newpart=  (tobits.b &and (bits(-1) >> 64-nobits) )  << slot * nobits &or part.a
      if slot = slotsperword -1 then
          bitpackedseq(length.a+1,data.a+frombits.newpart,bits.0)
          else bitpackedseq(length.a+1,data.a,newpart)
     
Function align(a:bitpackedseq.T) bitpackedseq.T
     let nobits = sizeinbits.frombits.bits(0)   let slotsperword = 64 / nobits 
      let slot = ( length.a) mod  slotsperword 
       if slot = 0 then a else
          align(add(a, frombits(bits(0))))

Function patch(a:bitpackedseq.T,j:int,val:int) bitpackedseq.T
   assert (j-1) mod 32 = 0 report "incorrect parameter to replace"
   let  i = j / 64 + 1
   let  b = if  i > length.data.a then part.a else tobits.(data.a)_i
   let x = if (j-1)mod 64 = 0 then 
       b &and bits(toint.(bits(1) << 32) - 1) << 32 &or bits(val)  
      else
       b &and bits(toint.(bits(1) << 32) - 1) &or bits(val) << 32
  // assert false report "PP"+toword.toint.x //
   if  i > length.data.a then 
      bitpackedseq(length.a,data.a,x)
   else 
    bitpackedseq(length.a,subseq(data.a,1,i-1)+ frombits.x+subseq(data.a,i+1,length.data.a),part.a)     
        
          
Function add(a:bitpackedseq.T, b:bits,count:int) bitpackedseq.T
     let nobits = sizeinbits.frombits.bits(0)   let slotsperword = 64 / nobits 
      let slot = ( length.a) mod  slotsperword  
      let   slotstoadd=    min ( slotsperword - slot , count )     
      let newpart=  (b &and (bits(-1) >> 64- slotstoadd * nobits) )  << slot * nobits &or part.a
      let d=if slot + slotstoadd = slotsperword  then
          bitpackedseq(length.a+slotstoadd,data.a+frombits.newpart,bits.0)
          else bitpackedseq(length.a+slotstoadd,data.a,newpart)
      if slotstoadd=count then d
      else add(d, b >> slotstoadd * nobits , count - slotstoadd)
          
