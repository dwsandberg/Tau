

Library 
stdlib UTF8   bits codegennew codetemplates encoding fileio format   groupparagraphs intdict 
internalbc interpreter  libdesc llvm llvmconstants main2  mangle mytype pretty otherseq parse parsersupport 
pass1 pass2  persistant postbind   process real seq set stack  symbol textio timestamp tree worddict words xxhash
 sparseseq standard maindict  outstream bitstream tausupport
 mergeblocks program   
   tests/test11 tests/checking tests/point tests/testencoding  
 tests/randomphrase tests/myseq tests/test20 tests/bug7 tests/testmodules
 tests/testprocess tests/testfileio tests/testseq
 tests/wordfreq
 testsCompile/testall
 testsCompile/testopt
 testsCompile/test11a
 graphs/svg
 graphs/svggraph
 graphs/makeDAG
 graphs/layergraph
 graphs/labeledgraph
 graphs/display
 graphs/displaygraph
 graphs/displaytextgraph
 graphs/barycenter
 graphs/bandeskopf
 graphs/ipair
 graphs/graph
 typerep
uses
exports UTF8 assignencodingnumber bitpackedseq bits dataio dict encoding fileio format abstractBuiltin
graph groupparagraphs intdict   ioseq ipair libdesc  
main2 maindict mangle mytype pretty otherseq    process 
real seq set stack   symbol textio timestamp tree worddict words xxhash 
  sparseseq   standard testall
svg svggraph displaygraph displaytextgraph display index
barycenter bandeskopf makeDAG layergraph labeledgraph tausupport 
  interpreter  llvm llvmconstants codegennew   persistant breakblocks
  program hidesymbol pass2 parse  symboldict taublockseq typerep firstpass

* Removed maindict 


Module PROFILE

use main2

use pass2

use codegennew

use standard

use  program

use symbol

use set.symbol

use seq.symbol

use bits

use seq.bits



Export  subcompilelib( seq.word)seq.word  


Export pass2(placehold:program)program  


Export codegen(theprg:program,  uses:set.symbol, thename:word, libdesc:seq.symbol, alltypes:type2dict,isbase:boolean)seq.bits  




module STATE

use standard

use fileio

use timestamp

use bits

use seq.bits


Export currenttime timestamp 

Export getfile(name:cstr)fileresult  

Export getbytefile(cstr) fileresultbyte  

Export getbitfile(cstr)  fileresultbit  

Export createfile(byteLength:int,data:seq.bits,cstr) int  

Export  createfile3(byteLength:int,data:seq.bits,name:cstr) int   




module INLINE
 
use symbol

Export Lit(int)symbol



module ININLINE

use standard

use UTF8

use symbol

Export toword(int)word  

Export decodeword(word) seq.char

Export Start(mytype) symbol

Export replaceT(mytype,mytype) mytype
  

module COMPILETIME

use standard

use bits

use UTF8

use tausupport

use real

Export -(int ) int 

Export +(int,int) int 

Export -(int,int) int 

Export /(int,int) int 

Export *(int,int) int 

Export =(int,int) boolean 

Export =(boolean,boolean) boolean 

Export >(int,int) boolean 

Export =(int,int) boolean 

Export  ∧(a:bits, bits)bits 

Export ∨(a:bits, bits)bits 

Export  >>(a:bits, i:int)bits 

Export  <<(a:bits, i:int)bits 

Export   -(real,real) real 

Export +(seq.word,seq.word) seq.word 

Export  merge(seq.word )  word 

Export makereal(seq.word) real 

Export  getseqlength(ptr) int 

Export toword(int) word 


Export encodeword( seq.char) word 


Export  decodeword( word) seq.char  


Export_(seq.word,int) word 

Export_(seq.int,int) int  

Export_(seq.char,int) char 









