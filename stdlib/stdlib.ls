

Library 
stdlib UTF8   bits codegennew codetemplates encoding fileio format     
internalbc interpreter  libdesc llvm llvmconstants main2  mangle mytype pretty otherseq parse parsersupport 
pass2  persistant postbind   process real seq set stack  symbol textio timestamp tree   words xxhash
 sparseseq standard maindict  outstream bitstream tausupport symbol2
 mergeblocks compilerfront symref symboldict  libraryModule
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
 typedict passsymbol passparse   
uses
exports UTF8   bits dataio  encoding fileio format 
graph    hashset   ioseq ipair   
main2 maindict mangle  pretty otherseq    process 
real seq set stack    textio timestamp tree  words xxhash 
  sparseseq   standard testall
svg svggraph displaygraph displaytextgraph display index
barycenter bandeskopf makeDAG layergraph labeledgraph tausupport 
    llvm llvmconstants  internalbc    
      taublockseq  libraryModule symbol2

* Removed maindict 

* only document standard seq real

Module PROFILE

use main2

use pass2

use codegennew

use standard

use  compilerfront

use symbol

use set.symbol

use seq.symbol

use bits

use seq.bits

use libdesc

use passparse

use passsymbol

use set.passsymbols

use codetemplates

Export  subcompilelib( seq.word)seq.word  


Export pass2(placehold:set.symdef)set.symdef  


Export codegen(theprg:set.symdef,  uses:set.symbol, thename:word, libdesc:libdescresult,
 alltypes:typedict,isbase:boolean)seq.bits  

Export compilerfront(option:seq.word,libname:seq.word
,allsrc:seq.seq.word,dependentlibs:seq.word,exports:seq.word) compileinfo

Export  passparse(   abstractmods :set.passsymbols,simplemods:set.passsymbols
,lib:word, prg1:seq.symdef
,src:seq.seq.word,mode:word) 
set.symdef

Export stepone(theprg:set.symdef,  roots:set.symbol,alltypes:typedict, isbase:boolean,
  thename:word,newmap:set.symbolref) steponeresult 

/Export uses(p:program, alltypes:typedict,processed:set.symbol, toprocess:set.symbol
,infref:set.symbol,inrecordconstant:set.symbol,inother:set.symbol 
)usesresult


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

Export createfile2(byteLength:int,data:seq.bits,cstr) int  

Export  createfile3(byteLength:int,data:seq.bits,name:cstr) int   




module INLINE
 
use symbol

Export Lit(int)symbol



module NOINLINE

use standard

use UTF8

use symbol


Export toword(int)word  

Export decodeword(word) seq.char

Export encodeword(seq.char) word
  

module COMPILETIME

use typedict

use standard

use bits

use UTF8

use tausupport

use real

use seq.word

Export -(int ) int 

Export +(int,int) int 

Export -(int,int) int 

Export /(int,int) int 

Export *(int,int) int 

Export =(int,int) boolean 

Export =(word,word) boolean

Export =(boolean,boolean) boolean 

Export >(int,int) boolean 

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

Export char1(seq.word) char

Export_(seq.word,index) word 

Export_(seq.word,int) word 

Export_(seq.int,int) int  

Export_(seq.char,int) char 









