
Library 
stdlib UTF8   bits codegennew codetemplates encoding fileio format   groupparagraphs intdict 
internalbc interpreter  libdesc llvm llvmconstants main2  mangle mytype pretty otherseq parse parsersupport 
pass1 pass2 breakblocks persistant postbind   process real seq set stack  symbol textio timestamp tree worddict words xxhash
 sparseseq standard maindict  outstream bitstream tausupport
 basetypecheck
  tests/test11 tests/checking tests/point tests/testencoding  
 tests/randomphrase tests/myseq tests/test20 tests/bug7 tests/testmodules
 tests/testprocess tests/test5 tests/testseq
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
uses
exports UTF8 assignencodingnumber bitpackedseq bits dataio dict encoding fileio format abstractBuiltin
graph groupparagraphs intdict   ioseq ipair libdesc llvm llvmconstants 
main2 maindict mangle mytype pretty otherseq  prims process 
real seq set stack   symbol textio timestamp tree worddict words xxhash 
codegennew codetemplates persistant  sparseseq parse standard testall
svg svggraph displaygraph displaytextgraph display
barycenter bandeskopf makeDAG layergraph labeledgraph tausupport
pass1 postbind breakblocks   interpreter internalbc  

* Removed maindict 

option.main2 subcompilelib(seq.word, seq.word)seq.word PROFILE

option.main2 compilelib2(seq.word)seq.word PROFILE

option.pass1 pass1( seq.seq.seq.word,  seq.word, seq.firstpass) linkage PROFILE

option.pass1 maptemp(st:program, templates:program, s:mapele)program PROFILE

option.symbol lookupcode(p:program, s:symbol)programele PROFILE

option.set.symbol findelement(val:symbol, s:set.symbol)set.symbol PROFILE



option.standard +(int,int) int COMPILETIME

option.standard -(int,int) int COMPILETIME

option.standard /(int,int) int COMPILETIME

option.standard *(int,int) int COMPILETIME

option.standard =(int,int) boolean COMPILETIME

option.standard =(boolean,boolean) boolean COMPILETIME

option.standard >(int,int) boolean COMPILETIME

option.standard =(int,int) boolean COMPILETIME

option.bits  ∧(a:bits, bits)bits COMPILETIME

option.bits ∨(a:bits, bits)bits COMPILETIME

option.bits  >>(a:bits, i:int)bits COMPILETIME

option.bits  <<(a:bits, i:int)bits COMPILETIME

option.real -(real,real) real COMPILETIME

option.seq.word +(seq.word,seq.word) seq.word COMPILETIME

option.words merge(seq.word )  word COMPILETIME

option.UTF8 makereal(seq.word) real COMPILETIME

/option.abstractBuiltin.int IDX2(seq.int,int) int  COMPILETIME



option.fileio getfile(name:cstr)fileresult STATE

option.fileio getbytefile(cstr) fileresultbyte STATE

option.fileio getbitfile(cstr)  fileresultbit STATE

option.fileio createfile(byteLength:int,data:seq.bits,cstr) int STATE

option.fileio  createfile3(byteLength:int,data:seq.bits,name:cstr) int  STATE



/option.builtin.int Assert(seq.word) int STATE

/option.UTF8 toword(int) word COMPILETIME

/option.encoding.seq.char decode(encoding.seq.char) seq.char COMPILETIME

option.words encodeword( seq.char) word COMPILETIME

/option.words  decodeword( word) seq.char COMPILETIME

option.seq.word _(seq.word,int) word COMPILETIME

/option.seq.int IDX(seq.T, int) int   COMPILETIME
 

option.timestamp   currenttime timestamp STATE

option.symbol Lit(int)symbol INLINE
 
option.UTF8 toword(int)word NOINLINE  


