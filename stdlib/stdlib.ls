

Library 
stdlib UTF8   bits codegennew codetemplates encoding fileio format   groupparagraphs intdict 
internalbc interpreter  libdesc llvm llvmconstants main2  mangle mytype pretty otherseq parse parsersupport 
pass1 pass2  persistant postbind   process real seq set stack  symbol textio timestamp tree worddict words xxhash
 sparseseq standard maindict  outstream bitstream tausupport
 basetypecheck
 mergeblocks
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
graph groupparagraphs intdict   ioseq ipair libdesc  
main2 maindict mangle mytype pretty otherseq    process 
real seq set stack   symbol textio timestamp tree worddict words xxhash 
  sparseseq   standard testall
svg svggraph displaygraph displaytextgraph display index
barycenter bandeskopf makeDAG layergraph labeledgraph tausupport
  interpreter  llvm llvmconstants internalbc codegennew codetemplates persistant breakblocks

* Removed maindict 

option.main2 subcompilelib(seq.word, seq.word)seq.word PROFILE

option.main2 compilelib2(seq.word)seq.word PROFILE

option.pass1 pass1( seq.seq.seq.word,  seq.word, seq.firstpass) linkage PROFILE

option.pass2 pass2(placehold:program, alltypes:typedict)program PROFILE


\option.pass2 xxx(alltypes:typedict,p:program,code:seq.symbol,s:symbol,
 pdict:worddict.seq.symbol,first:boolean
) expandresult PROFILE

\option.pass2 firstopt(p:program, rep:symbol, code:seq.symbol, alltypes:typedict)program PROFILE

option.pass2 subpass2(  alltypes:typedict,  bigin:seq.programele,corein:program,toprocess:program,count:int) program
 PROFILE

option.codegennew codegen(theprg:program, definesWithBuiltins:seq.symbol, uses:set.symbol, thename:word, libdesc:symbol, alltypes:typedict,isbase:boolean)seq.bits PROFILE

/option.pass1 maptemp(s: seq.mapele, templates:program) program PROFILE

option.symbol lookupcode(p:program, s:symbol)programele PROFILE

/option.set.symbol findelement(val:symbol, s:set.symbol)set.symbol PROFILE

\option.pass2 depthfirst(knownsymbols:program, alltypes:typedict, 
pending:seq.symbol, processed:program, code:seq.symbol, s:symbol)program
PROFILE

option.standard -(int ) int COMPILETIME

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

option.tausupport getseqlength(ptr) int COMPILETIME

\option.tausupport getseqtype(ptr) int COMPILETIME



option.fileio getfile(name:cstr)fileresult STATE

option.fileio getbytefile(cstr) fileresultbyte STATE

option.fileio getbitfile(cstr)  fileresultbit STATE

option.fileio createfile(byteLength:int,data:seq.bits,cstr) int STATE

option.fileio  createfile3(byteLength:int,data:seq.bits,name:cstr) int  STATE



 
option.UTF8 toword(int) word COMPILETIME


option.words encodeword( seq.char) word COMPILETIME


option.words  decodeword( word) seq.char NOINLINE

option.words  decodeword( word) seq.char COMPILETIME


option.seq.word _(seq.word,int) word COMPILETIME

option.seq.int _(seq.int,int) int COMPILETIME

option.seq.char _(seq.char,int) char COMPILETIME


  

option.timestamp   currenttime timestamp STATE

option.symbol Lit(int)symbol INLINE

option.symbol symbol(seq.word,seq.word,seq.word,bits) symbol NOINLINE

option.symbol start(mytype) symbol NOINLINE

option.mytype replaceT(mytype,mytype) mytype NOINLINE

 
option.UTF8 toword(int)word NOINLINE  


