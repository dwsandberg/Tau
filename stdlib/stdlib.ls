Library 
stdlib 
bits bitstream codegennew codetemplates compilerfront compilerfrontT encoding inputoutput format 
graph 
hashset internalbc compileTime libdesc libraryModule llvm llvmconstants localmap2
main2  mergeblocks mytype otherseq 
parse parsersupport pass2 pass2T passparse passsymbol persistant postbind pretty process 
real seq set sparseseq stack standard symbol symbol2 symboldict 
tausupport textio timestamp  typedict UTF8 words xxhash
codetemplates2
symbolconstant 
ptr
taublockseq
bitcast
IO2
uses
exports UTF8  barycenter bits   encoding fileio format graph hashset  internalbc ioseq   layergraph libraryModule llvm llvmconstants main2 maindict makeDAG mangle otherseq pretty process real seq set sparseseq stack standard svg svggraph 
symbol2 taublockseq tausupport testall textio timestamp  words xxhash compilerfront
bitcast IO2 

/* only document standard seq real

* usegraph include graph xxhash format encoding bits words real textio UTF8 set seq otherseq fileio standard bitstream 
exclude standard

* usegraph include  inputoutput process stack set taublockseq tau55 libraryModule tausupport typedict mytype symbol 
bitcast compileTime typedict
exclude 
standard seq bits otherseq 

* usegraph include codetemplates codetemplates2 codegennew internalbc llvmconstant llvm persistant exclude seq bits 
set otherseq standard UTF8 real stack

* usegraph include compilerfront compileTime libdesc main2 mergeblocks parse passparse passsymbol pass2 postbind pass2 
program typedict compilerfrontT pass2T
exclude seq set otherseq standard bits graph UTF8 stack real fileio textio encoding words symbol types

module COMPILETIME

use bits

use standard

use seq.word

Export+(seq.word, seq.word)seq.word

Export type:seq.word

Export type:word

Export type:bits

Export type:boolean

Export type:char

Export type:UTF8

Export_(seq.word, index)word

Export_(seq.word, int)word

Export_(seq.int, int)int

Export_(seq.char, int)char 