
Library stdlib UTF8 bitpackedseq bits codegennew codetemplates encoding fileio format graph groupparagraphs intdict 
internalbc interpreter ipair libdesc llvm llvmconstants main2 maindict mangle mytype pretty otherseq parse parsersupport 
pass1 pass2new persistant postbind prims process real seq set stack stacktrace symbol textio timestamp tree worddict words xxhash
 sparseseq standard
uses
exports UTF8 assignencodingnumber bitpackedseq bits dataio dict encoding fileio format 
graph groupparagraphs intdict internalbc ioseq ipair libdesc llvm llvmconstants 
main2 maindict mangle mytype pretty otherseq  prims process 
real seq set stack stacktrace  symbol textio timestamp tree worddict words xxhash 
codegennew codetemplates persistant  sparseseq parse standard

parse parsersupport


option.main2 subcompilelib(seq.word, seq.word)seq.word PROFILE

option.main2 compilelib2(seq.word)seq.word PROFILE

 
/option.builtin option(T, x:seq.word)T STATE
 
option.fileio getfile(seq.bits)fileresult STATE

option.fileio createlib(name:seq.bits, libs:seq.bits, t:outputformat)int STATE

option.fileio createfile(name:seq.bits, data:outputformat)int STATE

option.timestamp   currenttime timestamp STATE

 



option.symbol Lit(int)symbol INLINE



 


 

 
 
option.UTF8 toword(int)word NOINLINE  

