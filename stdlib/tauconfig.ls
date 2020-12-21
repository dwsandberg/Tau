
Library tauconfig stdlib UTF8 bitpackedseq bits codegennew codetemplates encoding fileio format  groupparagraphs intdict 
internalbc interpreter  libdesc llvm llvmconstants main2  mangle mytype pretty otherseq parse parsersupport 
pass1 pass2new persistant postbind prims process real seq set stack   symbol textio timestamp tree worddict words xxhash
 sparseseq standard maindict tausupportNostacktrace breakblocks
uses
exports UTF8 assignencodingnumber bitpackedseq bits dataio dict encoding fileio format 
 groupparagraphs intdict   ioseq libdesc  
main2   mangle mytype pretty otherseq  prims process 
real seq set stack   symbol textio timestamp tree worddict words xxhash 
     standard 

* Removed maindict 

option.main2 subcompilelib(seq.word, seq.word)seq.word PROFILE

option.main2 compilelib2(seq.word)seq.word PROFILE

 
/option.builtin option(T, x:seq.word)T STATE
 
option.fileio getfile(seq.bits)fileresult STATE

option.fileio createlib(name:seq.bits, libs:seq.bits, t:outputformat)int STATE

option.fileio createfile(name:seq.bits, data:outputformat)int STATE

option.timestamp   currenttime timestamp STATE

option.symbol Lit(int)symbol INLINE
 
option.UTF8 toword(int)word NOINLINE  

 
