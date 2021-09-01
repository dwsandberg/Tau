
Library tauconfig 
stdlib UTF8   bits codegennew codetemplates encoding fileio format   
internalbc interpreter  libdesc llvm llvmconstants main2  mangle mytype pretty otherseq parse parsersupport 
pass1 pass2 breakblocks persistant postbind   process real seq set stack   symbol textio timestamp tree   words xxhash
 sparseseq standard maindict outstream bitstream tausupportNostacktrace 
uses
exports UTF8  bits dataio dict encoding fileio format 
    ioseq libdesc  localmap2
main2   mangle mytype pretty otherseq   process 
real seq set stack   symbol textio timestamp tree   words xxhash 
     standard 

* Removed maindict 

option.main2 subcompilelib(seq.word, seq.word)seq.word PROFILE

option.main2 compilelib2(seq.word)seq.word PROFILE

 
/option.fileio getfile(seq.bits)fileresult STATE

/option.fileio createlib(name:seq.bits, libs:seq.bits, t:outputformat)int STATE

/option.fileio createfile(name:seq.bits, data:outputformat)int STATE

option.timestamp   currenttime timestamp STATE

option.symbol Lit(int)symbol INLINE
 
option.UTF8 toword(int)word NOINLINE  

 
