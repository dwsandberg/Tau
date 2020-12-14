
Library small   UTF8 bitpackedseq bits  encoding fileio format  
  ipair  maindict mangle mytype  otherseq  
 process real seq set stack stacktrace  textio  tree  words xxhash standard
uses
exports UTF8 assignencodingnumber bitpackedseq bits dataio dict encoding fileio format 
graph groupparagraphs intdict internalbc ioseq  libdesc llvm llvmconstants 
main2 maindict mangle mytype pretty otherseq  prims process 
real seq set stack stacktrace  standard symbol textio timestamp tree worddict words xxhash 
codegennew codetemplates persistant  sparseseq parse main2
  
option.fileio getfile(seq.bits)fileresult STATE

option.fileio createlib(name:seq.bits, libs:seq.bits, t:outputformat)int STATE

option.fileio createfile(name:seq.bits, data:outputformat)int STATE
 
option.UTF8 toword(int)word NOINLINE 

Module  main2

use standard

use fileio

use format

use UTF8

* usegraph exclude standard seq 

Function main(arg:seq.int)outputformat
   outputformat.toseqint.toUTF8(htmlheader + "processpara.output")
 

asdfsa
asfdasf


