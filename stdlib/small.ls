
Library small   UTF8 bitpackedseq bits  encoding fileio format  
  ipair   mangle mytype  otherseq  
 process real seq set stack stacktrace  textio  tree  words xxhash standard
 tests/test11 tests/checking tests/point tests/testencoding  
 tests/randomphrase tests/myseq tests/test20 tests/bug7 tests/testmodules
 tests/testprocess tests/test5 tests/testseq
 tests/wordfreq
 graph sparseseq
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

use test11

use testencoding

use bug7

use testmodules

use testprocess

use test5

use testseq 

use wordfreq

use real

* usegraph exclude standard seq 

Function loaddictionary(file:fileresult)int 0

Function main(arg:seq.int)outputformat
   outputformat.toseqint.toUTF8(htmlheader + test11+ 
   test5+testencoding + testprocess + testmodules + testbug7
   +testreal+testseq+testwordfreq
   )
 




