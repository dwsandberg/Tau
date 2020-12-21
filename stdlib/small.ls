
Library small   UTF8 bitpackedseq bits  encoding tausupportNostacktrace   fileio format  
     otherseq  
 process real seq set stack  textio  tree  words xxhash standard
 tests/randomphrase  
   tests/wordfreq
 sparseseq 
uses
exports UTF8 main2 words tausupport bitpackedseq       
 
 "Library small   UTF8 bitpackedseq bits  encoding tausupportNostacktrace   fileio format  
     otherseq  
 process real seq set stack  textio  tree  words xxhash standard
 tests/test11 tests/checking tests/point tests/testencoding  
 tests/randomphrase tests/myseq tests/test20 tests/bug7 tests/testmodules
 tests/testprocess tests/test5 tests/testseq tests/wordfreq
 graphs/ipair
 graphs/graph
 sparseseq 
uses
exports UTF8 main2 words tausupport bitpackedseq   "  
  
option.fileio getfile(seq.bits)fileresult STATE

option.fileio createlib(name:seq.bits, libs:seq.bits, t:outputformat)int STATE

option.fileio createfile(name:seq.bits, data:outputformat)int STATE
 
option.UTF8 toword(int)word NOINLINE 

Module  main2

use standard

use fileio

use format

use UTF8

/use test11

/use testencoding

/use bug7

/use testmodules

/use testprocess

/use test5

/use testseq 

use wordfreq

/use real

* usegraph exclude standard seq 

Function loaddictionary(file:fileresult)int 0

Function main(arg:seq.int)outputformat
   outputformat.toseqint.toUTF8(htmlheader +testwordfreq(300, 
    subseq(gettext."stdlib/pass2.ls" ,1, 90))
   )

/Function main(arg:seq.int)outputformat
   outputformat.toseqint.toUTF8(htmlheader + test11+ 
   test5+testencoding + testprocess + testmodules + testbug7
   +testreal+testseq+testwordfreq
   )




