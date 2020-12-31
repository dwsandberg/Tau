
Library small   UTF8  bitstream bits  encoding tausupportNostacktrace    fileio format  
     otherseq  outstream
 process real seq set stack  textio  tree  words xxhash standard
 tests/test11 tests/checking tests/point tests/testencoding  
 tests/randomphrase tests/myseq tests/test20 tests/bug7 tests/testmodules
 tests/testprocess tests/test5 tests/testseq tests/wordfreq
 graphs/ipair
 graphs/graph
 sparseseq 
uses
exports UTF8 main2 words tausupport    testmodules   
 
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
  
/option.fileio getfile(seq.bits)fileresult STATE

/option.fileio createlib(name:seq.bits, libs:seq.bits, t:outputformat)int STATE

/option.fileio createfile(name:seq.bits, data:outputformat)int STATE
 
option.UTF8 toword(int)word NOINLINE 

Module  main2

use standard

use fileio

use format

use UTF8

use bits

use seq.byte

use test11

use testencoding

 use bug7

use testmodules

use testprocess

 use test5

use testseq 

use wordfreq

 use real

use encoding.seq.char

* usegraph exclude standard seq  test11 test5 testmodules testprocess testseq wordfreq testencoding

 
Function main(arg:seq.byte) int
   let output=test11+test5+testencoding+testprocess + testmodules+ testbug7
   +testreal+testseq+testwordfreq
    createhtmlfile("stdout",   output  )
 
 Function addlibrarywords(l:liblib) int let discard=addencodingpairs(words.l) 1

type liblib is record libname:seq.word, words:seq.encodingpair.seq.char




