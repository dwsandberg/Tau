#!/bin/sh tau stdlib tools doclibrary webcore .


 
Library webcore
inputoutput webIO /stdlib/tausupport /stdlib/graph 
/common/barycenter /common/layergraph 
/common/makeDAG /stdlib/bits  /stdlib/encoding /stdlib/format /stdlib/otherseq /stdlib/process 
/stdlib/real /stdlib/seq /stdlib/set /stdlib/sparseseq /stdlib/standard /stdlib/stack /stdlib/UTF8 /stdlib/textio 
/stdlib/words /stdlib/xxhash
/stdlib/bitstream
/common/bandeskopf 
/stdlib/IO2
/stdlib/bitcast
/stdlib/taublockseq
/stdlib/ptr
uses 
exports inputoutput tausupport graph  bandeskopf barycenter layergraph 
makeDAG bits bitstream encoding format otherseq process 
real seq set sparseseq standard stack UTF8 textio bitcast taublockseq
words xxhash webIO IO2

* usegraph include   bits bitstream encoding format otherseq process 
real seq set sparseseq standard stack UTF8 textio webIO 
words xxhash 
exclude standard seq

* only document   graph   
  bits bitstream encoding format otherseq process 
real seq set sparseseq standard stack UTF8 textio  
words xxhash IO2 webIO 



 
   
   