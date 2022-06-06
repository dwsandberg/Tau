Module testall

use bug7

use checking

use real

use standard

use test11

use test11a

use testencoding

use testmodules

use testopt

use testprocess

use testseq

use wordfreq

use file

use seq.file


Function testall(input:seq.file,o:seq.word) seq.file 
let out=test11
+ testencoding 
+ testmodules
+ testbug7
+ randomtest(500)
+ testreal
+ testseq
+ test11a(input) 
+ testwordfreq
+ testprocess
+ if isempty.input then "no opt test file specified" else testopt(input)   
[file(filename.o,out)]

  