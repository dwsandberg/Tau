Module testall

use bug7

use checking

use real

use standard

use test11

use test11a

use testencoding

/use testfileio

use testmodules

use testopt

use testprocess

use testseq

use wordfreq

use file

use fileIO

use seq.file


Function testall(input:seq.file,o:seq.word) seq.file 
let out=test11
+ testencoding 
+ testmodules
+ testbug7
{+ testreal
+ testseq
+ test11a 
+ testwordfreq
+ testopt(first.input)  
+ {testfileio
+} testprocess}
[file(filename.o,out)]

  