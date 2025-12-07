Module profileCompile

use file

use seq.file

use main2

use profile

use standard

use bits

use seq.byte

Function profileCompile(input:seq.file, exports:seq.word, output:seq.word) seq.word
{COMMAND} 
let discard = makebitcode(input, exports, false, false, "", "", output),
for acc="",f ∈ discard do
   acc+fullname.fn.f+%.n.data.f
   acc+"/br"+
profileresults."time" 