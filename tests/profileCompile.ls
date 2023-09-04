Module profileCompile

use file

use seq.file

use main2

use profile

use standard

Function profileCompile(
 input:seq.file
 , library:seq.word
 , exports:seq.word
 , uses:seq.word
 , o:seq.word
) seq.word
{ENTRYPOINT}
let discard = makebitcode(input, library, exports, uses, false, false, "", ""),
profileresults."time" 