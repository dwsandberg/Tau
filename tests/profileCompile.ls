Module profileCompile

Function profileCompile(
 input:seq.file
 , library:seq.word
 , exports:seq.word
 , uses:seq.word
 , o:seq.word
) seq.word
{ENTRYPOINT}
let discard = makebitcode(input, library, exports, uses, false, false, ""),
profileresults."time"

use main2

use file

use seq.file

use profile

use standard 