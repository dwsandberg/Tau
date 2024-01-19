Module profileCompile

use file

use seq.file

use main2

use profile

use standard

Function profileCompile(input:seq.file, exports:seq.word, output:seq.word) seq.word
{COMMAND}
let discard = makebitcode(input, exports, false, false, "", "", output),
profileresults."time" 