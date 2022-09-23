Module profileexample

use doc

use file

use main2

use profile

use standard

Function testprofile(input:seq.file, o:seq.word)seq.file
let discard = makebitcode.input
[file(o, profileresults."time")]

Function testprofile2(input:seq.file, o:seq.word)seq.file
let discard = doclibrary(input, o, "")
[file(o, profileresults."time")] 