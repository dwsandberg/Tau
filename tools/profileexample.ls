Module profileexample

use UTF8

use doc

use file

use seq.file

use format

use main2

use profile

use standard

/Function testprofile(input:seq.file, o:seq.word) seq.file
let discard = makebitcode(input, "", [name.fn.first.input],false),
[file(o, profileresults."time")]

Function testprofile2(input:seq.file, o:seq.word) seq.file {ENTRYPOINT}
let discard = doclibrary(input, o, ""),
[file(o, profileresults."time")]

Function testprofile3(input:seq.file, o:seq.word) seq.file {ENTRYPOINT}
let discard = testx.first.input,
[file(o, profileresults."time")]

Function testx(f:file) int
{OPTION PROFILE NOINLINE}
let a = HTMLformat.towords.UTF8.data.f,
0

for acc = emptyUTF8, x /in constantseq (0, 1) do HTMLformat.towords.UTF8.data.f /for (0) 