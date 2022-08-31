Module tools

* STATE builtin:profile profileinfo profileresult

* only document printbitcodes profile prettylib doc

* usegraph exclude standard seq set otherseq UTF8 real graph

use doc

use file

use seq.file

use frontcmd

use genLR1

use main2

use profile

use standard

use taulextable

use textio

Function lextable(input:seq.file, o:seq.word)seq.file[file(o, getlextable)]

Function LR1(input:seq.file, o:seq.word, codeonly:boolean, parameterized:boolean)seq.file
[file(o, LR1gen(breakparagraph.data.first.input, codeonly, parameterized))]

Function front(input:seq.file, o:seq.word, pass:seq.word, n:seq.word, ~n:seq.word
, mods:seq.word, ~mods:seq.word, within:boolean, rn:seq.word, out:seq.word
)seq.file
let output = 
 front2(compilerFront(if isempty.pass then"pass2"else pass, input)
 , n
 , ~n
 , mods
 , ~mods
 , within
 , rn
 , out
 )
[file(o, output)]

Function testprofile(input:seq.file, o:seq.word)seq.file
let discard = makebitcode.input
[file(o, profileresults."time")]

Function testprofile2(input:seq.file, o:seq.word)seq.file
let discard = doclibrary(input, o)
[file(o, profileresults."time")] 